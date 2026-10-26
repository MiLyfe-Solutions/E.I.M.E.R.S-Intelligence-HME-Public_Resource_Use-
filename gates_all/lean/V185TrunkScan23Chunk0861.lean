import V185TrunkScan23Chunk0860

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5095218 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_5095218 : Nat := 118140960795 + 5095218 * 2 ^ 59
def prefixEnd_5095218 : Nat := 4983230072969 + 3 ^ 40 * 5095218 * 2
def baseEnd_5095218 : Nat := 290699541493372352204725

theorem tailTrace_5095218 : CollatzResearch.WordTrace tailWord_5095218 prefixEnd_5095218 290699541493372352204725 := by
  unfold tailWord_5095218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459466913725713699957577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123891911769935236533220205 46459466913725713699957577)
  ·
    refine ⟨34844600185294285274968183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46459466913725713699957577 34844600185294285274968183)
    ·
      refine ⟨52266900277941427912452275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34844600185294285274968183 52266900277941427912452275)
      ·
        refine ⟨78400350416912141868678413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52266900277941427912452275 78400350416912141868678413)
        ·
          refine ⟨29400131406342053200754405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78400350416912141868678413 29400131406342053200754405)
          ·
            refine ⟨5512524638689134975141451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29400131406342053200754405 5512524638689134975141451)
            ·
              refine ⟨8268786958033702462712177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512524638689134975141451 8268786958033702462712177)
              ·
                refine ⟨6201590218525276847034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8268786958033702462712177 6201590218525276847034133)
                ·
                  refine ⟨290699541493372352204725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6201590218525276847034133 290699541493372352204725)
                  ·
                    rfl

theorem cell23_5095218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_5095218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095218 prefixEnd_5095218 := by exact prefixLift 5095218
  have htrace : WordTrace (prefixWord ++ tailWord_5095218) baseStart_5095218 baseEnd_5095218 := by
    simpa [prefixWord, tailWord_5095218, baseEnd_5095218] using wordTrace_append hprefix tailTrace_5095218
  have hstable : (prefixWord ++ tailWord_5095218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095218).length < 2 ^ (prefixWord ++ tailWord_5095218).sum := by decide
  have hdescent : baseEnd_5095218 < baseStart_5095218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095222 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5095222 : Nat := 118140960795 + 5095222 * 2 ^ 59
def prefixEnd_5095222 : Nat := 4983230072969 + 3 ^ 40 * 5095222 * 2
def baseEnd_5095222 : Nat := 872099309120989718064169

theorem tailTrace_5095222 : CollatzResearch.WordTrace tailWord_5095222 prefixEnd_5095222 872099309120989718064169 := by
  unfold tailWord_5095222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614875846680522717685995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123892009031258908988650613 11614875846680522717685995)
  ·
    refine ⟨17422313770020784076528993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11614875846680522717685995 17422313770020784076528993)
    ·
      refine ⟨13066735327515588057396745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17422313770020784076528993 13066735327515588057396745)
      ·
        refine ⟨9800051495636691043047559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13066735327515588057396745 9800051495636691043047559)
        ·
          refine ⟨14700077243455036564571339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9800051495636691043047559 14700077243455036564571339)
          ·
            refine ⟨22050115865182554846857009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14700077243455036564571339 22050115865182554846857009)
            ·
              refine ⟨16537586898886916135142757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22050115865182554846857009 16537586898886916135142757)
              ·
                refine ⟨3100797543541296775339267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16537586898886916135142757 3100797543541296775339267)
                ·
                  refine ⟨4651196315311945163008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100797543541296775339267 4651196315311945163008901)
                  ·
                    refine ⟨872099309120989718064169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651196315311945163008901 872099309120989718064169)
                    ·
                      rfl

theorem cell23_5095222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5095222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095222 prefixEnd_5095222 := by exact prefixLift 5095222
  have htrace : WordTrace (prefixWord ++ tailWord_5095222) baseStart_5095222 baseEnd_5095222 := by
    simpa [prefixWord, tailWord_5095222, baseEnd_5095222] using wordTrace_append hprefix tailTrace_5095222
  have hstable : (prefixWord ++ tailWord_5095222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095222).length < 2 ^ (prefixWord ++ tailWord_5095222).sum := by decide
  have hdescent : baseEnd_5095222 < baseStart_5095222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095228 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_5095228 : Nat := 118140960795 + 5095228 * 2 ^ 59
def prefixEnd_5095228 : Nat := 4983230072969 + 3 ^ 40 * 5095228 * 2
def baseEnd_5095228 : Nat := 2616301008246896130717479

theorem tailTrace_5095228 : CollatzResearch.WordTrace tailWord_5095228 prefixEnd_5095228 2616301008246896130717479 := by
  unfold tailWord_5095228
  simp only [CollatzResearch.WordTrace]
  refine ⟨92919116192433313253847169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123892154923244417671796225 92919116192433313253847169)
  ·
    refine ⟨69689337144324984940385377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92919116192433313253847169 69689337144324984940385377)
    ·
      refine ⟨52267002858243738705289033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69689337144324984940385377 52267002858243738705289033)
      ·
        refine ⟨39200252143682804028966775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52267002858243738705289033 39200252143682804028966775)
        ·
          refine ⟨58800378215524206043450163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39200252143682804028966775 58800378215524206043450163)
          ·
            refine ⟨88200567323286309065175245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58800378215524206043450163 88200567323286309065175245)
            ·
              refine ⟨33075212746232365899440717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88200567323286309065175245 33075212746232365899440717)
              ·
                refine ⟨12403204779837137212290269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33075212746232365899440717 12403204779837137212290269)
                ·
                  refine ⟨4651201792438926454608851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12403204779837137212290269 4651201792438926454608851)
                  ·
                    refine ⟨6976802688658389681913277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4651201792438926454608851 6976802688658389681913277)
                    ·
                      refine ⟨2616301008246896130717479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6976802688658389681913277 2616301008246896130717479)
                      ·
                        rfl

theorem cell23_5095228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_5095228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095228 prefixEnd_5095228 := by exact prefixLift 5095228
  have htrace : WordTrace (prefixWord ++ tailWord_5095228) baseStart_5095228 baseEnd_5095228 := by
    simpa [prefixWord, tailWord_5095228, baseEnd_5095228] using wordTrace_append hprefix tailTrace_5095228
  have hstable : (prefixWord ++ tailWord_5095228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095228).length < 2 ^ (prefixWord ++ tailWord_5095228).sum := by decide
  have hdescent : baseEnd_5095228 < baseStart_5095228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095322 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5095322 : Nat := 118140960795 + 5095322 * 2 ^ 59
def prefixEnd_5095322 : Nat := 4983230072969 + 3 ^ 40 * 5095322 * 2
def baseEnd_5095322 : Nat := 2616349275428418762942047

theorem tailTrace_5095322 : CollatzResearch.WordTrace tailWord_5095322 prefixEnd_5095322 2616349275428418762942047 := by
  unfold tailWord_5095322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46460415211631520140404055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123894440564350720374410813 46460415211631520140404055)
  ·
    refine ⟨69690622817447280210606083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46460415211631520140404055 69690622817447280210606083)
    ·
      refine ⟨104535934226170920315909125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69690622817447280210606083 104535934226170920315909125)
      ·
        refine ⟨19600487667407047559232961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104535934226170920315909125 19600487667407047559232961)
        ·
          refine ⟨14700365750555285669424721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19600487667407047559232961 14700365750555285669424721)
          ·
            refine ⟨11025274312916464252068541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14700365750555285669424721 11025274312916464252068541)
            ·
              refine ⟨4134477867343674094525703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11025274312916464252068541 4134477867343674094525703)
              ·
                refine ⟨6201716801015511141788555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134477867343674094525703 6201716801015511141788555)
                ·
                  refine ⟨9302575201523266712682833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201716801015511141788555 9302575201523266712682833)
                  ·
                    refine ⟨6976931401142450034512125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9302575201523266712682833 6976931401142450034512125)
                    ·
                      refine ⟨2616349275428418762942047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6976931401142450034512125 2616349275428418762942047)
                      ·
                        rfl

theorem cell23_5095322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5095322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095322 prefixEnd_5095322 := by exact prefixLift 5095322
  have htrace : WordTrace (prefixWord ++ tailWord_5095322) baseStart_5095322 baseEnd_5095322 := by
    simpa [prefixWord, tailWord_5095322, baseEnd_5095322] using wordTrace_append hprefix tailTrace_5095322
  have hstable : (prefixWord ++ tailWord_5095322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095322).length < 2 ^ (prefixWord ++ tailWord_5095322).sum := by decide
  have hdescent : baseEnd_5095322 < baseStart_5095322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095345 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5095345 : Nat := 118140960795 + 5095345 * 2 ^ 59
def prefixEnd_5095345 : Nat := 4983230072969 + 3 ^ 40 * 5095345 * 2
def baseEnd_5095345 : Nat := 2616361085483472172954441

theorem tailTrace_5095345 : CollatzResearch.WordTrace tailWord_5095345 prefixEnd_5095345 2616361085483472172954441 := by
  unfold tailWord_5095345
  simp only [CollatzResearch.WordTrace]
  refine ⟨185842499725442755489703489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123894999816961836993135659 185842499725442755489703489)
  ·
    refine ⟨139381874794082066617277617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185842499725442755489703489 139381874794082066617277617)
    ·
      refine ⟨104536406095561549962958213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139381874794082066617277617 104536406095561549962958213)
      ·
        refine ⟨19600576142917790618054665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104536406095561549962958213 19600576142917790618054665)
        ·
          refine ⟨14700432107188342963540999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19600576142917790618054665 14700432107188342963540999)
          ·
            refine ⟨22050648160782514445311499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14700432107188342963540999 22050648160782514445311499)
            ·
              refine ⟨33075972241173771667967249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22050648160782514445311499 33075972241173771667967249)
              ·
                refine ⟨24806979180880328750975437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33075972241173771667967249 24806979180880328750975437)
                ·
                  refine ⟨9302617192830123281615789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24806979180880328750975437 9302617192830123281615789)
                  ·
                    refine ⟨3488481447311296230605921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9302617192830123281615789 3488481447311296230605921)
                    ·
                      refine ⟨2616361085483472172954441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488481447311296230605921 2616361085483472172954441)
                      ·
                        rfl

theorem cell23_5095345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5095345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095345 prefixEnd_5095345 := by exact prefixLift 5095345
  have htrace : WordTrace (prefixWord ++ tailWord_5095345) baseStart_5095345 baseEnd_5095345 := by
    simpa [prefixWord, tailWord_5095345, baseEnd_5095345] using wordTrace_append hprefix tailTrace_5095345
  have hstable : (prefixWord ++ tailWord_5095345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095345).length < 2 ^ (prefixWord ++ tailWord_5095345).sum := by decide
  have hdescent : baseEnd_5095345 < baseStart_5095345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095371 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_5095371 : Nat := 118140960795 + 5095371 * 2 ^ 59
def prefixEnd_5095371 : Nat := 4983230072969 + 3 ^ 40 * 5095371 * 2
def baseEnd_5095371 : Nat := 2616374435980489071229321

theorem tailTrace_5095371 : CollatzResearch.WordTrace tailWord_5095371 prefixEnd_5095371 2616374435980489071229321 := by
  unfold tailWord_5095371
  simp only [CollatzResearch.WordTrace]
  refine ⟨185843448023348561930149967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123895632015565707953433311 185843448023348561930149967)
  ·
    refine ⟨278765172035022842895224951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185843448023348561930149967 278765172035022842895224951)
    ·
      refine ⟨418147758052534264342837427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278765172035022842895224951 418147758052534264342837427)
      ·
        refine ⟨627221637078801396514256141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418147758052534264342837427 627221637078801396514256141)
        ·
          refine ⟨235208113904550523692846053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627221637078801396514256141 235208113904550523692846053)
          ·
            refine ⟨44101521357103223192408635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235208113904550523692846053 44101521357103223192408635)
            ·
              refine ⟨66152282035654834788612953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44101521357103223192408635 66152282035654834788612953)
              ·
                refine ⟨49614211526741126091459715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66152282035654834788612953 49614211526741126091459715)
                ·
                  refine ⟨74421317290111689137189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49614211526741126091459715 74421317290111689137189573)
                  ·
                    refine ⟨13953996991895941713223045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74421317290111689137189573 13953996991895941713223045)
                    ·
                      refine ⟨2616374435980489071229321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13953996991895941713223045 2616374435980489071229321)
                      ·
                        rfl

theorem cell23_5095371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_5095371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095371 prefixEnd_5095371 := by exact prefixLift 5095371
  have htrace : WordTrace (prefixWord ++ tailWord_5095371) baseStart_5095371 baseEnd_5095371 := by
    simpa [prefixWord, tailWord_5095371, baseEnd_5095371] using wordTrace_append hprefix tailTrace_5095371
  have hstable : (prefixWord ++ tailWord_5095371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095371).length < 2 ^ (prefixWord ++ tailWord_5095371).sum := by decide
  have hdescent : baseEnd_5095371 < baseStart_5095371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095375 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 4, 2, 2]
def baseStart_5095375 : Nat := 118140960795 + 5095375 * 2 ^ 59
def prefixEnd_5095375 : Nat := 4983230072969 + 3 ^ 40 * 5095375 * 2
def baseEnd_5095375 : Nat := 2616376489903107055579303

theorem tailTrace_5095375 : CollatzResearch.WordTrace tailWord_5095375 prefixEnd_5095375 2616376489903107055579303 := by
  unfold tailWord_5095375
  simp only [CollatzResearch.WordTrace]
  refine ⟨185843593915334070613295579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123895729276889380408863719 185843593915334070613295579)
  ·
    refine ⟨278765390873001105919943369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185843593915334070613295579 278765390873001105919943369)
    ·
      refine ⟨209074043154750829439957527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278765390873001105919943369 209074043154750829439957527)
      ·
        refine ⟨313611064732126244159936291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209074043154750829439957527 313611064732126244159936291)
        ·
          refine ⟨470416597098189366239904437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313611064732126244159936291 470416597098189366239904437)
          ·
            refine ⟨44101555977955253084991041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 470416597098189366239904437 44101555977955253084991041)
            ·
              refine ⟨33076166983466439813743281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44101555977955253084991041 33076166983466439813743281)
              ·
                refine ⟨24807125237599829860307461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33076166983466439813743281 24807125237599829860307461)
                ·
                  refine ⟨4651335982049968098807649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24807125237599829860307461 4651335982049968098807649)
                  ·
                    refine ⟨3488501986537476074105737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4651335982049968098807649 3488501986537476074105737)
                    ·
                      refine ⟨2616376489903107055579303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488501986537476074105737 2616376489903107055579303)
                      ·
                        rfl

theorem cell23_5095375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 2, 2].length) (baseStart_5095375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095375 prefixEnd_5095375 := by exact prefixLift 5095375
  have htrace : WordTrace (prefixWord ++ tailWord_5095375) baseStart_5095375 baseEnd_5095375 := by
    simpa [prefixWord, tailWord_5095375, baseEnd_5095375] using wordTrace_append hprefix tailTrace_5095375
  have hstable : (prefixWord ++ tailWord_5095375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095375).length < 2 ^ (prefixWord ++ tailWord_5095375).sum := by decide
  have hdescent : baseEnd_5095375 < baseStart_5095375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095408 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_5095408 : Nat := 118140960795 + 5095408 * 2 ^ 59
def prefixEnd_5095408 : Nat := 4983230072969 + 3 ^ 40 * 5095408 * 2
def baseEnd_5095408 : Nat := 2616393434764705426466651

theorem tailTrace_5095408 : CollatzResearch.WordTrace tailWord_5095408 prefixEnd_5095408 2616393434764705426466651 := by
  unfold tailWord_5095408
  simp only [CollatzResearch.WordTrace]
  refine ⟨92922398762107258624623439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123896531682809678166164585 92922398762107258624623439)
  ·
    refine ⟨139383598143160887936935159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92922398762107258624623439 139383598143160887936935159)
    ·
      refine ⟨209075397214741331905402739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139383598143160887936935159 209075397214741331905402739)
      ·
        refine ⟨313613095822111997858104109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209075397214741331905402739 313613095822111997858104109)
        ·
          refine ⟨117604910933291999196789041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313613095822111997858104109 117604910933291999196789041)
          ·
            refine ⟨88203683199968999397591781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117604910933291999196789041 88203683199968999397591781)
            ·
              refine ⟨16538190599994187387048459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88203683199968999397591781 16538190599994187387048459)
              ·
                refine ⟨24807285899991281080572689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16538190599994187387048459 24807285899991281080572689)
                ·
                  refine ⟨18605464424993460810429517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24807285899991281080572689 18605464424993460810429517)
                  ·
                    refine ⟨6977049159372547803911069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18605464424993460810429517 6977049159372547803911069)
                    ·
                      refine ⟨2616393434764705426466651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977049159372547803911069 2616393434764705426466651)
                      ·
                        rfl

theorem cell23_5095408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_5095408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095408 prefixEnd_5095408 := by exact prefixLift 5095408
  have htrace : WordTrace (prefixWord ++ tailWord_5095408) baseStart_5095408 baseEnd_5095408 := by
    simpa [prefixWord, tailWord_5095408, baseEnd_5095408] using wordTrace_append hprefix tailTrace_5095408
  have hstable : (prefixWord ++ tailWord_5095408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095408).length < 2 ^ (prefixWord ++ tailWord_5095408).sum := by decide
  have hdescent : baseEnd_5095408 < baseStart_5095408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095409 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_5095409 : Nat := 118140960795 + 5095409 * 2 ^ 59
def prefixEnd_5095409 : Nat := 4983230072969 + 3 ^ 40 * 5095409 * 2
def baseEnd_5095409 : Nat := 2616393948245359922554147

theorem tailTrace_5095409 : CollatzResearch.WordTrace tailWord_5095409 prefixEnd_5095409 2616393948245359922554147 := by
  unfold tailWord_5095409
  simp only [CollatzResearch.WordTrace]
  refine ⟨185844833997210894420033281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123896555998140596280022187 185844833997210894420033281)
  ·
    refine ⟨139383625497908170815024961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185844833997210894420033281 139383625497908170815024961)
    ·
      refine ⟨104537719123431128111268721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139383625497908170815024961 104537719123431128111268721)
      ·
        refine ⟨78403289342573346083451541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104537719123431128111268721 78403289342573346083451541)
        ·
          refine ⟨3675154187933125597661791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78403289342573346083451541 3675154187933125597661791)
          ·
            refine ⟨5512731281899688396492687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675154187933125597661791 5512731281899688396492687)
            ·
              refine ⟨8269096922849532594739031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512731281899688396492687 8269096922849532594739031)
              ·
                refine ⟨12403645384274298892108547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269096922849532594739031 12403645384274298892108547)
                ·
                  refine ⟨18605468076411448338162821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12403645384274298892108547 18605468076411448338162821)
                  ·
                    refine ⟨3488525264327146563405529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18605468076411448338162821 3488525264327146563405529)
                    ·
                      refine ⟨2616393948245359922554147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488525264327146563405529 2616393948245359922554147)
                      ·
                        rfl

theorem cell23_5095409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_5095409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095409 prefixEnd_5095409 := by exact prefixLift 5095409
  have htrace : WordTrace (prefixWord ++ tailWord_5095409) baseStart_5095409 baseEnd_5095409 := by
    simpa [prefixWord, tailWord_5095409, baseEnd_5095409] using wordTrace_append hprefix tailTrace_5095409
  have hstable : (prefixWord ++ tailWord_5095409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095409).length < 2 ^ (prefixWord ++ tailWord_5095409).sum := by decide
  have hdescent : baseEnd_5095409 < baseStart_5095409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095438 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5095438 : Nat := 118140960795 + 5095438 * 2 ^ 59
def prefixEnd_5095438 : Nat := 4983230072969 + 3 ^ 40 * 5095438 * 2
def baseEnd_5095438 : Nat := 2616408839184340309091513

theorem tailTrace_5095438 : CollatzResearch.WordTrace tailWord_5095438 prefixEnd_5095438 2616408839184340309091513 := by
  unfold tailWord_5095438
  simp only [CollatzResearch.WordTrace]
  refine ⟨23230736464263229046604871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123897261142737221581892645 23230736464263229046604871)
  ·
    refine ⟨34846104696394843569907307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23230736464263229046604871 34846104696394843569907307)
    ·
      refine ⟨52269157044592265354860961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34846104696394843569907307 52269157044592265354860961)
      ·
        refine ⟨39201867783444199016145721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52269157044592265354860961 39201867783444199016145721)
        ·
          refine ⟨29401400837583149262109291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39201867783444199016145721 29401400837583149262109291)
          ·
            refine ⟨44102101256374723893163937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29401400837583149262109291 44102101256374723893163937)
            ·
              refine ⟨33076575942281042919872953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44102101256374723893163937 33076575942281042919872953)
              ·
                refine ⟨24807431956710782189904715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33076575942281042919872953 24807431956710782189904715)
                ·
                  refine ⟨37211147935066173284857073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24807431956710782189904715 37211147935066173284857073)
                  ·
                    refine ⟨27908360951299629963642805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37211147935066173284857073 27908360951299629963642805)
                    ·
                      refine ⟨2616408839184340309091513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27908360951299629963642805 2616408839184340309091513)
                      ·
                        rfl

theorem cell23_5095438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5095438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095438 prefixEnd_5095438 := by exact prefixLift 5095438
  have htrace : WordTrace (prefixWord ++ tailWord_5095438) baseStart_5095438 baseEnd_5095438 := by
    simpa [prefixWord, tailWord_5095438, baseEnd_5095438] using wordTrace_append hprefix tailTrace_5095438
  have hstable : (prefixWord ++ tailWord_5095438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095438).length < 2 ^ (prefixWord ++ tailWord_5095438).sum := by decide
  have hdescent : baseEnd_5095438 < baseStart_5095438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095445 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_5095445 : Nat := 118140960795 + 5095445 * 2 ^ 59
def prefixEnd_5095445 : Nat := 4983230072969 + 3 ^ 40 * 5095445 * 2
def baseEnd_5095445 : Nat := 872137477849640593901327

theorem tailTrace_5095445 : CollatzResearch.WordTrace tailWord_5095445 prefixEnd_5095445 872137477849640593901327 := by
  unfold tailWord_5095445
  simp only [CollatzResearch.WordTrace]
  refine ⟨185846147025080472568343789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123897431350053648378895859 185846147025080472568343789)
  ·
    refine ⟨69692305134405177213128921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185846147025080472568343789 69692305134405177213128921)
    ·
      refine ⟨52269228850803882909846691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69692305134405177213128921 52269228850803882909846691)
      ·
        refine ⟨78403843276205824364770037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52269228850803882909846691 78403843276205824364770037)
        ·
          refine ⟨7350360307144296034197191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78403843276205824364770037 7350360307144296034197191)
          ·
            refine ⟨11025540460716444051295787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7350360307144296034197191 11025540460716444051295787)
            ·
              refine ⟨16538310691074666076943681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025540460716444051295787 16538310691074666076943681)
              ·
                refine ⟨12403733018305999557707761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16538310691074666076943681 12403733018305999557707761)
                ·
                  refine ⟨9302799763729499668280821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12403733018305999557707761 9302799763729499668280821)
                  ·
                    refine ⟨872137477849640593901327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9302799763729499668280821 872137477849640593901327)
                    ·
                      rfl

theorem cell23_5095445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_5095445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095445 prefixEnd_5095445 := by exact prefixLift 5095445
  have htrace : WordTrace (prefixWord ++ tailWord_5095445) baseStart_5095445 baseEnd_5095445 := by
    simpa [prefixWord, tailWord_5095445, baseEnd_5095445] using wordTrace_append hprefix tailTrace_5095445
  have hstable : (prefixWord ++ tailWord_5095445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095445).length < 2 ^ (prefixWord ++ tailWord_5095445).sum := by decide
  have hdescent : baseEnd_5095445 < baseStart_5095445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095451 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_5095451 : Nat := 118140960795 + 5095451 * 2 ^ 59
def prefixEnd_5095451 : Nat := 4983230072969 + 3 ^ 40 * 5095451 * 2
def baseEnd_5095451 : Nat := 2616415514432848758228953

theorem tailTrace_5095451 : CollatzResearch.WordTrace tailWord_5095451 prefixEnd_5095451 2616415514432848758228953 := by
  unfold tailWord_5095451
  simp only [CollatzResearch.WordTrace]
  refine ⟨185846365863058735593062207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123897577242039157062041471 185846365863058735593062207)
  ·
    refine ⟨278769548794588103389593311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185846365863058735593062207 278769548794588103389593311)
    ·
      refine ⟨418154323191882155084389967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278769548794588103389593311 418154323191882155084389967)
      ·
        refine ⟨627231484787823232626584951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418154323191882155084389967 627231484787823232626584951)
        ·
          refine ⟨940847227181734848939877427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627231484787823232626584951 940847227181734848939877427)
          ·
            refine ⟨1411270840772602273409816141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940847227181734848939877427 1411270840772602273409816141)
            ·
              refine ⟨529226565289725852528681053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411270840772602273409816141 529226565289725852528681053)
              ·
                refine ⟨198459961983647194698255395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529226565289725852528681053 198459961983647194698255395)
                ·
                  refine ⟨297689942975470792047383093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198459961983647194698255395 297689942975470792047383093)
                  ·
                    refine ⟨27908432153950386754442165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 297689942975470792047383093 27908432153950386754442165)
                    ·
                      refine ⟨2616415514432848758228953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27908432153950386754442165 2616415514432848758228953)
                      ·
                        rfl

theorem cell23_5095451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_5095451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095451 prefixEnd_5095451 := by exact prefixLift 5095451
  have htrace : WordTrace (prefixWord ++ tailWord_5095451) baseStart_5095451 baseEnd_5095451 := by
    simpa [prefixWord, tailWord_5095451, baseEnd_5095451] using wordTrace_append hprefix tailTrace_5095451
  have hstable : (prefixWord ++ tailWord_5095451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095451).length < 2 ^ (prefixWord ++ tailWord_5095451).sum := by decide
  have hdescent : baseEnd_5095451 < baseStart_5095451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095468 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_5095468 : Nat := 118140960795 + 5095468 * 2 ^ 59
def prefixEnd_5095468 : Nat := 4983230072969 + 3 ^ 40 * 5095468 * 2
def baseEnd_5095468 : Nat := 2616424243603975191716375

theorem tailTrace_5095468 : CollatzResearch.WordTrace tailWord_5095468 prefixEnd_5095468 2616424243603975191716375 := by
  unfold tailWord_5095468
  simp only [CollatzResearch.WordTrace]
  refine ⟨92923492951998573748215529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123897990602664764997620705 92923492951998573748215529)
  ·
    refine ⟨69692619713998930311161647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92923492951998573748215529 69692619713998930311161647)
    ·
      refine ⟨104538929570998395466742471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69692619713998930311161647 104538929570998395466742471)
      ·
        refine ⟨156808394356497593200113707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104538929570998395466742471 156808394356497593200113707)
        ·
          refine ⟨235212591534746389800170561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156808394356497593200113707 235212591534746389800170561)
          ·
            refine ⟨176409443651059792350127921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235212591534746389800170561 176409443651059792350127921)
            ·
              refine ⟨132307082738294844262595941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176409443651059792350127921 132307082738294844262595941)
              ·
                refine ⟨24807578013430283299236739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132307082738294844262595941 24807578013430283299236739)
                ·
                  refine ⟨37211367020145424948855109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24807578013430283299236739 37211367020145424948855109)
                  ·
                    refine ⟨6977131316277267177910333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37211367020145424948855109 6977131316277267177910333)
                    ·
                      refine ⟨2616424243603975191716375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977131316277267177910333 2616424243603975191716375)
                      ·
                        rfl

theorem cell23_5095468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_5095468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095468 prefixEnd_5095468 := by exact prefixLift 5095468
  have htrace : WordTrace (prefixWord ++ tailWord_5095468) baseStart_5095468 baseEnd_5095468 := by
    simpa [prefixWord, tailWord_5095468, baseEnd_5095468] using wordTrace_append hprefix tailTrace_5095468
  have hstable : (prefixWord ++ tailWord_5095468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095468).length < 2 ^ (prefixWord ++ tailWord_5095468).sum := by decide
  have hdescent : baseEnd_5095468 < baseStart_5095468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095471 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 10]
def baseStart_5095471 : Nat := 118140960795 + 5095471 * 2 ^ 59
def prefixEnd_5095471 : Nat := 4983230072969 + 3 ^ 40 * 5095471 * 2
def baseEnd_5095471 : Nat := 290713976005104297775429

theorem tailTrace_5095471 : CollatzResearch.WordTrace tailWord_5095471 prefixEnd_5095471 290713976005104297775429 := by
  unfold tailWord_5095471
  simp only [CollatzResearch.WordTrace]
  refine ⟨185847095322986279008790267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123898063548657519339193511 185847095322986279008790267)
  ·
    refine ⟨278770642984479418513185401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185847095322986279008790267 278770642984479418513185401)
    ·
      refine ⟨209077982238359563884889051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278770642984479418513185401 209077982238359563884889051)
      ·
        refine ⟨313616973357539345827333577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209077982238359563884889051 313616973357539345827333577)
        ·
          refine ⟨235212730018154509370500183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313616973357539345827333577 235212730018154509370500183)
          ·
            refine ⟨352819095027231764055750275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235212730018154509370500183 352819095027231764055750275)
            ·
              refine ⟨529228642540847646083625413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352819095027231764055750275 529228642540847646083625413)
              ·
                refine ⟨99230370476408933640679765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529228642540847646083625413 99230370476408933640679765)
                ·
                  refine ⟨290713976005104297775429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 99230370476408933640679765 290713976005104297775429)
                  ·
                    rfl

theorem cell23_5095471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 10].length) (baseStart_5095471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095471 prefixEnd_5095471 := by exact prefixLift 5095471
  have htrace : WordTrace (prefixWord ++ tailWord_5095471) baseStart_5095471 baseEnd_5095471 := by
    simpa [prefixWord, tailWord_5095471, baseEnd_5095471] using wordTrace_append hprefix tailTrace_5095471
  have hstable : (prefixWord ++ tailWord_5095471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095471).length < 2 ^ (prefixWord ++ tailWord_5095471).sum := by decide
  have hdescent : baseEnd_5095471 < baseStart_5095471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095508 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5095508 : Nat := 118140960795 + 5095508 * 2 ^ 59
def prefixEnd_5095508 : Nat := 4983230072969 + 3 ^ 40 * 5095508 * 2
def baseEnd_5095508 : Nat := 2616444782830155035216191

theorem tailTrace_5095508 : CollatzResearch.WordTrace tailWord_5095508 prefixEnd_5095508 2616444782830155035216191 := by
  unfold tailWord_5095508
  simp only [CollatzResearch.WordTrace]
  refine ⟨92924222411926117163943589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123898963215901489551924785 92924222411926117163943589)
  ·
    refine ⟨17423291702236146968239423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92924222411926117163943589 17423291702236146968239423)
    ·
      refine ⟨26134937553354220452359135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17423291702236146968239423 26134937553354220452359135)
      ·
        refine ⟨39202406330031330678538703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26134937553354220452359135 39202406330031330678538703)
        ·
          refine ⟨58803609495046996017808055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39202406330031330678538703 58803609495046996017808055)
          ·
            refine ⟨88205414242570494026712083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58803609495046996017808055 88205414242570494026712083)
            ·
              refine ⟨132308121363855741040068125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88205414242570494026712083 132308121363855741040068125)
              ·
                refine ⟨49615545511445902890025547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132308121363855741040068125 49615545511445902890025547)
                ·
                  refine ⟨74423318267168854335038321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49615545511445902890025547 74423318267168854335038321)
                  ·
                    refine ⟨55817488700376640751278741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74423318267168854335038321 55817488700376640751278741)
                    ·
                      refine ⟨2616444782830155035216191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55817488700376640751278741 2616444782830155035216191)
                      ·
                        rfl

theorem cell23_5095508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5095508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095508 prefixEnd_5095508 := by exact prefixLift 5095508
  have htrace : WordTrace (prefixWord ++ tailWord_5095508) baseStart_5095508 baseEnd_5095508 := by
    simpa [prefixWord, tailWord_5095508, baseEnd_5095508] using wordTrace_append hprefix tailTrace_5095508
  have hstable : (prefixWord ++ tailWord_5095508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095508).length < 2 ^ (prefixWord ++ tailWord_5095508).sum := by decide
  have hdescent : baseEnd_5095508 < baseStart_5095508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095509 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_5095509 : Nat := 118140960795 + 5095509 * 2 ^ 59
def prefixEnd_5095509 : Nat := 4983230072969 + 3 ^ 40 * 5095509 * 2
def baseEnd_5095509 : Nat := 872148432103603177101229

theorem tailTrace_5095509 : CollatzResearch.WordTrace tailWord_5095509 prefixEnd_5095509 872148432103603177101229 := by
  unfold tailWord_5095509
  simp only [CollatzResearch.WordTrace]
  refine ⟨185848481296848611498673581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123898987531232407665782387 185848481296848611498673581)
  ·
    refine ⟨69693180486318229312002593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185848481296848611498673581 69693180486318229312002593)
    ·
      refine ⟨52269885364738671984001945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69693180486318229312002593 52269885364738671984001945)
      ·
        refine ⟨39202414023554003988001459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52269885364738671984001945 39202414023554003988001459)
        ·
          refine ⟨58803621035331005982002189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39202414023554003988001459 58803621035331005982002189)
          ·
            refine ⟨22051357888249127243250821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58803621035331005982002189 22051357888249127243250821)
            ·
              refine ⟨4134629604046711358109529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22051357888249127243250821 4134629604046711358109529)
              ·
                refine ⟨3100972203035033518582147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134629604046711358109529 3100972203035033518582147)
                ·
                  refine ⟨4651458304552550277873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100972203035033518582147 4651458304552550277873221)
                  ·
                    refine ⟨872148432103603177101229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651458304552550277873221 872148432103603177101229)
                    ·
                      rfl

theorem cell23_5095509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_5095509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095509 prefixEnd_5095509 := by exact prefixLift 5095509
  have htrace : WordTrace (prefixWord ++ tailWord_5095509) baseStart_5095509 baseEnd_5095509 := by
    simpa [prefixWord, tailWord_5095509, baseEnd_5095509] using wordTrace_append hprefix tailTrace_5095509
  have hstable : (prefixWord ++ tailWord_5095509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095509).length < 2 ^ (prefixWord ++ tailWord_5095509).sum := by decide
  have hdescent : baseEnd_5095509 < baseStart_5095509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095532 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_5095532 : Nat := 118140960795 + 5095532 * 2 ^ 59
def prefixEnd_5095532 : Nat := 4983230072969 + 3 ^ 40 * 5095532 * 2
def baseEnd_5095532 : Nat := 2616457106365862941316081

theorem tailTrace_5095532 : CollatzResearch.WordTrace tailWord_5095532 prefixEnd_5095532 2616457106365862941316081 := by
  unfold tailWord_5095532
  simp only [CollatzResearch.WordTrace]
  refine ⟨92924660087882643213380425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123899546783843524284507233 92924660087882643213380425)
  ·
    refine ⟨69693495065911982410035319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92924660087882643213380425 69693495065911982410035319)
    ·
      refine ⟨104540242598867973615052979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69693495065911982410035319 104540242598867973615052979)
      ·
        refine ⟨156810363898301960422579469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104540242598867973615052979 156810363898301960422579469)
        ·
          refine ⟨58803886461863235158467301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156810363898301960422579469 58803886461863235158467301)
          ·
            refine ⟨11025728711599356592212619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58803886461863235158467301 11025728711599356592212619)
            ·
              refine ⟨16538593067399034888318929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025728711599356592212619 16538593067399034888318929)
              ·
                refine ⟨12403944800549276166239197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16538593067399034888318929 12403944800549276166239197)
                ·
                  refine ⟨4651479300205978562339699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12403944800549276166239197 4651479300205978562339699)
                  ·
                    refine ⟨6977218950308967843509549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4651479300205978562339699 6977218950308967843509549)
                    ·
                      refine ⟨2616457106365862941316081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977218950308967843509549 2616457106365862941316081)
                      ·
                        rfl

theorem cell23_5095532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_5095532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095532 prefixEnd_5095532 := by exact prefixLift 5095532
  have htrace : WordTrace (prefixWord ++ tailWord_5095532) baseStart_5095532 baseEnd_5095532 := by
    simpa [prefixWord, tailWord_5095532, baseEnd_5095532] using wordTrace_append hprefix tailTrace_5095532
  have hstable : (prefixWord ++ tailWord_5095532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095532).length < 2 ^ (prefixWord ++ tailWord_5095532).sum := by decide
  have hdescent : baseEnd_5095532 < baseStart_5095532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095549 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_5095549 : Nat := 118140960795 + 5095549 * 2 ^ 59
def prefixEnd_5095549 : Nat := 4983230072969 + 3 ^ 40 * 5095549 * 2
def baseEnd_5095549 : Nat := 2616465835536989374803503

theorem tailTrace_5095549 : CollatzResearch.WordTrace tailWord_5095549 prefixEnd_5095549 2616465835536989374803503 := by
  unfold tailWord_5095549
  simp only [CollatzResearch.WordTrace]
  refine ⟨185849940216703698330129701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123899960144469132220086467 185849940216703698330129701)
  ·
    refine ⟨34846863790631943436899319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185849940216703698330129701 34846863790631943436899319)
    ·
      refine ⟨52270295685947915155348979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34846863790631943436899319 52270295685947915155348979)
      ·
        refine ⟨78405443528921872733023469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52270295685947915155348979 78405443528921872733023469)
        ·
          refine ⟨29402041323345702274883801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78405443528921872733023469 29402041323345702274883801)
          ·
            refine ⟨22051530992509276706162851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29402041323345702274883801 22051530992509276706162851)
            ·
              refine ⟨33077296488763915059244277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22051530992509276706162851 33077296488763915059244277)
              ·
                refine ⟨3100996545821617036804151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33077296488763915059244277 3100996545821617036804151)
                ·
                  refine ⟨4651494818732425555206227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100996545821617036804151 4651494818732425555206227)
                  ·
                    refine ⟨6977242228098638332809341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4651494818732425555206227 6977242228098638332809341)
                    ·
                      refine ⟨2616465835536989374803503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977242228098638332809341 2616465835536989374803503)
                      ·
                        rfl

theorem cell23_5095549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_5095549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095549 prefixEnd_5095549 := by exact prefixLift 5095549
  have htrace : WordTrace (prefixWord ++ tailWord_5095549) baseStart_5095549 baseEnd_5095549 := by
    simpa [prefixWord, tailWord_5095549, baseEnd_5095549] using wordTrace_append hprefix tailTrace_5095549
  have hstable : (prefixWord ++ tailWord_5095549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095549).length < 2 ^ (prefixWord ++ tailWord_5095549).sum := by decide
  have hdescent : baseEnd_5095549 < baseStart_5095549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095568 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_5095568 : Nat := 118140960795 + 5095568 * 2 ^ 59
def prefixEnd_5095568 : Nat := 4983230072969 + 3 ^ 40 * 5095568 * 2
def baseEnd_5095568 : Nat := 2616475591669424800465915

theorem tailTrace_5095568 : CollatzResearch.WordTrace tailWord_5095568 prefixEnd_5095568 2616475591669424800465915 := by
  unfold tailWord_5095568
  simp only [CollatzResearch.WordTrace]
  refine ⟨92925316601817432287535679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123900422135756576383380905 92925316601817432287535679)
  ·
    refine ⟨139387974902726148431303519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92925316601817432287535679 139387974902726148431303519)
    ·
      refine ⟨209081962354089222646955279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139387974902726148431303519 209081962354089222646955279)
      ·
        refine ⟨313622943531133833970432919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209081962354089222646955279 313622943531133833970432919)
        ·
          refine ⟨470434415296700750955649379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313622943531133833970432919 470434415296700750955649379)
          ·
            refine ⟨705651622945051126433474069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470434415296700750955649379 705651622945051126433474069)
            ·
              refine ⟨33077419825549271551569097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 705651622945051126433474069 33077419825549271551569097)
              ·
                refine ⟨24808064869161953663676823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33077419825549271551569097 24808064869161953663676823)
                ·
                  refine ⟨37212097303742930495515235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24808064869161953663676823 37212097303742930495515235)
                  ·
                    refine ⟨55818145955614395743272853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37212097303742930495515235 55818145955614395743272853)
                    ·
                      refine ⟨2616475591669424800465915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55818145955614395743272853 2616475591669424800465915)
                      ·
                        rfl

theorem cell23_5095568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_5095568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095568 prefixEnd_5095568 := by exact prefixLift 5095568
  have htrace : WordTrace (prefixWord ++ tailWord_5095568) baseStart_5095568 baseEnd_5095568 := by
    simpa [prefixWord, tailWord_5095568, baseEnd_5095568] using wordTrace_append hprefix tailTrace_5095568
  have hstable : (prefixWord ++ tailWord_5095568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095568).length < 2 ^ (prefixWord ++ tailWord_5095568).sum := by decide
  have hdescent : baseEnd_5095568 < baseStart_5095568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095585 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5095585 : Nat := 118140960795 + 5095585 * 2 ^ 59
def prefixEnd_5095585 : Nat := 4983230072969 + 3 ^ 40 * 5095585 * 2
def baseEnd_5095585 : Nat := 2616484320840551233953337

theorem tailTrace_5095585 : CollatzResearch.WordTrace tailWord_5095585 prefixEnd_5095585 2616484320840551233953337 := by
  unfold tailWord_5095585
  simp only [CollatzResearch.WordTrace]
  refine ⟨185851253244573276478440209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123900835496382184318960139 185851253244573276478440209)
  ·
    refine ⟨139388439933429957358830157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185851253244573276478440209 139388439933429957358830157)
    ·
      refine ⟨52270664975036234009561309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139388439933429957358830157 52270664975036234009561309)
      ·
        refine ⟨19601499365638587753585491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52270664975036234009561309 19601499365638587753585491)
        ·
          refine ⟨29402249048457881630378237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19601499365638587753585491 29402249048457881630378237)
          ·
            refine ⟨11025843393171705611391839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29402249048457881630378237 11025843393171705611391839)
            ·
              refine ⟨16538765089757558417087759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025843393171705611391839 16538765089757558417087759)
              ·
                refine ⟨24808147634636337625631639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16538765089757558417087759 24808147634636337625631639)
                ·
                  refine ⟨37212221451954506438447459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24808147634636337625631639 37212221451954506438447459)
                  ·
                    refine ⟨55818332177931759657671189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37212221451954506438447459 55818332177931759657671189)
                    ·
                      refine ⟨2616484320840551233953337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55818332177931759657671189 2616484320840551233953337)
                      ·
                        rfl

theorem cell23_5095585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5095585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095585 prefixEnd_5095585 := by exact prefixLift 5095585
  have htrace : WordTrace (prefixWord ++ tailWord_5095585) baseStart_5095585 baseEnd_5095585 := by
    simpa [prefixWord, tailWord_5095585, baseEnd_5095585] using wordTrace_append hprefix tailTrace_5095585
  have hstable : (prefixWord ++ tailWord_5095585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095585).length < 2 ^ (prefixWord ++ tailWord_5095585).sum := by decide
  have hdescent : baseEnd_5095585 < baseStart_5095585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095612 : List Nat := [2, 2, 2, 3, 4, 1, 9]
def baseStart_5095612 : Nat := 118140960795 + 5095612 * 2 ^ 59
def prefixEnd_5095612 : Nat := 4983230072969 + 3 ^ 40 * 5095612 * 2
def baseEnd_5095612 : Nat := 32302446726150896645873

theorem tailTrace_5095612 : CollatzResearch.WordTrace tailWord_5095612 prefixEnd_5095612 32302446726150896645873 := by
  unfold tailWord_5095612
  simp only [CollatzResearch.WordTrace]
  refine ⟨92926119007737730044836545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123901492010316973393115393 92926119007737730044836545)
  ·
    refine ⟨69694589255803297533627409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92926119007737730044836545 69694589255803297533627409)
    ·
      refine ⟨52270941941852473150220557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69694589255803297533627409 52270941941852473150220557)
      ·
        refine ⟨19601603228194677431332709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52270941941852473150220557 19601603228194677431332709)
        ·
          refine ⟨3675300605286502018374883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19601603228194677431332709 3675300605286502018374883)
          ·
            refine ⟨5512950907929753027562325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675300605286502018374883 5512950907929753027562325)
            ·
              refine ⟨32302446726150896645873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5512950907929753027562325 32302446726150896645873)
              ·
                rfl

theorem cell23_5095612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 9].length) (baseStart_5095612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095612 prefixEnd_5095612 := by exact prefixLift 5095612
  have htrace : WordTrace (prefixWord ++ tailWord_5095612) baseStart_5095612 baseEnd_5095612 := by
    simpa [prefixWord, tailWord_5095612, baseEnd_5095612] using wordTrace_append hprefix tailTrace_5095612
  have hstable : (prefixWord ++ tailWord_5095612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095612).length < 2 ^ (prefixWord ++ tailWord_5095612).sum := by decide
  have hdescent : baseEnd_5095612 < baseStart_5095612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095665 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_5095665 : Nat := 118140960795 + 5095665 * 2 ^ 59
def prefixEnd_5095665 : Nat := 4983230072969 + 3 ^ 40 * 5095665 * 2
def baseEnd_5095665 : Nat := 2616525399292910920952969

theorem tailTrace_5095665 : CollatzResearch.WordTrace tailWord_5095665 prefixEnd_5095665 2616525399292910920952969 := by
  unfold tailWord_5095665
  simp only [CollatzResearch.WordTrace]
  refine ⟨185854171084283450141352449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123902780722855633427568299 185854171084283450141352449)
  ·
    refine ⟨139390628313212587606014337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185854171084283450141352449 139390628313212587606014337)
    ·
      refine ⟨104542971234909440704510753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139390628313212587606014337 104542971234909440704510753)
      ·
        refine ⟨78407228426182080528383065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104542971234909440704510753 78407228426182080528383065)
        ·
          refine ⟨58805421319636560396287299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78407228426182080528383065 58805421319636560396287299)
          ·
            refine ⟨88208131979454840594430949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58805421319636560396287299 88208131979454840594430949)
            ·
              refine ⟨16539024746147782611455803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88208131979454840594430949 16539024746147782611455803)
              ·
                refine ⟨24808537119221673917183705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16539024746147782611455803 24808537119221673917183705)
                ·
                  refine ⟨18606402839416255437887779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24808537119221673917183705 18606402839416255437887779)
                  ·
                    refine ⟨27909604259124383156831669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18606402839416255437887779 27909604259124383156831669)
                    ·
                      refine ⟨2616525399292910920952969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27909604259124383156831669 2616525399292910920952969)
                      ·
                        rfl

theorem cell23_5095665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_5095665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095665 prefixEnd_5095665 := by exact prefixLift 5095665
  have htrace : WordTrace (prefixWord ++ tailWord_5095665) baseStart_5095665 baseEnd_5095665 := by
    simpa [prefixWord, tailWord_5095665, baseEnd_5095665] using wordTrace_append hprefix tailTrace_5095665
  have hstable : (prefixWord ++ tailWord_5095665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095665).length < 2 ^ (prefixWord ++ tailWord_5095665).sum := by decide
  have hdescent : baseEnd_5095665 < baseStart_5095665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095715 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 7]
def baseStart_5095715 : Nat := 118140960795 + 5095715 * 2 ^ 59
def prefixEnd_5095715 : Nat := 4983230072969 + 3 ^ 40 * 5095715 * 2
def baseEnd_5095715 : Nat := 872183691108545241775913

theorem tailTrace_5095715 : CollatzResearch.WordTrace tailWord_5095715 prefixEnd_5095715 872183691108545241775913 := by
  unfold tailWord_5095715
  simp only [CollatzResearch.WordTrace]
  refine ⟨185855994734102308680672599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123903996489401539120448399 185855994734102308680672599)
  ·
    refine ⟨278783992101153463021008899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185855994734102308680672599 278783992101153463021008899)
    ·
      refine ⟨418175988151730194531513349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278783992101153463021008899 418175988151730194531513349)
      ·
        refine ⟨78407997778449411474658753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418175988151730194531513349 78407997778449411474658753)
        ·
          refine ⟨58805998333837058605994065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78407997778449411474658753 58805998333837058605994065)
          ·
            refine ⟨44104498750377793954495549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58805998333837058605994065 44104498750377793954495549)
            ·
              refine ⟨16539187031391672732935831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44104498750377793954495549 16539187031391672732935831)
              ·
                refine ⟨24808780547087509099403747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16539187031391672732935831 24808780547087509099403747)
                ·
                  refine ⟨37213170820631263649105621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24808780547087509099403747 37213170820631263649105621)
                  ·
                    refine ⟨872183691108545241775913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37213170820631263649105621 872183691108545241775913)
                    ·
                      rfl

theorem cell23_5095715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_5095715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095715 prefixEnd_5095715 := by exact prefixLift 5095715
  have htrace : WordTrace (prefixWord ++ tailWord_5095715) baseStart_5095715 baseEnd_5095715 := by
    simpa [prefixWord, tailWord_5095715, baseEnd_5095715] using wordTrace_append hprefix tailTrace_5095715
  have hstable : (prefixWord ++ tailWord_5095715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095715).length < 2 ^ (prefixWord ++ tailWord_5095715).sum := by decide
  have hdescent : baseEnd_5095715 < baseStart_5095715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095730 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_5095730 : Nat := 118140960795 + 5095730 * 2 ^ 59
def prefixEnd_5095730 : Nat := 4983230072969 + 3 ^ 40 * 5095730 * 2
def baseEnd_5095730 : Nat := 2616558775535453166640171

theorem tailTrace_5095730 : CollatzResearch.WordTrace tailWord_5095730 prefixEnd_5095730 2616558775535453166640171 := by
  unfold tailWord_5095730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46464135457261991560617161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123904361219365310828312429 46464135457261991560617161)
  ·
    refine ⟨34848101592946493670462871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46464135457261991560617161 34848101592946493670462871)
    ·
      refine ⟨52272152389419740505694307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34848101592946493670462871 52272152389419740505694307)
      ·
        refine ⟨78408228584129610758541461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52272152389419740505694307 78408228584129610758541461)
        ·
          refine ⟨3675385714881075504306631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78408228584129610758541461 3675385714881075504306631)
          ·
            refine ⟨5513078572321613256459947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675385714881075504306631 5513078572321613256459947)
            ·
              refine ⟨8269617858482419884689921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513078572321613256459947 8269617858482419884689921)
              ·
                refine ⟨6202213393861814913517441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8269617858482419884689921 6202213393861814913517441)
                ·
                  refine ⟨4651660045396361185138081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6202213393861814913517441 4651660045396361185138081)
                  ·
                    refine ⟨3488745034047270888853561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4651660045396361185138081 3488745034047270888853561)
                    ·
                      refine ⟨2616558775535453166640171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3488745034047270888853561 2616558775535453166640171)
                      ·
                        rfl

theorem cell23_5095730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_5095730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095730 prefixEnd_5095730 := by exact prefixLift 5095730
  have htrace : WordTrace (prefixWord ++ tailWord_5095730) baseStart_5095730 baseEnd_5095730 := by
    simpa [prefixWord, tailWord_5095730, baseEnd_5095730] using wordTrace_append hprefix tailTrace_5095730
  have hstable : (prefixWord ++ tailWord_5095730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095730).length < 2 ^ (prefixWord ++ tailWord_5095730).sum := by decide
  have hdescent : baseEnd_5095730 < baseStart_5095730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095775 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 8]
def baseStart_5095775 : Nat := 118140960795 + 5095775 * 2 ^ 59
def prefixEnd_5095775 : Nat := 4983230072969 + 3 ^ 40 * 5095775 * 2
def baseEnd_5095775 : Nat := 290731320240545054508607

theorem tailTrace_5095775 : CollatzResearch.WordTrace tailWord_5095775 prefixEnd_5095775 290731320240545054508607 := by
  unfold tailWord_5095775
  simp only [CollatzResearch.WordTrace]
  refine ⟨185858183113884938927856779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123905455409256625951904519 185858183113884938927856779)
  ·
    refine ⟨278787274670827408391785169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185858183113884938927856779 278787274670827408391785169)
    ·
      refine ⟨209090456003120556293838877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278787274670827408391785169 209090456003120556293838877)
      ·
        refine ⟨78408921001170208610189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209090456003120556293838877 78408921001170208610189579)
        ·
          refine ⟨117613381501755312915284369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78408921001170208610189579 117613381501755312915284369)
          ·
            refine ⟨88210036126316484686463277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117613381501755312915284369 88210036126316484686463277)
            ·
              refine ⟨33078763547368681757423729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88210036126316484686463277 33078763547368681757423729)
              ·
                refine ⟨24809072660526511318067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33078763547368681757423729 24809072660526511318067797)
                ·
                  refine ⟨290731320240545054508607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24809072660526511318067797 290731320240545054508607)
                  ·
                    rfl

theorem cell23_5095775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 8].length) (baseStart_5095775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095775 prefixEnd_5095775 := by exact prefixLift 5095775
  have htrace : WordTrace (prefixWord ++ tailWord_5095775) baseStart_5095775 baseEnd_5095775 := by
    simpa [prefixWord, tailWord_5095775, baseEnd_5095775] using wordTrace_append hprefix tailTrace_5095775
  have hstable : (prefixWord ++ tailWord_5095775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095775).length < 2 ^ (prefixWord ++ tailWord_5095775).sum := by decide
  have hdescent : baseEnd_5095775 < baseStart_5095775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095789 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5095789 : Nat := 118140960795 + 5095789 * 2 ^ 59
def prefixEnd_5095789 : Nat := 4983230072969 + 3 ^ 40 * 5095789 * 2
def baseEnd_5095789 : Nat := 2616589070894068435802399

theorem tailTrace_5095789 : CollatzResearch.WordTrace tailWord_5095789 prefixEnd_5095789 2616589070894068435802399 := by
  unfold tailWord_5095789
  simp only [CollatzResearch.WordTrace]
  refine ⟨185858693735834219318866421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123905795823889479545910947 185858693735834219318866421)
  ·
    refine ⟨17424252537734458061143727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185858693735834219318866421 17424252537734458061143727)
    ·
      refine ⟨26136378806601687091715591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17424252537734458061143727 26136378806601687091715591)
      ·
        refine ⟨39204568209902530637573387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26136378806601687091715591 39204568209902530637573387)
        ·
          refine ⟨58806852314853795956360081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39204568209902530637573387 58806852314853795956360081)
          ·
            refine ⟨44105139236140346967270061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58806852314853795956360081 44105139236140346967270061)
            ·
              refine ⟨16539427213552630112726273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44105139236140346967270061 16539427213552630112726273)
              ·
                refine ⟨12404570410164472584544705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16539427213552630112726273 12404570410164472584544705)
                ·
                  refine ⟨9303427807623354438408529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12404570410164472584544705 9303427807623354438408529)
                  ·
                    refine ⟨6977570855717515828806397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9303427807623354438408529 6977570855717515828806397)
                    ·
                      refine ⟨2616589070894068435802399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977570855717515828806397 2616589070894068435802399)
                      ·
                        rfl

theorem cell23_5095789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5095789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095789 prefixEnd_5095789 := by exact prefixLift 5095789
  have htrace : WordTrace (prefixWord ++ tailWord_5095789) baseStart_5095789 baseEnd_5095789 := by
    simpa [prefixWord, tailWord_5095789, baseEnd_5095789] using wordTrace_append hprefix tailTrace_5095789
  have hstable : (prefixWord ++ tailWord_5095789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095789).length < 2 ^ (prefixWord ++ tailWord_5095789).sum := by decide
  have hdescent : baseEnd_5095789 < baseStart_5095789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095809 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 6]
def baseStart_5095809 : Nat := 118140960795 + 5095809 * 2 ^ 59
def prefixEnd_5095809 : Nat := 4983230072969 + 3 ^ 40 * 5095809 * 2
def baseEnd_5095809 : Nat := 290733260056350928616923

theorem tailTrace_5095809 : CollatzResearch.WordTrace tailWord_5095809 prefixEnd_5095809 290733260056350928616923 := by
  unfold tailWord_5095809
  simp only [CollatzResearch.WordTrace]
  refine ⟨185859423195761762734594481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123906282130507841823062987 185859423195761762734594481)
  ·
    refine ⟨139394567396821322050945861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185859423195761762734594481 139394567396821322050945861)
    ·
      refine ⟨26136481386903997884552349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139394567396821322050945861 26136481386903997884552349)
      ·
        refine ⟨9801180520088999206707131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26136481386903997884552349 9801180520088999206707131)
        ·
          refine ⟨14701770780133498810060697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801180520088999206707131 14701770780133498810060697)
          ·
            refine ⟨11026328085100124107545523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14701770780133498810060697 11026328085100124107545523)
            ·
              refine ⟨16539492127650186161318285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11026328085100124107545523 16539492127650186161318285)
              ·
                refine ⟨6202309547868819810494357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16539492127650186161318285 6202309547868819810494357)
                ·
                  refine ⟨290733260056350928616923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6202309547868819810494357 290733260056350928616923)
                  ·
                    rfl

theorem cell23_5095809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_5095809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095809 prefixEnd_5095809 := by exact prefixLift 5095809
  have htrace : WordTrace (prefixWord ++ tailWord_5095809) baseStart_5095809 baseEnd_5095809 := by
    simpa [prefixWord, tailWord_5095809, baseEnd_5095809] using wordTrace_append hprefix tailTrace_5095809
  have hstable : (prefixWord ++ tailWord_5095809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095809).length < 2 ^ (prefixWord ++ tailWord_5095809).sum := by decide
  have hdescent : baseEnd_5095809 < baseStart_5095809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095869 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_5095869 : Nat := 118140960795 + 5095869 * 2 ^ 59
def prefixEnd_5095869 : Nat := 4983230072969 + 3 ^ 40 * 5095869 * 2
def baseEnd_5095869 : Nat := 872210049782142707600677

theorem tailTrace_5095869 : CollatzResearch.WordTrace tailWord_5095869 prefixEnd_5095869 872210049782142707600677 := by
  unfold tailWord_5095869
  simp only [CollatzResearch.WordTrace]
  refine ⟨185861611575544392981778661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123907741050362928654519107 185861611575544392981778661)
  ·
    refine ⟨34849052170414573684083499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185861611575544392981778661 34849052170414573684083499)
    ·
      refine ⟨52273578255621860526125249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34849052170414573684083499 52273578255621860526125249)
      ·
        refine ⟨39205183691716395394593937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52273578255621860526125249 39205183691716395394593937)
        ·
          refine ⟨29403887768787296545945453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39205183691716395394593937 29403887768787296545945453)
          ·
            refine ⟨11026457913295236204729545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29403887768787296545945453 11026457913295236204729545)
            ·
              refine ⟨8269843434971427153547159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11026457913295236204729545 8269843434971427153547159)
              ·
                refine ⟨12404765152457140730320739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269843434971427153547159 12404765152457140730320739)
                ·
                  refine ⟨18607147728685711095481109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12404765152457140730320739 18607147728685711095481109)
                  ·
                    refine ⟨872210049782142707600677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18607147728685711095481109 872210049782142707600677)
                    ·
                      rfl

theorem cell23_5095869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_5095869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095869 prefixEnd_5095869 := by exact prefixLift 5095869
  have htrace : WordTrace (prefixWord ++ tailWord_5095869) baseStart_5095869 baseEnd_5095869 := by
    simpa [prefixWord, tailWord_5095869, baseEnd_5095869] using wordTrace_append hprefix tailTrace_5095869
  have hstable : (prefixWord ++ tailWord_5095869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095869).length < 2 ^ (prefixWord ++ tailWord_5095869).sum := by decide
  have hdescent : baseEnd_5095869 < baseStart_5095869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095879 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_5095879 : Nat := 118140960795 + 5095879 * 2 ^ 59
def prefixEnd_5095879 : Nat := 4983230072969 + 3 ^ 40 * 5095879 * 2
def baseEnd_5095879 : Nat := 2616635284152973083676985

theorem tailTrace_5095879 : CollatzResearch.WordTrace tailWord_5095879 prefixEnd_5095879 2616635284152973083676985 := by
  unfold tailWord_5095879
  simp only [CollatzResearch.WordTrace]
  refine ⟨185861976305508164689642691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123907984203672109793095127 185861976305508164689642691)
  ·
    refine ⟨278792964458262247034464037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185861976305508164689642691 278792964458262247034464037)
    ·
      refine ⟨52273680835924171318962007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278792964458262247034464037 52273680835924171318962007)
      ·
        refine ⟨78410521253886256978443011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52273680835924171318962007 78410521253886256978443011)
        ·
          refine ⟨117615781880829385467664517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78410521253886256978443011 117615781880829385467664517)
          ·
            refine ⟨22052959102655509775187097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117615781880829385467664517 22052959102655509775187097)
            ·
              refine ⟨16539719326991632331390323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22052959102655509775187097 16539719326991632331390323)
              ·
                refine ⟨24809578990487448497085485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16539719326991632331390323 24809578990487448497085485)
                ·
                  refine ⟨9303592121432793186407057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24809578990487448497085485 9303592121432793186407057)
                  ·
                    refine ⟨6977694091074594889805293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9303592121432793186407057 6977694091074594889805293)
                    ·
                      refine ⟨2616635284152973083676985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977694091074594889805293 2616635284152973083676985)
                      ·
                        rfl

theorem cell23_5095879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_5095879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095879 prefixEnd_5095879 := by exact prefixLift 5095879
  have htrace : WordTrace (prefixWord ++ tailWord_5095879) baseStart_5095879 baseEnd_5095879 := by
    simpa [prefixWord, tailWord_5095879, baseEnd_5095879] using wordTrace_append hprefix tailTrace_5095879
  have hstable : (prefixWord ++ tailWord_5095879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095879).length < 2 ^ (prefixWord ++ tailWord_5095879).sum := by decide
  have hdescent : baseEnd_5095879 < baseStart_5095879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095890 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5095890 : Nat := 118140960795 + 5095890 * 2 ^ 59
def prefixEnd_5095890 : Nat := 4983230072969 + 3 ^ 40 * 5095890 * 2
def baseEnd_5095890 : Nat := 872213644146724180213145

theorem tailTrace_5095890 : CollatzResearch.WordTrace tailWord_5095890 prefixEnd_5095890 872213644146724180213145 := by
  unfold tailWord_5095890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46465594377117078392073281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123908251672312209045528749 46465594377117078392073281)
  ·
    refine ⟨34849195782837808794054961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46465594377117078392073281 34849195782837808794054961)
    ·
      refine ⟨26136896837128356595541221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34849195782837808794054961 26136896837128356595541221)
      ·
        refine ⟨4900668156961566861663979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26136896837128356595541221 4900668156961566861663979)
        ·
          refine ⟨7351002235442350292495969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900668156961566861663979 7351002235442350292495969)
          ·
            refine ⟨5513251676581762719371977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351002235442350292495969 5513251676581762719371977)
            ·
              refine ⟨4134938757436322039528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513251676581762719371977 4134938757436322039528983)
              ·
                refine ⟨6202408136154483059293475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134938757436322039528983 6202408136154483059293475)
                ·
                  refine ⟨9303612204231724588940213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202408136154483059293475 9303612204231724588940213)
                  ·
                    refine ⟨872213644146724180213145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9303612204231724588940213 872213644146724180213145)
                    ·
                      rfl

theorem cell23_5095890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5095890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095890 prefixEnd_5095890 := by exact prefixLift 5095890
  have htrace : WordTrace (prefixWord ++ tailWord_5095890) baseStart_5095890 baseEnd_5095890 := by
    simpa [prefixWord, tailWord_5095890, baseEnd_5095890] using wordTrace_append hprefix tailTrace_5095890
  have hstable : (prefixWord ++ tailWord_5095890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095890).length < 2 ^ (prefixWord ++ tailWord_5095890).sum := by decide
  have hdescent : baseEnd_5095890 < baseStart_5095890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095893 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5095893 : Nat := 118140960795 + 5095893 * 2 ^ 59
def prefixEnd_5095893 : Nat := 4983230072969 + 3 ^ 40 * 5095893 * 2
def baseEnd_5095893 : Nat := 2616642472882136028901921

theorem tailTrace_5095893 : CollatzResearch.WordTrace tailWord_5095893 prefixEnd_5095893 2616642472882136028901921 := by
  unfold tailWord_5095893
  simp only [CollatzResearch.WordTrace]
  refine ⟨185862486927457445080652333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123908324618304963387101555 185862486927457445080652333)
  ·
    refine ⟨69698432597796541905244625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185862486927457445080652333 69698432597796541905244625)
    ·
      refine ⟨52273824448347406428933469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69698432597796541905244625 52273824448347406428933469)
      ·
        refine ⟨19602684168130277410850051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52273824448347406428933469 19602684168130277410850051)
        ·
          refine ⟨29404026252195416116275077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19602684168130277410850051 29404026252195416116275077)
          ·
            refine ⟨5513254922286640521801577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29404026252195416116275077 5513254922286640521801577)
            ·
              refine ⟨4134941191714980391351183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513254922286640521801577 4134941191714980391351183)
              ·
                refine ⟨6202411787572470587026775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134941191714980391351183 6202411787572470587026775)
                ·
                  refine ⟨9303617681358705880540163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202411787572470587026775 9303617681358705880540163)
                  ·
                    refine ⟨13955426522038058820810245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9303617681358705880540163 13955426522038058820810245)
                    ·
                      refine ⟨2616642472882136028901921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13955426522038058820810245 2616642472882136028901921)
                      ·
                        rfl

theorem cell23_5095893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5095893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095893 prefixEnd_5095893 := by exact prefixLift 5095893
  have htrace : WordTrace (prefixWord ++ tailWord_5095893) baseStart_5095893 baseEnd_5095893 := by
    simpa [prefixWord, tailWord_5095893, baseEnd_5095893] using wordTrace_append hprefix tailTrace_5095893
  have hstable : (prefixWord ++ tailWord_5095893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095893).length < 2 ^ (prefixWord ++ tailWord_5095893).sum := by decide
  have hdescent : baseEnd_5095893 < baseStart_5095893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5095969 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5095969 : Nat := 118140960795 + 5095969 * 2 ^ 59
def prefixEnd_5095969 : Nat := 4983230072969 + 3 ^ 40 * 5095969 * 2
def baseEnd_5095969 : Nat := 2616681497411877731551571

theorem tailTrace_5095969 : CollatzResearch.WordTrace tailWord_5095969 prefixEnd_5095969 2616681497411877731551571 := by
  unfold tailWord_5095969
  simp only [CollatzResearch.WordTrace]
  refine ⟨185865258875182110060418961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123910172583454740040279307 185865258875182110060418961)
  ·
    refine ⟨139398944156386582545314221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185865258875182110060418961 139398944156386582545314221)
    ·
      refine ⟨52274604058644968454492833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139398944156386582545314221 52274604058644968454492833)
      ·
        refine ⟨39205953043983726340869625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52274604058644968454492833 39205953043983726340869625)
        ·
          refine ⟨29404464782987794755652219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39205953043983726340869625 29404464782987794755652219)
          ·
            refine ⟨44106697174481692133478329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29404464782987794755652219 44106697174481692133478329)
            ·
              refine ⟨33080022880861269100108747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44106697174481692133478329 33080022880861269100108747)
              ·
                refine ⟨49620034321291903650163121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33080022880861269100108747 49620034321291903650163121)
                ·
                  refine ⟨37215025740968927737622341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49620034321291903650163121 37215025740968927737622341)
                  ·
                    refine ⟨6977817326431673950804189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37215025740968927737622341 6977817326431673950804189)
                    ·
                      refine ⟨2616681497411877731551571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6977817326431673950804189 2616681497411877731551571)
                      ·
                        rfl

theorem cell23_5095969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5095969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5095969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5095969 prefixEnd_5095969 := by exact prefixLift 5095969
  have htrace : WordTrace (prefixWord ++ tailWord_5095969) baseStart_5095969 baseEnd_5095969 := by
    simpa [prefixWord, tailWord_5095969, baseEnd_5095969] using wordTrace_append hprefix tailTrace_5095969
  have hstable : (prefixWord ++ tailWord_5095969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5095969).length < 2 ^ (prefixWord ++ tailWord_5095969).sum := by decide
  have hdescent : baseEnd_5095969 < baseStart_5095969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5095969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096039 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5096039 : Nat := 118140960795 + 5096039 * 2 ^ 59
def prefixEnd_5096039 : Nat := 4983230072969 + 3 ^ 40 * 5096039 * 2
def baseEnd_5096039 : Nat := 2616717441057692457676249

theorem tailTrace_5096039 : CollatzResearch.WordTrace tailWord_5096039 prefixEnd_5096039 2616717441057692457676249 := by
  unfold tailWord_5096039
  simp only [CollatzResearch.WordTrace]
  refine ⟨185867811984928512015467171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123911874656619008010311447 185867811984928512015467171)
  ·
    refine ⟨278801717977392768023200757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185867811984928512015467171 278801717977392768023200757)
    ·
      refine ⟨26137661060380572002175071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278801717977392768023200757 26137661060380572002175071)
      ·
        refine ⟨39206491590570858003262607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26137661060380572002175071 39206491590570858003262607)
        ·
          refine ⟨58809737385856287004893911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39206491590570858003262607 58809737385856287004893911)
          ·
            refine ⟨88214606078784430507340867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58809737385856287004893911 88214606078784430507340867)
            ·
              refine ⟨132321909118176645761011301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88214606078784430507340867 132321909118176645761011301)
              ·
                refine ⟨24810357959658121080189619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132321909118176645761011301 24810357959658121080189619)
                ·
                  refine ⟨37215536939487181620284429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24810357959658121080189619 37215536939487181620284429)
                  ·
                    refine ⟨13955826352307693107606661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37215536939487181620284429 13955826352307693107606661)
                    ·
                      refine ⟨2616717441057692457676249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13955826352307693107606661 2616717441057692457676249)
                      ·
                        rfl

theorem cell23_5096039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5096039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096039 prefixEnd_5096039 := by exact prefixLift 5096039
  have htrace : WordTrace (prefixWord ++ tailWord_5096039) baseStart_5096039 baseEnd_5096039 := by
    simpa [prefixWord, tailWord_5096039, baseEnd_5096039] using wordTrace_append hprefix tailTrace_5096039
  have hstable : (prefixWord ++ tailWord_5096039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096039).length < 2 ^ (prefixWord ++ tailWord_5096039).sum := by decide
  have hdescent : baseEnd_5096039 < baseStart_5096039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096069 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_5096069 : Nat := 118140960795 + 5096069 * 2 ^ 59
def prefixEnd_5096069 : Nat := 4983230072969 + 3 ^ 40 * 5096069 * 2
def baseEnd_5096069 : Nat := 2616732845477327340301111

theorem tailTrace_5096069 : CollatzResearch.WordTrace tailWord_5096069 prefixEnd_5096069 2616732845477327340301111 := by
  unfold tailWord_5096069
  simp only [CollatzResearch.WordTrace]
  refine ⟨185868906174819827139059261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123912604116546551426039507 185868906174819827139059261)
  ·
    refine ⟨69700839815557435177147223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185868906174819827139059261 69700839815557435177147223)
    ·
      refine ⟨104551259723336152765720835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69700839815557435177147223 104551259723336152765720835)
      ·
        refine ⟨156826889585004229148581253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104551259723336152765720835 156826889585004229148581253)
        ·
          refine ⟨29405041797188292965358985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156826889585004229148581253 29405041797188292965358985)
          ·
            refine ⟨22053781347891219724019239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29405041797188292965358985 22053781347891219724019239)
            ·
              refine ⟨33080672021836829586028859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22053781347891219724019239 33080672021836829586028859)
              ·
                refine ⟨49621008032755244379043289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33080672021836829586028859 49621008032755244379043289)
                ·
                  refine ⟨37215756024566433284282467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49621008032755244379043289 37215756024566433284282467)
                  ·
                    refine ⟨55823634036849649926423701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37215756024566433284282467 55823634036849649926423701)
                    ·
                      refine ⟨2616732845477327340301111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55823634036849649926423701 2616732845477327340301111)
                      ·
                        rfl

theorem cell23_5096069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_5096069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096069 prefixEnd_5096069 := by exact prefixLift 5096069
  have htrace : WordTrace (prefixWord ++ tailWord_5096069) baseStart_5096069 baseEnd_5096069 := by
    simpa [prefixWord, tailWord_5096069, baseEnd_5096069] using wordTrace_append hprefix tailTrace_5096069
  have hstable : (prefixWord ++ tailWord_5096069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096069).length < 2 ^ (prefixWord ++ tailWord_5096069).sum := by decide
  have hdescent : baseEnd_5096069 < baseStart_5096069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096117 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_5096117 : Nat := 118140960795 + 5096117 * 2 ^ 59
def prefixEnd_5096117 : Nat := 4983230072969 + 3 ^ 40 * 5096117 * 2
def baseEnd_5096117 : Nat := 872252497516247717500297

theorem tailTrace_5096117 : CollatzResearch.WordTrace tailWord_5096117 prefixEnd_5096117 872252497516247717500297 := by
  unfold tailWord_5096117
  simp only [CollatzResearch.WordTrace]
  refine ⟨185870656878645931336806605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123913771252430620891204403 185870656878645931336806605)
  ·
    refine ⟨69701496329492224251302477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185870656878645931336806605 69701496329492224251302477)
    ·
      refine ⟨26138061123559584094238429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69701496329492224251302477 26138061123559584094238429)
      ·
        refine ⟨9801772921334844035339411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26138061123559584094238429 9801772921334844035339411)
        ·
          refine ⟨14702659382002266053009117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801772921334844035339411 14702659382002266053009117)
          ·
            refine ⟨5513497268250849769878419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14702659382002266053009117 5513497268250849769878419)
            ·
              refine ⟨8270245902376274654817629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513497268250849769878419 8270245902376274654817629)
              ·
                refine ⟨3101342213391102995556611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8270245902376274654817629 3101342213391102995556611)
                ·
                  refine ⟨4652013320086654493334917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101342213391102995556611 4652013320086654493334917)
                  ·
                    refine ⟨872252497516247717500297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652013320086654493334917 872252497516247717500297)
                    ·
                      rfl

theorem cell23_5096117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_5096117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096117 prefixEnd_5096117 := by exact prefixLift 5096117
  have htrace : WordTrace (prefixWord ++ tailWord_5096117) baseStart_5096117 baseEnd_5096117 := by
    simpa [prefixWord, tailWord_5096117, baseEnd_5096117] using wordTrace_append hprefix tailTrace_5096117
  have hstable : (prefixWord ++ tailWord_5096117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096117).length < 2 ^ (prefixWord ++ tailWord_5096117).sum := by decide
  have hdescent : baseEnd_5096117 < baseStart_5096117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096134 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5096134 : Nat := 118140960795 + 5096134 * 2 ^ 59
def prefixEnd_5096134 : Nat := 4983230072969 + 3 ^ 40 * 5096134 * 2
def baseEnd_5096134 : Nat := 872255407239956528662771

theorem tailTrace_5096134 : CollatzResearch.WordTrace tailWord_5096134 prefixEnd_5096134 872255407239956528662771 := by
  unfold tailWord_5096134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808477403737010726255483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123914184613056228826783637 5808477403737010726255483)
  ·
    refine ⟨8712716105605516089383225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808477403737010726255483 8712716105605516089383225)
    ·
      refine ⟨6534537079204137067037419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712716105605516089383225 6534537079204137067037419)
      ·
        refine ⟨9801805618806205600556129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534537079204137067037419 9801805618806205600556129)
        ·
          refine ⟨7351354214104654200417097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801805618806205600556129 7351354214104654200417097)
          ·
            refine ⟨5513515660578490650312823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351354214104654200417097 5513515660578490650312823)
            ·
              refine ⟨8270273490867735975469235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513515660578490650312823 8270273490867735975469235)
              ·
                refine ⟨12405410236301603963203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270273490867735975469235 12405410236301603963203853)
                ·
                  refine ⟨4652028838613101486201445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12405410236301603963203853 4652028838613101486201445)
                  ·
                    refine ⟨872255407239956528662771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652028838613101486201445 872255407239956528662771)
                    ·
                      rfl

theorem cell23_5096134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5096134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096134 prefixEnd_5096134 := by exact prefixLift 5096134
  have htrace : WordTrace (prefixWord ++ tailWord_5096134) baseStart_5096134 baseEnd_5096134 := by
    simpa [prefixWord, tailWord_5096134, baseEnd_5096134] using wordTrace_append hprefix tailTrace_5096134
  have hstable : (prefixWord ++ tailWord_5096134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096134).length < 2 ^ (prefixWord ++ tailWord_5096134).sum := by decide
  have hdescent : baseEnd_5096134 < baseStart_5096134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096140 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5096140 : Nat := 118140960795 + 5096140 * 2 ^ 59
def prefixEnd_5096140 : Nat := 4983230072969 + 3 ^ 40 * 5096140 * 2
def baseEnd_5096140 : Nat := 2616769302603796562513285

theorem tailTrace_5096140 : CollatzResearch.WordTrace tailWord_5096140 prefixEnd_5096140 2616769302603796562513285 := by
  unfold tailWord_5096140
  simp only [CollatzResearch.WordTrace]
  refine ⟨92935747878781303132446937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123914330505041737509929249 92935747878781303132446937)
  ·
    refine ⟨69701810909085977349335203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92935747878781303132446937 69701810909085977349335203)
    ·
      refine ⟨104552716363628966024002805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69701810909085977349335203 104552716363628966024002805)
      ·
        refine ⟨9801817159090215564750263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104552716363628966024002805 9801817159090215564750263)
        ·
          refine ⟨14702725738635323347125395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801817159090215564750263 14702725738635323347125395)
          ·
            refine ⟨22054088607952985020688093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702725738635323347125395 22054088607952985020688093)
            ·
              refine ⟨8270283227982369382758035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22054088607952985020688093 8270283227982369382758035)
              ·
                refine ⟨12405424841973554074137053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270283227982369382758035 12405424841973554074137053)
                ·
                  refine ⟨4652034315740082777801395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12405424841973554074137053 4652034315740082777801395)
                  ·
                    refine ⟨6978051473610124166702093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652034315740082777801395 6978051473610124166702093)
                    ·
                      refine ⟨2616769302603796562513285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978051473610124166702093 2616769302603796562513285)
                      ·
                        rfl

theorem cell23_5096140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5096140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096140 prefixEnd_5096140 := by exact prefixLift 5096140
  have htrace : WordTrace (prefixWord ++ tailWord_5096140) baseStart_5096140 baseEnd_5096140 := by
    simpa [prefixWord, tailWord_5096140, baseEnd_5096140] using wordTrace_append hprefix tailTrace_5096140
  have hstable : (prefixWord ++ tailWord_5096140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096140).length < 2 ^ (prefixWord ++ tailWord_5096140).sum := by decide
  have hdescent : baseEnd_5096140 < baseStart_5096140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096163 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5096163 : Nat := 118140960795 + 5096163 * 2 ^ 59
def prefixEnd_5096163 : Nat := 4983230072969 + 3 ^ 40 * 5096163 * 2
def baseEnd_5096163 : Nat := 2616781112658849972525679

theorem tailTrace_5096163 : CollatzResearch.WordTrace tailWord_5096163 prefixEnd_5096163 2616781112658849972525679 := by
  unfold tailWord_5096163
  simp only [CollatzResearch.WordTrace]
  refine ⟨185872334636479281192981143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123914889757652854128654095 185872334636479281192981143)
  ·
    refine ⟨278808501954718921789471715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185872334636479281192981143 278808501954718921789471715)
    ·
      refine ⟨418212752932078382684207573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278808501954718921789471715 418212752932078382684207573)
      ·
        refine ⟨9801861396845587094161115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 418212752932078382684207573 9801861396845587094161115)
        ·
          refine ⟨14702792095268380641241673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801861396845587094161115 14702792095268380641241673)
          ·
            refine ⟨11027094071451285480931255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14702792095268380641241673 11027094071451285480931255)
            ·
              refine ⟨16540641107176928221396883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11027094071451285480931255 16540641107176928221396883)
              ·
                refine ⟨24810961660765392332095325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16540641107176928221396883 24810961660765392332095325)
                ·
                  refine ⟨9304110622787022124535747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24810961660765392332095325 9304110622787022124535747)
                  ·
                    refine ⟨13956165934180533186803621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9304110622787022124535747 13956165934180533186803621)
                    ·
                      refine ⟨2616781112658849972525679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13956165934180533186803621 2616781112658849972525679)
                      ·
                        rfl

theorem cell23_5096163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5096163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096163 prefixEnd_5096163 := by exact prefixLift 5096163
  have htrace : WordTrace (prefixWord ++ tailWord_5096163) baseStart_5096163 baseEnd_5096163 := by
    simpa [prefixWord, tailWord_5096163, baseEnd_5096163] using wordTrace_append hprefix tailTrace_5096163
  have hstable : (prefixWord ++ tailWord_5096163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096163).length < 2 ^ (prefixWord ++ tailWord_5096163).sum := by decide
  have hdescent : baseEnd_5096163 < baseStart_5096163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096169 : List Nat := [1, 2, 1, 1, 1, 2, 6, 9]
def baseStart_5096169 : Nat := 118140960795 + 5096169 * 2 ^ 59
def prefixEnd_5096169 : Nat := 4983230072969 + 3 ^ 40 * 5096169 * 2
def baseEnd_5096169 : Nat := 96917933094176924038913

theorem tailTrace_5096169 : CollatzResearch.WordTrace tailWord_5096169 prefixEnd_5096169 96917933094176924038913 := by
  unfold tailWord_5096169
  simp only [CollatzResearch.WordTrace]
  refine ⟨185872553474457544217699561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123915035649638362811799707 185872553474457544217699561)
  ·
    refine ⟨139404415105843158163274671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185872553474457544217699561 139404415105843158163274671)
    ·
      refine ⟨209106622658764737244912007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139404415105843158163274671 209106622658764737244912007)
      ·
        refine ⟨313659933988147105867368011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209106622658764737244912007 313659933988147105867368011)
        ·
          refine ⟨470489900982220658801052017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313659933988147105867368011 470489900982220658801052017)
          ·
            refine ⟨352867425736665494100789013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470489900982220658801052017 352867425736665494100789013)
            ·
              refine ⟨16540660581406195035974485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 352867425736665494100789013 16540660581406195035974485)
              ·
                refine ⟨96917933094176924038913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16540660581406195035974485 96917933094176924038913)
                ·
                  rfl

theorem cell23_5096169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 9].length) (baseStart_5096169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096169 prefixEnd_5096169 := by exact prefixLift 5096169
  have htrace : WordTrace (prefixWord ++ tailWord_5096169) baseStart_5096169 baseEnd_5096169 := by
    simpa [prefixWord, tailWord_5096169, baseEnd_5096169] using wordTrace_append hprefix tailTrace_5096169
  have hstable : (prefixWord ++ tailWord_5096169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096169).length < 2 ^ (prefixWord ++ tailWord_5096169).sum := by decide
  have hdescent : baseEnd_5096169 < baseStart_5096169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096176 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_5096176 : Nat := 118140960795 + 5096176 * 2 ^ 59
def prefixEnd_5096176 : Nat := 4983230072969 + 3 ^ 40 * 5096176 * 2
def baseEnd_5096176 : Nat := 2616787787907358421663119

theorem tailTrace_5096176 : CollatzResearch.WordTrace tailWord_5096176 prefixEnd_5096176 2616787787907358421663119 := by
  unfold tailWord_5096176
  simp only [CollatzResearch.WordTrace]
  refine ⟨92936404392716092206602191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123915205856954789608802921 92936404392716092206602191)
  ·
    refine ⟨139404606589074138309903287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92936404392716092206602191 139404606589074138309903287)
    ·
      refine ⟨209106909883611207464854931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139404606589074138309903287 209106909883611207464854931)
      ·
        refine ⟨313660364825416811197282397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209106909883611207464854931 313660364825416811197282397)
        ·
          refine ⟨117622636809531304198980899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313660364825416811197282397 117622636809531304198980899)
          ·
            refine ⟨176433955214296956298471349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117622636809531304198980899 176433955214296956298471349)
            ·
              refine ⟨16540683301340339652981689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176433955214296956298471349 16540683301340339652981689)
              ·
                refine ⟨12405512476005254739736267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16540683301340339652981689 12405512476005254739736267)
                ·
                  refine ⟨18608268714007882109604401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12405512476005254739736267 18608268714007882109604401)
                  ·
                    refine ⟨13956201535505911582203301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18608268714007882109604401 13956201535505911582203301)
                    ·
                      refine ⟨2616787787907358421663119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13956201535505911582203301 2616787787907358421663119)
                      ·
                        rfl

theorem cell23_5096176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_5096176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096176 prefixEnd_5096176 := by exact prefixLift 5096176
  have htrace : WordTrace (prefixWord ++ tailWord_5096176) baseStart_5096176 baseEnd_5096176 := by
    simpa [prefixWord, tailWord_5096176, baseEnd_5096176] using wordTrace_append hprefix tailTrace_5096176
  have hstable : (prefixWord ++ tailWord_5096176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096176).length < 2 ^ (prefixWord ++ tailWord_5096176).sum := by decide
  have hdescent : baseEnd_5096176 < baseStart_5096176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096190 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_5096190 : Nat := 118140960795 + 5096190 * 2 ^ 59
def prefixEnd_5096190 : Nat := 4983230072969 + 3 ^ 40 * 5096190 * 2
def baseEnd_5096190 : Nat := 872264992212173788962685

theorem tailTrace_5096190 : CollatzResearch.WordTrace tailWord_5096190 prefixEnd_5096190 872264992212173788962685 := by
  unfold tailWord_5096190
  simp only [CollatzResearch.WordTrace]
  refine ⟨23234164925922683100526753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123915546271587643202809349 23234164925922683100526753)
  ·
    refine ⟨17425623694442012325395065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23234164925922683100526753 17425623694442012325395065)
    ·
      refine ⟨13069217770831509244046299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17425623694442012325395065 13069217770831509244046299)
      ·
        refine ⟨19603826656247263866069449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069217770831509244046299 19603826656247263866069449)
        ·
          refine ⟨14702869992185447899552087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19603826656247263866069449 14702869992185447899552087)
          ·
            refine ⟨22054304988278171849328131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702869992185447899552087 22054304988278171849328131)
            ·
              refine ⟨33081457482417257773992197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22054304988278171849328131 33081457482417257773992197)
              ·
                refine ⟨6202773277953235832623537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33081457482417257773992197 6202773277953235832623537)
                ·
                  refine ⟨4652079958464926874467653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6202773277953235832623537 4652079958464926874467653)
                  ·
                    refine ⟨872264992212173788962685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652079958464926874467653 872264992212173788962685)
                    ·
                      rfl

theorem cell23_5096190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_5096190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096190 prefixEnd_5096190 := by exact prefixLift 5096190
  have htrace : WordTrace (prefixWord ++ tailWord_5096190) baseStart_5096190 baseEnd_5096190 := by
    simpa [prefixWord, tailWord_5096190, baseEnd_5096190] using wordTrace_append hprefix tailTrace_5096190
  have hstable : (prefixWord ++ tailWord_5096190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096190).length < 2 ^ (prefixWord ++ tailWord_5096190).sum := by decide
  have hdescent : baseEnd_5096190 < baseStart_5096190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096213 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_5096213 : Nat := 118140960795 + 5096213 * 2 ^ 59
def prefixEnd_5096213 : Nat := 4983230072969 + 3 ^ 40 * 5096213 * 2
def baseEnd_5096213 : Nat := 2616806786691574776900449

theorem tailTrace_5096213 : CollatzResearch.WordTrace tailWord_5096213 prefixEnd_5096213 2616806786691574776900449 := by
  unfold tailWord_5096213
  simp only [CollatzResearch.WordTrace]
  refine ⟨185874158286298139732301293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123916105524198759821534195 185874158286298139732301293)
  ·
    refine ⟨69702809357361802399612985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185874158286298139732301293 69702809357361802399612985)
    ·
      refine ⟨52277107018021351799709739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69702809357361802399612985 52277107018021351799709739)
      ·
        refine ⟨78415660527032027699564609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52277107018021351799709739 78415660527032027699564609)
        ·
          refine ⟨58811745395274020774673457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78415660527032027699564609 58811745395274020774673457)
          ·
            refine ⟨44108809046455515581005093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58811745395274020774673457 44108809046455515581005093)
            ·
              refine ⟨8270401696210409171438455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44108809046455515581005093 8270401696210409171438455)
              ·
                refine ⟨12405602544315613757157683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270401696210409171438455 12405602544315613757157683)
                ·
                  refine ⟨18608403816473420635736525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12405602544315613757157683 18608403816473420635736525)
                  ·
                    refine ⟨6978151431177532738401197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18608403816473420635736525 6978151431177532738401197)
                    ·
                      refine ⟨2616806786691574776900449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978151431177532738401197 2616806786691574776900449)
                      ·
                        rfl

theorem cell23_5096213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_5096213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096213 prefixEnd_5096213 := by exact prefixLift 5096213
  have htrace : WordTrace (prefixWord ++ tailWord_5096213) baseStart_5096213 baseEnd_5096213 := by
    simpa [prefixWord, tailWord_5096213, baseEnd_5096213] using wordTrace_append hprefix tailTrace_5096213
  have hstable : (prefixWord ++ tailWord_5096213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096213).length < 2 ^ (prefixWord ++ tailWord_5096213).sum := by decide
  have hdescent : baseEnd_5096213 < baseStart_5096213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_5096219 : Nat := 118140960795 + 5096219 * 2 ^ 59
def prefixEnd_5096219 : Nat := 4983230072969 + 3 ^ 40 * 5096219 * 2
def baseEnd_5096219 : Nat := 2616809867575501753425421

theorem tailTrace_5096219 : CollatzResearch.WordTrace tailWord_5096219 prefixEnd_5096219 2616809867575501753425421 := by
  unfold tailWord_5096219
  simp only [CollatzResearch.WordTrace]
  refine ⟨185874377124276402757019711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123916251416184268504679807 185874377124276402757019711)
  ·
    refine ⟨278811565686414604135529567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185874377124276402757019711 278811565686414604135529567)
    ·
      refine ⟨418217348529621906203294351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278811565686414604135529567 418217348529621906203294351)
      ·
        refine ⟨627326022794432859304941527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418217348529621906203294351 627326022794432859304941527)
        ·
          refine ⟨940989034191649288957412291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627326022794432859304941527 940989034191649288957412291)
          ·
            refine ⟨1411483551287473933436118437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940989034191649288957412291 1411483551287473933436118437)
            ·
              refine ⟨264653165866401362519272207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1411483551287473933436118437 264653165866401362519272207)
              ·
                refine ⟨396979748799602043778908311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264653165866401362519272207 396979748799602043778908311)
                ·
                  refine ⟨595469623199403065668362467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396979748799602043778908311 595469623199403065668362467)
                  ·
                    refine ⟨893204434799104598502543701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595469623199403065668362467 893204434799104598502543701)
                    ·
                      refine ⟨2616809867575501753425421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 893204434799104598502543701 2616809867575501753425421)
                      ·
                        rfl

theorem cell23_5096219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_5096219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096219 prefixEnd_5096219 := by exact prefixLift 5096219
  have htrace : WordTrace (prefixWord ++ tailWord_5096219) baseStart_5096219 baseEnd_5096219 := by
    simpa [prefixWord, tailWord_5096219, baseEnd_5096219] using wordTrace_append hprefix tailTrace_5096219
  have hstable : (prefixWord ++ tailWord_5096219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096219).length < 2 ^ (prefixWord ++ tailWord_5096219).sum := by decide
  have hdescent : baseEnd_5096219 < baseStart_5096219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096256 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_5096256 : Nat := 118140960795 + 5096256 * 2 ^ 59
def prefixEnd_5096256 : Nat := 4983230072969 + 3 ^ 40 * 5096256 * 2
def baseEnd_5096256 : Nat := 2616828866359718108662751

theorem tailTrace_5096256 : CollatzResearch.WordTrace tailWord_5096256 prefixEnd_5096256 2616828866359718108662751 := by
  unfold tailWord_5096256
  simp only [CollatzResearch.WordTrace]
  refine ⟨92937863312571179038058311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123917151083428238717411081 92937863312571179038058311)
  ·
    refine ⟨139406794968856768557087467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92937863312571179038058311 139406794968856768557087467)
    ·
      refine ⟨209110192453285152835631201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139406794968856768557087467 209110192453285152835631201)
      ·
        refine ⟨156832644339963864626723401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209110192453285152835631201 156832644339963864626723401)
        ·
          refine ⟨117624483254972898470042551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156832644339963864626723401 117624483254972898470042551)
          ·
            refine ⟨176436724882459347705063827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117624483254972898470042551 176436724882459347705063827)
            ·
              refine ⟨264655087323689021557595741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176436724882459347705063827 264655087323689021557595741)
              ·
                refine ⟨99245657746383383084098403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264655087323689021557595741 99245657746383383084098403)
                ·
                  refine ⟨148868486619575074626147605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99245657746383383084098403 148868486619575074626147605)
                  ·
                    refine ⟨6978210310292581623100669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148868486619575074626147605 6978210310292581623100669)
                    ·
                      refine ⟨2616828866359718108662751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978210310292581623100669 2616828866359718108662751)
                      ·
                        rfl

theorem cell23_5096256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_5096256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096256 prefixEnd_5096256 := by exact prefixLift 5096256
  have htrace : WordTrace (prefixWord ++ tailWord_5096256) baseStart_5096256 baseEnd_5096256 := by
    simpa [prefixWord, tailWord_5096256, baseEnd_5096256] using wordTrace_append hprefix tailTrace_5096256
  have hstable : (prefixWord ++ tailWord_5096256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096256).length < 2 ^ (prefixWord ++ tailWord_5096256).sum := by decide
  have hdescent : baseEnd_5096256 < baseStart_5096256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096266 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_5096266 : Nat := 118140960795 + 5096266 * 2 ^ 59
def prefixEnd_5096266 : Nat := 4983230072969 + 3 ^ 40 * 5096266 * 2
def baseEnd_5096266 : Nat := 2616834001166263069537705

theorem tailTrace_5096266 : CollatzResearch.WordTrace tailWord_5096266 prefixEnd_5096266 2616834001166263069537705 := by
  unfold tailWord_5096266
  simp only [CollatzResearch.WordTrace]
  refine ⟨46469022838776532445995163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123917394236737419855987101 46469022838776532445995163)
  ·
    refine ⟨69703534258164798668992745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46469022838776532445995163 69703534258164798668992745)
    ·
      refine ⟨52277650693623599001744559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69703534258164798668992745 52277650693623599001744559)
      ·
        refine ⟨78416476040435398502616839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52277650693623599001744559 78416476040435398502616839)
        ·
          refine ⟨117624714060653097753925259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78416476040435398502616839 117624714060653097753925259)
          ·
            refine ⟨176437071090979646630887889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117624714060653097753925259 176437071090979646630887889)
            ·
              refine ⟨132327803318234734973165917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176437071090979646630887889 132327803318234734973165917)
              ·
                refine ⟨49622926244338025614937219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132327803318234734973165917 49622926244338025614937219)
                ·
                  refine ⟨74434389366507038422405829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49622926244338025614937219 74434389366507038422405829)
                  ·
                    refine ⟨13956448006220069704201093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74434389366507038422405829 13956448006220069704201093)
                    ·
                      refine ⟨2616834001166263069537705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13956448006220069704201093 2616834001166263069537705)
                      ·
                        rfl

theorem cell23_5096266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_5096266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096266 prefixEnd_5096266 := by exact prefixLift 5096266
  have htrace : WordTrace (prefixWord ++ tailWord_5096266) baseStart_5096266 baseEnd_5096266 := by
    simpa [prefixWord, tailWord_5096266, baseEnd_5096266] using wordTrace_append hprefix tailTrace_5096266
  have hstable : (prefixWord ++ tailWord_5096266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096266).length < 2 ^ (prefixWord ++ tailWord_5096266).sum := by decide
  have hdescent : baseEnd_5096266 < baseStart_5096266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096290 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5096290 : Nat := 118140960795 + 5096290 * 2 ^ 59
def prefixEnd_5096290 : Nat := 4983230072969 + 3 ^ 40 * 5096290 * 2
def baseEnd_5096290 : Nat := 2616846324701970975637595

theorem tailTrace_5096290 : CollatzResearch.WordTrace tailWord_5096290 prefixEnd_5096290 2616846324701970975637595 := by
  unfold tailWord_5096290
  simp only [CollatzResearch.WordTrace]
  refine ⟨46469241676754795470713581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123917977804679454588569549 46469241676754795470713581)
  ·
    refine ⟨17425965628783048301517593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46469241676754795470713581 17425965628783048301517593)
    ·
      refine ⟨13069474221587286226138195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17425965628783048301517593 13069474221587286226138195)
      ·
        refine ⟨19604211332380929339207293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069474221587286226138195 19604211332380929339207293)
        ·
          refine ⟨7351579249642848502202735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19604211332380929339207293 7351579249642848502202735)
          ·
            refine ⟨11027368874464272753304103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351579249642848502202735 11027368874464272753304103)
            ·
              refine ⟨16541053311696409129956155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11027368874464272753304103 16541053311696409129956155)
              ·
                refine ⟨24811579967544613694934233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16541053311696409129956155 24811579967544613694934233)
                ·
                  refine ⟨18608684975658460271200675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24811579967544613694934233 18608684975658460271200675)
                  ·
                    refine ⟨27913027463487690406801013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18608684975658460271200675 27913027463487690406801013)
                    ·
                      refine ⟨2616846324701970975637595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27913027463487690406801013 2616846324701970975637595)
                      ·
                        rfl

theorem cell23_5096290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5096290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096290 prefixEnd_5096290 := by exact prefixLift 5096290
  have htrace : WordTrace (prefixWord ++ tailWord_5096290) baseStart_5096290 baseEnd_5096290 := by
    simpa [prefixWord, tailWord_5096290, baseEnd_5096290] using wordTrace_append hprefix tailTrace_5096290
  have hstable : (prefixWord ++ tailWord_5096290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096290).length < 2 ^ (prefixWord ++ tailWord_5096290).sum := by decide
  have hdescent : baseEnd_5096290 < baseStart_5096290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096310 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_5096310 : Nat := 118140960795 + 5096310 * 2 ^ 59
def prefixEnd_5096310 : Nat := 4983230072969 + 3 ^ 40 * 5096310 * 2
def baseEnd_5096310 : Nat := 290761843812784544154167

theorem tailTrace_5096310 : CollatzResearch.WordTrace tailWord_5096310 prefixEnd_5096310 290761843812784544154167 := by
  unfold tailWord_5096310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617356010434170331161399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123918464111297816865721589 11617356010434170331161399)
  ·
    refine ⟨17426034015651255496742099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11617356010434170331161399 17426034015651255496742099)
    ·
      refine ⟨26139051023476883245113149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17426034015651255496742099 26139051023476883245113149)
      ·
        refine ⟨9802144133803831216917431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26139051023476883245113149 9802144133803831216917431)
        ·
          refine ⟨14703216200705746825376147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802144133803831216917431 14703216200705746825376147)
          ·
            refine ⟨22054824301058620238064221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703216200705746825376147 22054824301058620238064221)
            ·
              refine ⟨8270559112896982589274083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22054824301058620238064221 8270559112896982589274083)
              ·
                refine ⟨12405838669345473883911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270559112896982589274083 12405838669345473883911125)
                ·
                  refine ⟨290761843812784544154167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12405838669345473883911125 290761843812784544154167)
                  ·
                    rfl

theorem cell23_5096310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_5096310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096310 prefixEnd_5096310 := by exact prefixLift 5096310
  have htrace : WordTrace (prefixWord ++ tailWord_5096310) baseStart_5096310 baseEnd_5096310 := by
    simpa [prefixWord, tailWord_5096310, baseEnd_5096310] using wordTrace_append hprefix tailTrace_5096310
  have hstable : (prefixWord ++ tailWord_5096310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096310).length < 2 ^ (prefixWord ++ tailWord_5096310).sum := by decide
  have hdescent : baseEnd_5096310 < baseStart_5096310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096340 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5096340 : Nat := 118140960795 + 5096340 * 2 ^ 59
def prefixEnd_5096340 : Nat := 4983230072969 + 3 ^ 40 * 5096340 * 2
def baseEnd_5096340 : Nat := 872290666244898593337455

theorem tailTrace_5096340 : CollatzResearch.WordTrace tailWord_5096340 prefixEnd_5096340 872290666244898593337455 := by
  unfold tailWord_5096340
  simp only [CollatzResearch.WordTrace]
  refine ⟨92939395178419020211087237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123919193571225360281449649 92939395178419020211087237)
  ·
    refine ⟨17426136595953566289578857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92939395178419020211087237 17426136595953566289578857)
    ·
      refine ⟨13069602446965174717184143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17426136595953566289578857 13069602446965174717184143)
      ·
        refine ⟨19604403670447762075776215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069602446965174717184143 19604403670447762075776215)
        ·
          refine ⟨29406605505671643113664323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19604403670447762075776215 29406605505671643113664323)
          ·
            refine ⟨44109908258507464670496485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29406605505671643113664323 44109908258507464670496485)
            ·
              refine ⟨8270607798470149625718091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44109908258507464670496485 8270607798470149625718091)
              ·
                refine ⟨12405911697705224438577137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270607798470149625718091 12405911697705224438577137)
                ·
                  refine ⟨9304433773278918328932853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12405911697705224438577137 9304433773278918328932853)
                  ·
                    refine ⟨872290666244898593337455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9304433773278918328932853 872290666244898593337455)
                    ·
                      rfl

theorem cell23_5096340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5096340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096340 prefixEnd_5096340 := by exact prefixLift 5096340
  have htrace : WordTrace (prefixWord ++ tailWord_5096340) baseStart_5096340 baseEnd_5096340 := by
    simpa [prefixWord, tailWord_5096340, baseEnd_5096340] using wordTrace_append hprefix tailTrace_5096340
  have hstable : (prefixWord ++ tailWord_5096340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096340).length < 2 ^ (prefixWord ++ tailWord_5096340).sum := by decide
  have hdescent : baseEnd_5096340 < baseStart_5096340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096404 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_5096404 : Nat := 118140960795 + 5096404 * 2 ^ 59
def prefixEnd_5096404 : Nat := 4983230072969 + 3 ^ 40 * 5096404 * 2
def baseEnd_5096404 : Nat := 872301620498861176537357

theorem tailTrace_5096404 : CollatzResearch.WordTrace tailWord_5096404 prefixEnd_5096404 872301620498861176537357 := by
  unfold tailWord_5096404
  simp only [CollatzResearch.WordTrace]
  refine ⟨92940562314303089676252133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123920749752404119568336177 92940562314303089676252133)
  ·
    refine ⟨17426355433931829314297275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92940562314303089676252133 17426355433931829314297275)
    ·
      refine ⟨26139533150897743971445913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17426355433931829314297275 26139533150897743971445913)
      ·
        refine ⟨19604649863173307978584435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26139533150897743971445913 19604649863173307978584435)
        ·
          refine ⟨29406974794759961967876653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19604649863173307978584435 29406974794759961967876653)
          ·
            refine ⟨11027615548034985737953745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29406974794759961967876653 11027615548034985737953745)
            ·
              refine ⟨8270711661026239303465309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11027615548034985737953745 8270711661026239303465309)
              ·
                refine ⟨3101516872884839738799491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8270711661026239303465309 3101516872884839738799491)
                ·
                  refine ⟨4652275309327259608199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101516872884839738799491 4652275309327259608199237)
                  ·
                    refine ⟨872301620498861176537357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652275309327259608199237 872301620498861176537357)
                    ·
                      rfl

theorem cell23_5096404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_5096404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096404 prefixEnd_5096404 := by exact prefixLift 5096404
  have htrace : WordTrace (prefixWord ++ tailWord_5096404) baseStart_5096404 baseEnd_5096404 := by
    simpa [prefixWord, tailWord_5096404, baseEnd_5096404] using wordTrace_append hprefix tailTrace_5096404
  have hstable : (prefixWord ++ tailWord_5096404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096404).length < 2 ^ (prefixWord ++ tailWord_5096404).sum := by decide
  have hdescent : baseEnd_5096404 < baseStart_5096404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096434 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_5096434 : Nat := 118140960795 + 5096434 * 2 ^ 59
def prefixEnd_5096434 : Nat := 4983230072969 + 3 ^ 40 * 5096434 * 2
def baseEnd_5096434 : Nat := 290768918435135379137437

theorem tailTrace_5096434 : CollatzResearch.WordTrace tailWord_5096434 prefixEnd_5096434 290768918435135379137437 := by
  unfold tailWord_5096434
  simp only [CollatzResearch.WordTrace]
  refine ⟨46470554704624373619024089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123921479212331662984064237 46470554704624373619024089)
  ·
    refine ⟨34852916028468280214268067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46470554704624373619024089 34852916028468280214268067)
    ·
      refine ⟨52279374042702420321402101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34852916028468280214268067 52279374042702420321402101)
      ·
        refine ⟨4901191316503351905131447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52279374042702420321402101 4901191316503351905131447)
        ·
          refine ⟨7351786974755027857697171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901191316503351905131447 7351786974755027857697171)
          ·
            refine ⟨11027680462132541786545757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351786974755027857697171 11027680462132541786545757)
            ·
              refine ⟨4135380173299703169954659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11027680462132541786545757 4135380173299703169954659)
              ·
                refine ⟨6203070259949554754931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135380173299703169954659 6203070259949554754931989)
                ·
                  refine ⟨290768918435135379137437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6203070259949554754931989 290768918435135379137437)
                  ·
                    rfl

theorem cell23_5096434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_5096434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096434 prefixEnd_5096434 := by exact prefixLift 5096434
  have htrace : WordTrace (prefixWord ++ tailWord_5096434) baseStart_5096434 baseEnd_5096434 := by
    simpa [prefixWord, tailWord_5096434, baseEnd_5096434] using wordTrace_append hprefix tailTrace_5096434
  have hstable : (prefixWord ++ tailWord_5096434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096434).length < 2 ^ (prefixWord ++ tailWord_5096434).sum := by decide
  have hdescent : baseEnd_5096434 < baseStart_5096434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096453 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_5096453 : Nat := 118140960795 + 5096453 * 2 ^ 59
def prefixEnd_5096453 : Nat := 4983230072969 + 3 ^ 40 * 5096453 * 2
def baseEnd_5096453 : Nat := 2616930022048653837899345

theorem tailTrace_5096453 : CollatzResearch.WordTrace tailWord_5096453 prefixEnd_5096453 2616930022048653837899345 := by
  unfold tailWord_5096453
  simp only [CollatzResearch.WordTrace]
  refine ⟨185882911805428660721038013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123921941203619107147358675 185882911805428660721038013)
  ·
    refine ⟨69706091927035747770389255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185882911805428660721038013 69706091927035747770389255)
    ·
      refine ⟨104559137890553621655583883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69706091927035747770389255 104559137890553621655583883)
      ·
        refine ⟨156838706835830432483375825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104559137890553621655583883 156838706835830432483375825)
        ·
          refine ⟨117629030126872824362531869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156838706835830432483375825 117629030126872824362531869)
          ·
            refine ⟨44110886297577309135949451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117629030126872824362531869 44110886297577309135949451)
            ·
              refine ⟨66166329446365963703924177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44110886297577309135949451 66166329446365963703924177)
              ·
                refine ⟨49624747084774472777943133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66166329446365963703924177 49624747084774472777943133)
                ·
                  refine ⟨18609280156790427291728675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49624747084774472777943133 18609280156790427291728675)
                  ·
                    refine ⟨27913920235185640937593013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18609280156790427291728675 27913920235185640937593013)
                    ·
                      refine ⟨2616930022048653837899345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27913920235185640937593013 2616930022048653837899345)
                      ·
                        rfl

theorem cell23_5096453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_5096453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096453 prefixEnd_5096453 := by exact prefixLift 5096453
  have htrace : WordTrace (prefixWord ++ tailWord_5096453) baseStart_5096453 baseEnd_5096453 := by
    simpa [prefixWord, tailWord_5096453, baseEnd_5096453] using wordTrace_append hprefix tailTrace_5096453
  have hstable : (prefixWord ++ tailWord_5096453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096453).length < 2 ^ (prefixWord ++ tailWord_5096453).sum := by decide
  have hdescent : baseEnd_5096453 < baseStart_5096453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096460 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_5096460 : Nat := 118140960795 + 5096460 * 2 ^ 59
def prefixEnd_5096460 : Nat := 4983230072969 + 3 ^ 40 * 5096460 * 2
def baseEnd_5096460 : Nat := 872311205471078436837271

theorem tailTrace_5096460 : CollatzResearch.WordTrace tailWord_5096460 prefixEnd_5096460 872311205471078436837271 := by
  unfold tailWord_5096460
  simp only [CollatzResearch.WordTrace]
  refine ⟨92941583558201650458271417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123922111410935533944361889 92941583558201650458271417)
  ·
    refine ⟨69706187668651237843703563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92941583558201650458271417 69706187668651237843703563)
    ·
      refine ⟨104559281502976856765555345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69706187668651237843703563 104559281502976856765555345)
      ·
        refine ⟨78419461127232642574166509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104559281502976856765555345 78419461127232642574166509)
        ·
          refine ⟨29407297922712240965312441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78419461127232642574166509 29407297922712240965312441)
          ·
            refine ⟨22055473442034180723984331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29407297922712240965312441 22055473442034180723984331)
            ·
              refine ⟨33083210163051271085976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22055473442034180723984331 33083210163051271085976497)
              ·
                refine ⟨24812407622288453314482373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33083210163051271085976497 24812407622288453314482373)
                ·
                  refine ⟨4652326429179084996465445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24812407622288453314482373 4652326429179084996465445)
                  ·
                    refine ⟨872311205471078436837271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652326429179084996465445 872311205471078436837271)
                    ·
                      rfl

theorem cell23_5096460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_5096460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096460 prefixEnd_5096460 := by exact prefixLift 5096460
  have htrace : WordTrace (prefixWord ++ tailWord_5096460) baseStart_5096460 baseEnd_5096460 := by
    simpa [prefixWord, tailWord_5096460, baseEnd_5096460] using wordTrace_append hprefix tailTrace_5096460
  have hstable : (prefixWord ++ tailWord_5096460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096460).length < 2 ^ (prefixWord ++ tailWord_5096460).sum := by decide
  have hdescent : baseEnd_5096460 < baseStart_5096460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096487 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5096487 : Nat := 118140960795 + 5096487 * 2 ^ 59
def prefixEnd_5096487 : Nat := 4983230072969 + 3 ^ 40 * 5096487 * 2
def baseEnd_5096487 : Nat := 2616947480390906704874189

theorem tailTrace_5096487 : CollatzResearch.WordTrace tailWord_5096487 prefixEnd_5096487 2616947480390906704874189 := by
  unfold tailWord_5096487
  simp only [CollatzResearch.WordTrace]
  refine ⟨185884151887305484527775715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123922767924870323018517143 185884151887305484527775715)
  ·
    refine ⟨278826227830958226791663573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185884151887305484527775715 278826227830958226791663573)
    ·
      refine ⟨6534989714788083440429615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 278826227830958226791663573 6534989714788083440429615)
      ·
        refine ⟨9802484572182125160644423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534989714788083440429615 9802484572182125160644423)
        ·
          refine ⟨14703726858273187740966635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802484572182125160644423 14703726858273187740966635)
          ·
            refine ⟨22055590287409781611449953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703726858273187740966635 22055590287409781611449953)
            ·
              refine ⟨16541692715557336208587465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22055590287409781611449953 16541692715557336208587465)
              ·
                refine ⟨12406269536668002156440599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16541692715557336208587465 12406269536668002156440599)
                ·
                  refine ⟨18609404305002003234660899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12406269536668002156440599 18609404305002003234660899)
                  ·
                    refine ⟨27914106457503004851991349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18609404305002003234660899 27914106457503004851991349)
                    ·
                      refine ⟨2616947480390906704874189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27914106457503004851991349 2616947480390906704874189)
                      ·
                        rfl

theorem cell23_5096487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5096487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096487 prefixEnd_5096487 := by exact prefixLift 5096487
  have htrace : WordTrace (prefixWord ++ tailWord_5096487) baseStart_5096487 baseEnd_5096487 := by
    simpa [prefixWord, tailWord_5096487, baseEnd_5096487] using wordTrace_append hprefix tailTrace_5096487
  have hstable : (prefixWord ++ tailWord_5096487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096487).length < 2 ^ (prefixWord ++ tailWord_5096487).sum := by decide
  have hdescent : baseEnd_5096487 < baseStart_5096487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096504 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_5096504 : Nat := 118140960795 + 5096504 * 2 ^ 59
def prefixEnd_5096504 : Nat := 4983230072969 + 3 ^ 40 * 5096504 * 2
def baseEnd_5096504 : Nat := 2616956209562033138361611

theorem tailTrace_5096504 : CollatzResearch.WordTrace tailWord_5096504 prefixEnd_5096504 2616956209562033138361611 := by
  unfold tailWord_5096504
  simp only [CollatzResearch.WordTrace]
  refine ⟨92942385964121948215572283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123923181285495930954096377 92942385964121948215572283)
  ·
    refine ⟨139413578946182922323358425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92942385964121948215572283 139413578946182922323358425)
    ·
      refine ⟨104560184209637191742518819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139413578946182922323358425 104560184209637191742518819)
      ·
        refine ⟨156840276314455787613778229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104560184209637191742518819 156840276314455787613778229)
        ·
          refine ⟨14703775904480230088791709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156840276314455787613778229 14703775904480230088791709)
          ·
            refine ⟨5513915964180086283296891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14703775904480230088791709 5513915964180086283296891)
            ·
              refine ⟨8270873946270129424945337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513915964180086283296891 8270873946270129424945337)
              ·
                refine ⟨6203155459702597068709003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8270873946270129424945337 6203155459702597068709003)
                ·
                  refine ⟨9304733189553895603063505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203155459702597068709003 9304733189553895603063505)
                  ·
                    refine ⟨6978549892165421702297629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9304733189553895603063505 6978549892165421702297629)
                    ·
                      refine ⟨2616956209562033138361611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978549892165421702297629 2616956209562033138361611)
                      ·
                        rfl

theorem cell23_5096504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_5096504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096504 prefixEnd_5096504 := by exact prefixLift 5096504
  have htrace : WordTrace (prefixWord ++ tailWord_5096504) baseStart_5096504 baseEnd_5096504 := by
    simpa [prefixWord, tailWord_5096504, baseEnd_5096504] using wordTrace_append hprefix tailTrace_5096504
  have hstable : (prefixWord ++ tailWord_5096504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096504).length < 2 ^ (prefixWord ++ tailWord_5096504).sum := by decide
  have hdescent : baseEnd_5096504 < baseStart_5096504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096523 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_5096523 : Nat := 118140960795 + 5096523 * 2 ^ 59
def prefixEnd_5096523 : Nat := 4983230072969 + 3 ^ 40 * 5096523 * 2
def baseEnd_5096523 : Nat := 2616965965694468564024023

theorem tailTrace_5096523 : CollatzResearch.WordTrace tailWord_5096523 prefixEnd_5096523 2616965965694468564024023 := by
  unfold tailWord_5096523
  simp only [CollatzResearch.WordTrace]
  refine ⟨185885464915175062676086223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123923643276783375117390815 185885464915175062676086223)
  ·
    refine ⟨278828197372762594014129335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185885464915175062676086223 278828197372762594014129335)
    ·
      refine ⟨418242296059143891021194003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278828197372762594014129335 418242296059143891021194003)
      ·
        refine ⟨627363444088715836531791005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418242296059143891021194003 627363444088715836531791005)
        ·
          refine ⟨235261291533268438699421627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627363444088715836531791005 235261291533268438699421627)
          ·
            refine ⟨352891937299902658049132441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235261291533268438699421627 352891937299902658049132441)
            ·
              refine ⟨264668952974926993536849331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352891937299902658049132441 264668952974926993536849331)
              ·
                refine ⟨397003429462390490305273997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264668952974926993536849331 397003429462390490305273997)
                ·
                  refine ⟨148876286048396433864477749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397003429462390490305273997 148876286048396433864477749)
                  ·
                    refine ⟨13957151817037165674794789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148876286048396433864477749 13957151817037165674794789)
                    ·
                      refine ⟨2616965965694468564024023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13957151817037165674794789 2616965965694468564024023)
                      ·
                        rfl

theorem cell23_5096523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_5096523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096523 prefixEnd_5096523 := by exact prefixLift 5096523
  have htrace : WordTrace (prefixWord ++ tailWord_5096523) baseStart_5096523 baseEnd_5096523 := by
    simpa [prefixWord, tailWord_5096523, baseEnd_5096523] using wordTrace_append hprefix tailTrace_5096523
  have hstable : (prefixWord ++ tailWord_5096523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096523).length < 2 ^ (prefixWord ++ tailWord_5096523).sum := by decide
  have hdescent : baseEnd_5096523 < baseStart_5096523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096540 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5096540 : Nat := 118140960795 + 5096540 * 2 ^ 59
def prefixEnd_5096540 : Nat := 4983230072969 + 3 ^ 40 * 5096540 * 2
def baseEnd_5096540 : Nat := 2616974694865594997511445

theorem tailTrace_5096540 : CollatzResearch.WordTrace tailWord_5096540 prefixEnd_5096540 2616974694865594997511445 := by
  unfold tailWord_5096540
  simp only [CollatzResearch.WordTrace]
  refine ⟨92943042478056737289727537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123924056637408983052970049 92943042478056737289727537)
  ·
    refine ⟨69707281858542552967295653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92943042478056737289727537 69707281858542552967295653)
    ·
      refine ⟨13070115348476728681367935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69707281858542552967295653 13070115348476728681367935)
      ·
        refine ⟨19605173022715093022051903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13070115348476728681367935 19605173022715093022051903)
        ·
          refine ⟨29407759534072639533077855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19605173022715093022051903 29407759534072639533077855)
          ·
            refine ⟨44111639301108959299616783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29407759534072639533077855 44111639301108959299616783)
            ·
              refine ⟨66167458951663438949425175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44111639301108959299616783 66167458951663438949425175)
              ·
                refine ⟨99251188427495158424137763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66167458951663438949425175 99251188427495158424137763)
                ·
                  refine ⟨148876782641242737636206645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99251188427495158424137763 148876782641242737636206645)
                  ·
                    refine ⟨13957198372616506653394373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148876782641242737636206645 13957198372616506653394373)
                    ·
                      refine ⟨2616974694865594997511445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13957198372616506653394373 2616974694865594997511445)
                      ·
                        rfl

theorem cell23_5096540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5096540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096540 prefixEnd_5096540 := by exact prefixLift 5096540
  have htrace : WordTrace (prefixWord ++ tailWord_5096540) baseStart_5096540 baseEnd_5096540 := by
    simpa [prefixWord, tailWord_5096540, baseEnd_5096540] using wordTrace_append hprefix tailTrace_5096540
  have hstable : (prefixWord ++ tailWord_5096540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096540).length < 2 ^ (prefixWord ++ tailWord_5096540).sum := by decide
  have hdescent : baseEnd_5096540 < baseStart_5096540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096560 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_5096560 : Nat := 118140960795 + 5096560 * 2 ^ 59
def prefixEnd_5096560 : Nat := 4983230072969 + 3 ^ 40 * 5096560 * 2
def baseEnd_5096560 : Nat := 2616984964478684919261353

theorem tailTrace_5096560 : CollatzResearch.WordTrace tailWord_5096560 prefixEnd_5096560 2616984964478684919261353 := by
  unfold tailWord_5096560
  simp only [CollatzResearch.WordTrace]
  refine ⟨92943407208020508997591567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123924542944027345330122089 92943407208020508997591567)
  ·
    refine ⟨139415110812030763496387351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92943407208020508997591567 139415110812030763496387351)
    ·
      refine ⟨209122666218046145244581027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139415110812030763496387351 209122666218046145244581027)
      ·
        refine ⟨313683999327069217866871541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209122666218046145244581027 313683999327069217866871541)
        ·
          refine ⟨29407874936912739175019207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313683999327069217866871541 29407874936912739175019207)
          ·
            refine ⟨44111812405369108762528811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29407874936912739175019207 44111812405369108762528811)
            ·
              refine ⟨66167718608053663143793217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44111812405369108762528811 66167718608053663143793217)
              ·
                refine ⟨49625788956040247357844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66167718608053663143793217 49625788956040247357844913)
                ·
                  refine ⟨37219341717030185518383685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49625788956040247357844913 37219341717030185518383685)
                  ·
                    refine ⟨6978626571943159784696941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37219341717030185518383685 6978626571943159784696941)
                    ·
                      refine ⟨2616984964478684919261353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978626571943159784696941 2616984964478684919261353)
                      ·
                        rfl

theorem cell23_5096560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_5096560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096560 prefixEnd_5096560 := by exact prefixLift 5096560
  have htrace : WordTrace (prefixWord ++ tailWord_5096560) baseStart_5096560 baseEnd_5096560 := by
    simpa [prefixWord, tailWord_5096560, baseEnd_5096560] using wordTrace_append hprefix tailTrace_5096560
  have hstable : (prefixWord ++ tailWord_5096560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096560).length < 2 ^ (prefixWord ++ tailWord_5096560).sum := by decide
  have hdescent : baseEnd_5096560 < baseStart_5096560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096644 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5096644 : Nat := 118140960795 + 5096644 * 2 ^ 59
def prefixEnd_5096644 : Nat := 4983230072969 + 3 ^ 40 * 5096644 * 2
def baseEnd_5096644 : Nat := 872342698951220863536989

theorem tailTrace_5096644 : CollatzResearch.WordTrace tailWord_5096644 prefixEnd_5096644 872342698951220863536989 := by
  unfold tailWord_5096644
  simp only [CollatzResearch.WordTrace]
  refine ⟨92944939073868350170620493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123926585431824466894160657 92944939073868350170620493)
  ·
    refine ⟨34854352152700631313982685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92944939073868350170620493 34854352152700631313982685)
    ·
      refine ⟨13070382057262736742743507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34854352152700631313982685 13070382057262736742743507)
      ·
        refine ⟨19605573085894105114115261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13070382057262736742743507 19605573085894105114115261)
        ·
          refine ⟨7352089907210289417793223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19605573085894105114115261 7352089907210289417793223)
          ·
            refine ⟨11028134860815434126689835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7352089907210289417793223 11028134860815434126689835)
            ·
              refine ⟨16542202291223151190034753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11028134860815434126689835 16542202291223151190034753)
              ·
                refine ⟨12406651718417363392526065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16542202291223151190034753 12406651718417363392526065)
                ·
                  refine ⟨9304988788813022544394549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12406651718417363392526065 9304988788813022544394549)
                  ·
                    refine ⟨872342698951220863536989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9304988788813022544394549 872342698951220863536989)
                    ·
                      rfl

theorem cell23_5096644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5096644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096644 prefixEnd_5096644 := by exact prefixLift 5096644
  have htrace : WordTrace (prefixWord ++ tailWord_5096644) baseStart_5096644 baseEnd_5096644 := by
    simpa [prefixWord, tailWord_5096644, baseEnd_5096644] using wordTrace_append hprefix tailTrace_5096644
  have hstable : (prefixWord ++ tailWord_5096644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096644).length < 2 ^ (prefixWord ++ tailWord_5096644).sum := by decide
  have hdescent : baseEnd_5096644 < baseStart_5096644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_5096647 : Nat := 118140960795 + 5096647 * 2 ^ 59
def prefixEnd_5096647 : Nat := 4983230072969 + 3 ^ 40 * 5096647 * 2
def baseEnd_5096647 : Nat := 2617029637295626078873453

theorem tailTrace_5096647 : CollatzResearch.WordTrace tailWord_5096647 prefixEnd_5096647 2617029637295626078873453 := by
  unfold tailWord_5096647
  simp only [CollatzResearch.WordTrace]
  refine ⟨185889987566725831853600195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123926658377817221235733463 185889987566725831853600195)
  ·
    refine ⟨278834981350088747780400293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185889987566725831853600195 278834981350088747780400293)
    ·
      refine ⟨52281559003141640208825055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278834981350088747780400293 52281559003141640208825055)
      ·
        refine ⟨78422338504712460313237583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52281559003141640208825055 78422338504712460313237583)
        ·
          refine ⟨117633507757068690469856375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78422338504712460313237583 117633507757068690469856375)
          ·
            refine ⟨176450261635603035704784563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117633507757068690469856375 176450261635603035704784563)
            ·
              refine ⟨264675392453404553557176845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176450261635603035704784563 264675392453404553557176845)
              ·
                refine ⟨99253272170026707583941317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264675392453404553557176845 99253272170026707583941317)
                ·
                  refine ⟨18609988531880007671988997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99253272170026707583941317 18609988531880007671988997)
                  ·
                    refine ⟨3489372849727501438497937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18609988531880007671988997 3489372849727501438497937)
                    ·
                      refine ⟨2617029637295626078873453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489372849727501438497937 2617029637295626078873453)
                      ·
                        rfl

theorem cell23_5096647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_5096647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096647 prefixEnd_5096647 := by exact prefixLift 5096647
  have htrace : WordTrace (prefixWord ++ tailWord_5096647) baseStart_5096647 baseEnd_5096647 := by
    simpa [prefixWord, tailWord_5096647, baseEnd_5096647] using wordTrace_append hprefix tailTrace_5096647
  have hstable : (prefixWord ++ tailWord_5096647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096647).length < 2 ^ (prefixWord ++ tailWord_5096647).sum := by decide
  have hdescent : baseEnd_5096647 < baseStart_5096647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096684 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_5096684 : Nat := 118140960795 + 5096684 * 2 ^ 59
def prefixEnd_5096684 : Nat := 4983230072969 + 3 ^ 40 * 5096684 * 2
def baseEnd_5096684 : Nat := 2617048636079842434110783

theorem tailTrace_5096684 : CollatzResearch.WordTrace tailWord_5096684 prefixEnd_5096684 2617048636079842434110783 := by
  unfold tailWord_5096684
  simp only [CollatzResearch.WordTrace]
  refine ⟨92945668533795893586348553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123927558045061191448464737 92945668533795893586348553)
  ·
    refine ⟨69709251400346920189761415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92945668533795893586348553 69709251400346920189761415)
    ·
      refine ⟨104563877100520380284642123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69709251400346920189761415 104563877100520380284642123)
      ·
        refine ⟨156845815650780570426963185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104563877100520380284642123 156845815650780570426963185)
        ·
          refine ⟨117634361738085427820222389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156845815650780570426963185 117634361738085427820222389)
          ·
            refine ⟨11028221412945508858145849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117634361738085427820222389 11028221412945508858145849)
            ·
              refine ⟨8271166059709131643609387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11028221412945508858145849 8271166059709131643609387)
              ·
                refine ⟨12406749089563697465414081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8271166059709131643609387 12406749089563697465414081)
                ·
                  refine ⟨9305061817172773099060561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12406749089563697465414081 9305061817172773099060561)
                  ·
                    refine ⟨6978796362879579824295421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9305061817172773099060561 6978796362879579824295421)
                    ·
                      refine ⟨2617048636079842434110783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978796362879579824295421 2617048636079842434110783)
                      ·
                        rfl

theorem cell23_5096684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_5096684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096684 prefixEnd_5096684 := by exact prefixLift 5096684
  have htrace : WordTrace (prefixWord ++ tailWord_5096684) baseStart_5096684 baseEnd_5096684 := by
    simpa [prefixWord, tailWord_5096684, baseEnd_5096684] using wordTrace_append hprefix tailTrace_5096684
  have hstable : (prefixWord ++ tailWord_5096684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096684).length < 2 ^ (prefixWord ++ tailWord_5096684).sum := by decide
  have hdescent : baseEnd_5096684 < baseStart_5096684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096708 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5096708 : Nat := 118140960795 + 5096708 * 2 ^ 59
def prefixEnd_5096708 : Nat := 4983230072969 + 3 ^ 40 * 5096708 * 2
def baseEnd_5096708 : Nat := 872353653205183446736891

theorem tailTrace_5096708 : CollatzResearch.WordTrace tailWord_5096708 prefixEnd_5096708 872353653205183446736891 := by
  unfold tailWord_5096708
  simp only [CollatzResearch.WordTrace]
  refine ⟨92946106209752419635785389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123928141613003226181047185 92946106209752419635785389)
  ·
    refine ⟨34854789828657157363419521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92946106209752419635785389 34854789828657157363419521)
    ·
      refine ⟨26141092371492868022564641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34854789828657157363419521 26141092371492868022564641)
      ·
        refine ⟨19605819278619651016923481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26141092371492868022564641 19605819278619651016923481)
        ·
          refine ⟨14704364458964738262692611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19605819278619651016923481 14704364458964738262692611)
          ·
            refine ⟨22056546688447107394038917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14704364458964738262692611 22056546688447107394038917)
            ·
              refine ⟨4135602504083832636382297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22056546688447107394038917 4135602504083832636382297)
              ·
                refine ⟨3101701878062874477286723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4135602504083832636382297 3101701878062874477286723)
                ·
                  refine ⟨4652552817094311715930085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101701878062874477286723 4652552817094311715930085)
                  ·
                    refine ⟨872353653205183446736891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652552817094311715930085 872353653205183446736891)
                    ·
                      rfl

theorem cell23_5096708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5096708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096708 prefixEnd_5096708 := by exact prefixLift 5096708
  have htrace : WordTrace (prefixWord ++ tailWord_5096708) baseStart_5096708 baseEnd_5096708 := by
    simpa [prefixWord, tailWord_5096708, baseEnd_5096708] using wordTrace_append hprefix tailTrace_5096708
  have hstable : (prefixWord ++ tailWord_5096708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096708).length < 2 ^ (prefixWord ++ tailWord_5096708).sum := by decide
  have hdescent : baseEnd_5096708 < baseStart_5096708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096714 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_5096714 : Nat := 118140960795 + 5096714 * 2 ^ 59
def prefixEnd_5096714 : Nat := 4983230072969 + 3 ^ 40 * 5096714 * 2
def baseEnd_5096714 : Nat := 2617064040499477316735645

theorem tailTrace_5096714 : CollatzResearch.WordTrace tailWord_5096714 prefixEnd_5096714 2617064040499477316735645 := by
  unfold tailWord_5096714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46473107814370775574072299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123928287504988734864192797 46473107814370775574072299)
  ·
    refine ⟨69709661721556163361108449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46473107814370775574072299 69709661721556163361108449)
    ·
      refine ⟨52282246291167122520831337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69709661721556163361108449 52282246291167122520831337)
      ·
        refine ⟨39211684718375341890623503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52282246291167122520831337 39211684718375341890623503)
        ·
          refine ⟨58817527077563012835935255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39211684718375341890623503 58817527077563012835935255)
          ·
            refine ⟨88226290616344519253902883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58817527077563012835935255 88226290616344519253902883)
            ·
              refine ⟨132339435924516778880854325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88226290616344519253902883 132339435924516778880854325)
              ·
                refine ⟨12406822117923448020080093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132339435924516778880854325 12406822117923448020080093)
                ·
                  refine ⟨4652558294221293007530035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12406822117923448020080093 4652558294221293007530035)
                  ·
                    refine ⟨6978837441331939511295053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652558294221293007530035 6978837441331939511295053)
                    ·
                      refine ⟨2617064040499477316735645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978837441331939511295053 2617064040499477316735645)
                      ·
                        rfl

theorem cell23_5096714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_5096714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096714 prefixEnd_5096714 := by exact prefixLift 5096714
  have htrace : WordTrace (prefixWord ++ tailWord_5096714) baseStart_5096714 baseEnd_5096714 := by
    simpa [prefixWord, tailWord_5096714, baseEnd_5096714] using wordTrace_append hprefix tailTrace_5096714
  have hstable : (prefixWord ++ tailWord_5096714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096714).length < 2 ^ (prefixWord ++ tailWord_5096714).sum := by decide
  have hdescent : baseEnd_5096714 < baseStart_5096714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096741 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_5096741 : Nat := 118140960795 + 5096741 * 2 ^ 59
def prefixEnd_5096741 : Nat := 4983230072969 + 3 ^ 40 * 5096741 * 2
def baseEnd_5096741 : Nat := 2617077904477148711098021

theorem tailTrace_5096741 : CollatzResearch.WordTrace tailWord_5096741 prefixEnd_5096741 2617077904477148711098021 := by
  unfold tailWord_5096741
  simp only [CollatzResearch.WordTrace]
  refine ⟨185893416028385285907522077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123928944018923523938348051 185893416028385285907522077)
  ·
    refine ⟨69710031010644482215320779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185893416028385285907522077 69710031010644482215320779)
    ·
      refine ⟨104565046515966723322981169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69710031010644482215320779 104565046515966723322981169)
      ·
        refine ⟨78423784886975042492235877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104565046515966723322981169 78423784886975042492235877)
        ·
          refine ⟨14704459666307820467294227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78423784886975042492235877 14704459666307820467294227)
          ·
            refine ⟨22056689499461730700941341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14704459666307820467294227 22056689499461730700941341)
            ·
              refine ⟨8271258562298149012853003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22056689499461730700941341 8271258562298149012853003)
              ·
                refine ⟨12406887843447223519279505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8271258562298149012853003 12406887843447223519279505)
                ·
                  refine ⟨9305165882585417639459629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12406887843447223519279505 9305165882585417639459629)
                  ·
                    refine ⟨3489437205969531614797361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9305165882585417639459629 3489437205969531614797361)
                    ·
                      refine ⟨2617077904477148711098021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489437205969531614797361 2617077904477148711098021)
                      ·
                        rfl

theorem cell23_5096741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_5096741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096741 prefixEnd_5096741 := by exact prefixLift 5096741
  have htrace : WordTrace (prefixWord ++ tailWord_5096741) baseStart_5096741 baseEnd_5096741 := by
    simpa [prefixWord, tailWord_5096741, baseEnd_5096741] using wordTrace_append hprefix tailTrace_5096741
  have hstable : (prefixWord ++ tailWord_5096741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096741).length < 2 ^ (prefixWord ++ tailWord_5096741).sum := by decide
  have hdescent : baseEnd_5096741 < baseStart_5096741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096764 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_5096764 : Nat := 118140960795 + 5096764 * 2 ^ 59
def prefixEnd_5096764 : Nat := 4983230072969 + 3 ^ 40 * 5096764 * 2
def baseEnd_5096764 : Nat := 872363238177400707036805

theorem tailTrace_5096764 : CollatzResearch.WordTrace tailWord_5096764 prefixEnd_5096764 872363238177400707036805 := by
  unfold tailWord_5096764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92947127453650980417804673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123929503271534640557072897 92947127453650980417804673)
  ·
    refine ⟨69710345590238235313353505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92947127453650980417804673 69710345590238235313353505)
    ·
      refine ⟨52282759192678676485015129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69710345590238235313353505 52282759192678676485015129)
      ·
        refine ⟨39212069394509007363761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52282759192678676485015129 39212069394509007363761347)
        ·
          refine ⟨58818104091763511045642021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39212069394509007363761347 58818104091763511045642021)
          ·
            refine ⟨11028394517205658321057879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58818104091763511045642021 11028394517205658321057879)
            ·
              refine ⟨16542591775808487481586819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11028394517205658321057879 16542591775808487481586819)
              ·
                refine ⟨24813887663712731222380229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16542591775808487481586819 24813887663712731222380229)
                ·
                  refine ⟨4652603936946137104196293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24813887663712731222380229 4652603936946137104196293)
                  ·
                    refine ⟨872363238177400707036805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652603936946137104196293 872363238177400707036805)
                    ·
                      rfl

theorem cell23_5096764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_5096764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096764 prefixEnd_5096764 := by exact prefixLift 5096764
  have htrace : WordTrace (prefixWord ++ tailWord_5096764) baseStart_5096764 baseEnd_5096764 := by
    simpa [prefixWord, tailWord_5096764, baseEnd_5096764] using wordTrace_append hprefix tailTrace_5096764
  have hstable : (prefixWord ++ tailWord_5096764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096764).length < 2 ^ (prefixWord ++ tailWord_5096764).sum := by decide
  have hdescent : baseEnd_5096764 < baseStart_5096764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096791 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_5096791 : Nat := 118140960795 + 5096791 * 2 ^ 59
def prefixEnd_5096791 : Nat := 4983230072969 + 3 ^ 40 * 5096791 * 2
def baseEnd_5096791 : Nat := 2617103578509873515472791

theorem tailTrace_5096791 : CollatzResearch.WordTrace tailWord_5096791 prefixEnd_5096791 2617103578509873515472791 := by
  unfold tailWord_5096791
  simp only [CollatzResearch.WordTrace]
  refine ⟨185895239678204144446842227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123930159785469429631228151 185895239678204144446842227)
  ·
    refine ⟨278842859517306216670263341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185895239678204144446842227 278842859517306216670263341)
    ·
      refine ⟨104566072318989831251348753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278842859517306216670263341 104566072318989831251348753)
      ·
        refine ⟨78424554239242373438511565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104566072318989831251348753 78424554239242373438511565)
        ·
          refine ⟨29409207839715890039441837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78424554239242373438511565 29409207839715890039441837)
          ·
            refine ⟨11028452939893458764790689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29409207839715890039441837 11028452939893458764790689)
            ·
              refine ⟨8271339704920094073593017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11028452939893458764790689 8271339704920094073593017)
              ·
                refine ⟨6203504778690070555194763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8271339704920094073593017 6203504778690070555194763)
                ·
                  refine ⟨9305257168035105832792145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203504778690070555194763 9305257168035105832792145)
                  ·
                    refine ⟨6978942876026329374594109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9305257168035105832792145 6978942876026329374594109)
                    ·
                      refine ⟨2617103578509873515472791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6978942876026329374594109 2617103578509873515472791)
                      ·
                        rfl

theorem cell23_5096791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_5096791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096791 prefixEnd_5096791 := by exact prefixLift 5096791
  have htrace : WordTrace (prefixWord ++ tailWord_5096791) baseStart_5096791 baseEnd_5096791 := by
    simpa [prefixWord, tailWord_5096791, baseEnd_5096791] using wordTrace_append hprefix tailTrace_5096791
  have hstable : (prefixWord ++ tailWord_5096791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096791).length < 2 ^ (prefixWord ++ tailWord_5096791).sum := by decide
  have hdescent : baseEnd_5096791 < baseStart_5096791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096827 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_5096827 : Nat := 118140960795 + 5096827 * 2 ^ 59
def prefixEnd_5096827 : Nat := 4983230072969 + 3 ^ 40 * 5096827 * 2
def baseEnd_5096827 : Nat := 2617122063813435374622625

theorem tailTrace_5096827 : CollatzResearch.WordTrace tailWord_5096827 prefixEnd_5096827 2617122063813435374622625 := by
  unfold tailWord_5096827
  simp only [CollatzResearch.WordTrace]
  refine ⟨185896552706073722595152735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123931035137382481730101823 185896552706073722595152735)
  ·
    refine ⟨278844829059110583892729103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185896552706073722595152735 278844829059110583892729103)
    ·
      refine ⟨418267243588665875839093655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278844829059110583892729103 418267243588665875839093655)
      ·
        refine ⟨627400865382998813758640483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418267243588665875839093655 627400865382998813758640483)
        ·
          refine ⟨941101298074498220637960725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627400865382998813758640483 941101298074498220637960725)
          ·
            refine ⟨44114123347242104092404409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 941101298074498220637960725 44114123347242104092404409)
            ·
              refine ⟨33085592510431578069303307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44114123347242104092404409 33085592510431578069303307)
              ·
                refine ⟨49628388765647367103954961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33085592510431578069303307 49628388765647367103954961)
                ·
                  refine ⟨37221291574235525327966221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49628388765647367103954961 37221291574235525327966221)
                  ·
                    refine ⟨13957984340338321997987333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37221291574235525327966221 13957984340338321997987333)
                    ·
                      refine ⟨2617122063813435374622625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13957984340338321997987333 2617122063813435374622625)
                      ·
                        rfl

theorem cell23_5096827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_5096827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096827 prefixEnd_5096827 := by exact prefixLift 5096827
  have htrace : WordTrace (prefixWord ++ tailWord_5096827) baseStart_5096827 baseEnd_5096827 := by
    simpa [prefixWord, tailWord_5096827, baseEnd_5096827] using wordTrace_append hprefix tailTrace_5096827
  have hstable : (prefixWord ++ tailWord_5096827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096827).length < 2 ^ (prefixWord ++ tailWord_5096827).sum := by decide
  have hdescent : baseEnd_5096827 < baseStart_5096827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096837 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_5096837 : Nat := 118140960795 + 5096837 * 2 ^ 59
def prefixEnd_5096837 : Nat := 4983230072969 + 3 ^ 40 * 5096837 * 2
def baseEnd_5096837 : Nat := 872375732873326778499193

theorem tailTrace_5096837 : CollatzResearch.WordTrace tailWord_5096837 prefixEnd_5096837 872375732873326778499193 := by
  unfold tailWord_5096837
  simp only [CollatzResearch.WordTrace]
  refine ⟨185896917436037494303016765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123931278290691662868677843 185896917436037494303016765)
  ·
    refine ⟨69711344038514060363631287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185896917436037494303016765 69711344038514060363631287)
    ·
      refine ⟨104567016057771090545446931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69711344038514060363631287 104567016057771090545446931)
      ·
        refine ⟨156850524086656635818170397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104567016057771090545446931 156850524086656635818170397)
        ·
          refine ⟨58818946532496238431813899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156850524086656635818170397 58818946532496238431813899)
          ·
            refine ⟨88228419798744357647720849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58818946532496238431813899 88228419798744357647720849)
            ·
              refine ⟨66171314849058268235790637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88228419798744357647720849 66171314849058268235790637)
              ·
                refine ⟨24814243068396850588421489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66171314849058268235790637 24814243068396850588421489)
                ·
                  refine ⟨18610682301297637941316117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24814243068396850588421489 18610682301297637941316117)
                  ·
                    refine ⟨872375732873326778499193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18610682301297637941316117 872375732873326778499193)
                    ·
                      rfl

theorem cell23_5096837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_5096837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096837 prefixEnd_5096837 := by exact prefixLift 5096837
  have htrace : WordTrace (prefixWord ++ tailWord_5096837) baseStart_5096837 baseEnd_5096837 := by
    simpa [prefixWord, tailWord_5096837, baseEnd_5096837] using wordTrace_append hprefix tailTrace_5096837
  have hstable : (prefixWord ++ tailWord_5096837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096837).length < 2 ^ (prefixWord ++ tailWord_5096837).sum := by decide
  have hdescent : baseEnd_5096837 < baseStart_5096837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096861 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5096861 : Nat := 118140960795 + 5096861 * 2 ^ 59
def prefixEnd_5096861 : Nat := 4983230072969 + 3 ^ 40 * 5096861 * 2
def baseEnd_5096861 : Nat := 2617139522155688241597469

theorem tailTrace_5096861 : CollatzResearch.WordTrace tailWord_5096861 prefixEnd_5096861 2617139522155688241597469 := by
  unfold tailWord_5096861
  simp only [CollatzResearch.WordTrace]
  refine ⟨185897792787950546401890437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123931861858633697601260291 185897792787950546401890437)
  ·
    refine ⟨34855836147740727450354457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185897792787950546401890437 34855836147740727450354457)
    ·
      refine ⟨26141877110805545587765843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34855836147740727450354457 26141877110805545587765843)
      ·
        refine ⟨39212815666208318381648765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26141877110805545587765843 39212815666208318381648765)
        ·
          refine ⟨14704805874828119393118287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39212815666208318381648765 14704805874828119393118287)
          ·
            refine ⟨22057208812242179089677431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14704805874828119393118287 22057208812242179089677431)
            ·
              refine ⟨33085813218363268634516147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22057208812242179089677431 33085813218363268634516147)
              ·
                refine ⟨49628719827544902951774221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33085813218363268634516147 49628719827544902951774221)
                ·
                  refine ⟨18610769935329338606915333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49628719827544902951774221 18610769935329338606915333)
                  ·
                    refine ⟨3489519362874250988796625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18610769935329338606915333 3489519362874250988796625)
                    ·
                      refine ⟨2617139522155688241597469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489519362874250988796625 2617139522155688241597469)
                      ·
                        rfl

theorem cell23_5096861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5096861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096861 prefixEnd_5096861 := by exact prefixLift 5096861
  have htrace : WordTrace (prefixWord ++ tailWord_5096861) baseStart_5096861 baseEnd_5096861 := by
    simpa [prefixWord, tailWord_5096861, baseEnd_5096861] using wordTrace_append hprefix tailTrace_5096861
  have hstable : (prefixWord ++ tailWord_5096861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096861).length < 2 ^ (prefixWord ++ tailWord_5096861).sum := by decide
  have hdescent : baseEnd_5096861 < baseStart_5096861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096907 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_5096907 : Nat := 118140960795 + 5096907 * 2 ^ 59
def prefixEnd_5096907 : Nat := 4983230072969 + 3 ^ 40 * 5096907 * 2
def baseEnd_5096907 : Nat := 2617163142265795061622257

theorem tailTrace_5096907 : CollatzResearch.WordTrace tailWord_5096907 prefixEnd_5096907 2617163142265795061622257 := by
  unfold tailWord_5096907
  simp only [CollatzResearch.WordTrace]
  refine ⟨185899470545783896258064975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123932980363855930838709983 185899470545783896258064975)
  ·
    refine ⟨278849205818675844387097463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185899470545783896258064975 278849205818675844387097463)
    ·
      refine ⟨418273808728013766580646195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278849205818675844387097463 418273808728013766580646195)
      ·
        refine ⟨627410713092020649870969293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418273808728013766580646195 627410713092020649870969293)
        ·
          refine ⟨235279017409507743701613485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627410713092020649870969293 235279017409507743701613485)
          ·
            refine ⟨88229631528565403888105057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235279017409507743701613485 88229631528565403888105057)
            ·
              refine ⟨66172223646424052916078793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88229631528565403888105057 66172223646424052916078793)
              ·
                refine ⟨49629167734818039687059095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66172223646424052916078793 49629167734818039687059095)
                ·
                  refine ⟨74443751602227059530588643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49629167734818039687059095 74443751602227059530588643)
                  ·
                    refine ⟨111665627403340589295882965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74443751602227059530588643 111665627403340589295882965)
                    ·
                      refine ⟨2617163142265795061622257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111665627403340589295882965 2617163142265795061622257)
                      ·
                        rfl

theorem cell23_5096907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_5096907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096907 prefixEnd_5096907 := by exact prefixLift 5096907
  have htrace : WordTrace (prefixWord ++ tailWord_5096907) baseStart_5096907 baseEnd_5096907 := by
    simpa [prefixWord, tailWord_5096907, baseEnd_5096907] using wordTrace_append hprefix tailTrace_5096907
  have hstable : (prefixWord ++ tailWord_5096907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096907).length < 2 ^ (prefixWord ++ tailWord_5096907).sum := by decide
  have hdescent : baseEnd_5096907 < baseStart_5096907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096918 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_5096918 : Nat := 118140960795 + 5096918 * 2 ^ 59
def prefixEnd_5096918 : Nat := 4983230072969 + 3 ^ 40 * 5096918 * 2
def baseEnd_5096918 : Nat := 290796532283666057620523

theorem tailTrace_5096918 : CollatzResearch.WordTrace tailWord_5096918 prefixEnd_5096918 290796532283666057620523 := by
  unfold tailWord_5096918
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618741984296502821044713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123933247832496030091143605 11618741984296502821044713)
  ·
    refine ⟨8714056488222377115783535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11618741984296502821044713 8714056488222377115783535)
    ·
      refine ⟨13071084732333565673675303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8714056488222377115783535 13071084732333565673675303)
      ·
        refine ⟨19606627098500348510512955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13071084732333565673675303 19606627098500348510512955)
        ·
          refine ⟨29409940647750522765769433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19606627098500348510512955 29409940647750522765769433)
          ·
            refine ⟨22057455485812892074327075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29409940647750522765769433 22057455485812892074327075)
            ·
              refine ⟨33086183228719338111490613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22057455485812892074327075 33086183228719338111490613)
              ·
                refine ⟨3101829677692437947952245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33086183228719338111490613 3101829677692437947952245)
                ·
                  refine ⟨290796532283666057620523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3101829677692437947952245 290796532283666057620523)
                  ·
                    rfl

theorem cell23_5096918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_5096918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096918 prefixEnd_5096918 := by exact prefixLift 5096918
  have htrace : WordTrace (prefixWord ++ tailWord_5096918) baseStart_5096918 baseEnd_5096918 := by
    simpa [prefixWord, tailWord_5096918, baseEnd_5096918] using wordTrace_append hprefix tailTrace_5096918
  have hstable : (prefixWord ++ tailWord_5096918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096918).length < 2 ^ (prefixWord ++ tailWord_5096918).sum := by decide
  have hdescent : baseEnd_5096918 < baseStart_5096918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096954 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_5096954 : Nat := 118140960795 + 5096954 * 2 ^ 59
def prefixEnd_5096954 : Nat := 4983230072969 + 3 ^ 40 * 5096954 * 2
def baseEnd_5096954 : Nat := 2617187275856556377734541

theorem tailTrace_5096954 : CollatzResearch.WordTrace tailWord_5096954 prefixEnd_5096954 2617187275856556377734541 := by
  unfold tailWord_5096954
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475296194153405821256479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123934123184409082190017277 46475296194153405821256479)
  ·
    refine ⟨69712944291230108731884719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46475296194153405821256479 69712944291230108731884719)
    ·
      refine ⟨104569416436845163097827079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69712944291230108731884719 104569416436845163097827079)
      ·
        refine ⟨156854124655267744646740619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104569416436845163097827079 156854124655267744646740619)
        ·
          refine ⟨235281186982901616970110929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156854124655267744646740619 235281186982901616970110929)
          ·
            refine ⟨176460890237176212727583197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235281186982901616970110929 176460890237176212727583197)
            ·
              refine ⟨66172833838941079772843699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176460890237176212727583197 66172833838941079772843699)
              ·
                refine ⟨99259250758411619659265549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66172833838941079772843699 99259250758411619659265549)
                ·
                  refine ⟨37222219034404357372224581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99259250758411619659265549 37222219034404357372224581)
                  ·
                    refine ⟨6979166068950817007292109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37222219034404357372224581 6979166068950817007292109)
                    ·
                      refine ⟨2617187275856556377734541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979166068950817007292109 2617187275856556377734541)
                      ·
                        rfl

theorem cell23_5096954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_5096954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096954 prefixEnd_5096954 := by exact prefixLift 5096954
  have htrace : WordTrace (prefixWord ++ tailWord_5096954) baseStart_5096954 baseEnd_5096954 := by
    simpa [prefixWord, tailWord_5096954, baseEnd_5096954] using wordTrace_append hprefix tailTrace_5096954
  have hstable : (prefixWord ++ tailWord_5096954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096954).length < 2 ^ (prefixWord ++ tailWord_5096954).sum := by decide
  have hdescent : baseEnd_5096954 < baseStart_5096954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096994 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5096994 : Nat := 118140960795 + 5096994 * 2 ^ 59
def prefixEnd_5096994 : Nat := 4983230072969 + 3 ^ 40 * 5096994 * 2
def baseEnd_5096994 : Nat := 2617207815082736221234357

theorem tailTrace_5096994 : CollatzResearch.WordTrace tailWord_5096994 prefixEnd_5096994 2617207815082736221234357 := by
  unfold tailWord_5096994
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475660924117177529120509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123935095797645806744321357 46475660924117177529120509)
  ·
    refine ⟨17428372846543941573420191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46475660924117177529120509 17428372846543941573420191)
    ·
      refine ⟨26142559269815912360130287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17428372846543941573420191 26142559269815912360130287)
      ·
        refine ⟨39213838904723868540195431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26142559269815912360130287 39213838904723868540195431)
        ·
          refine ⟨58820758357085802810293147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39213838904723868540195431 58820758357085802810293147)
          ·
            refine ⟨88231137535628704215439721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58820758357085802810293147 88231137535628704215439721)
            ·
              refine ⟨66173353151721528161579791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88231137535628704215439721 66173353151721528161579791)
              ·
                refine ⟨99260029727582292242369687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66173353151721528161579791 99260029727582292242369687)
                ·
                  refine ⟨148890044591373438363554531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99260029727582292242369687 148890044591373438363554531)
                  ·
                    refine ⟨223335066887060157545331797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148890044591373438363554531 223335066887060157545331797)
                    ·
                      refine ⟨2617207815082736221234357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 223335066887060157545331797 2617207815082736221234357)
                      ·
                        rfl

theorem cell23_5096994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5096994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096994 prefixEnd_5096994 := by exact prefixLift 5096994
  have htrace : WordTrace (prefixWord ++ tailWord_5096994) baseStart_5096994 baseEnd_5096994 := by
    simpa [prefixWord, tailWord_5096994, baseEnd_5096994] using wordTrace_append hprefix tailTrace_5096994
  have hstable : (prefixWord ++ tailWord_5096994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096994).length < 2 ^ (prefixWord ++ tailWord_5096994).sum := by decide
  have hdescent : baseEnd_5096994 < baseStart_5096994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5096995 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 3, 4]
def baseStart_5096995 : Nat := 118140960795 + 5096995 * 2 ^ 59
def prefixEnd_5096995 : Nat := 4983230072969 + 3 ^ 40 * 5096995 * 2
def baseEnd_5096995 : Nat := 872402776187796905773951

theorem tailTrace_5096995 : CollatzResearch.WordTrace tailWord_5096995 prefixEnd_5096995 872402776187796905773951 := by
  unfold tailWord_5096995
  simp only [CollatzResearch.WordTrace]
  refine ⟨185902680169465087287268439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123935120112976724858178959 185902680169465087287268439)
  ·
    refine ⟨278854020254197630930902659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185902680169465087287268439 278854020254197630930902659)
    ·
      refine ⟨418281030381296446396353989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278854020254197630930902659 418281030381296446396353989)
      ·
        refine ⟨78427693196493083699316373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418281030381296446396353989 78427693196493083699316373)
        ·
          refine ⟨3676298118585613298405455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78427693196493083699316373 3676298118585613298405455)
          ·
            refine ⟨5514447177878419947608183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676298118585613298405455 5514447177878419947608183)
            ·
              refine ⟨8271670766817629921412275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514447177878419947608183 8271670766817629921412275)
              ·
                refine ⟨12407506150226444882118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8271670766817629921412275 12407506150226444882118413)
                ·
                  refine ⟨4652814806334916830794405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12407506150226444882118413 4652814806334916830794405)
                  ·
                    refine ⟨872402776187796905773951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4652814806334916830794405 872402776187796905773951)
                    ·
                      rfl

theorem cell23_5096995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 4].length) (baseStart_5096995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5096995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5096995 prefixEnd_5096995 := by exact prefixLift 5096995
  have htrace : WordTrace (prefixWord ++ tailWord_5096995) baseStart_5096995 baseEnd_5096995 := by
    simpa [prefixWord, tailWord_5096995, baseEnd_5096995] using wordTrace_append hprefix tailTrace_5096995
  have hstable : (prefixWord ++ tailWord_5096995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5096995).length < 2 ^ (prefixWord ++ tailWord_5096995).sum := by decide
  have hdescent : baseEnd_5096995 < baseStart_5096995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5096995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097052 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_5097052 : Nat := 118140960795 + 5097052 * 2 ^ 59
def prefixEnd_5097052 : Nat := 4983230072969 + 3 ^ 40 * 5097052 * 2
def baseEnd_5097052 : Nat := 2617237596960696994309091

theorem tailTrace_5097052 : CollatzResearch.WordTrace tailWord_5097052 prefixEnd_5097052 2617237596960696994309091 := by
  unfold tailWord_5097052
  simp only [CollatzResearch.WordTrace]
  refine ⟨92952379565129293011046705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123936506086839057348062273 92952379565129293011046705)
  ·
    refine ⟨69714284673846969758285029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92952379565129293011046705 69714284673846969758285029)
    ·
      refine ⟨13071428376346306829678443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69714284673846969758285029 13071428376346306829678443)
      ·
        refine ⟨19607142564519460244517665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13071428376346306829678443 19607142564519460244517665)
        ·
          refine ⟨14705356923389595183388249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19607142564519460244517665 14705356923389595183388249)
          ·
            refine ⟨11029017692542196387541187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14705356923389595183388249 11029017692542196387541187)
            ·
              refine ⟨16543526538813294581311781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11029017692542196387541187 16543526538813294581311781)
              ·
                refine ⟨3101911226027492733995959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16543526538813294581311781 3101911226027492733995959)
                ·
                  refine ⟨4652866839041239100993939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101911226027492733995959 4652866839041239100993939)
                  ·
                    refine ⟨6979300258561858651490909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652866839041239100993939 6979300258561858651490909)
                    ·
                      refine ⟨2617237596960696994309091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979300258561858651490909 2617237596960696994309091)
                      ·
                        rfl

theorem cell23_5097052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_5097052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097052 prefixEnd_5097052 := by exact prefixLift 5097052
  have htrace : WordTrace (prefixWord ++ tailWord_5097052) baseStart_5097052 baseEnd_5097052 := by
    simpa [prefixWord, tailWord_5097052, baseEnd_5097052] using wordTrace_append hprefix tailTrace_5097052
  have hstable : (prefixWord ++ tailWord_5097052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097052).length < 2 ^ (prefixWord ++ tailWord_5097052).sum := by decide
  have hdescent : baseEnd_5097052 < baseStart_5097052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097081 : List Nat := [1, 2, 1, 3, 3, 1, 5, 7]
def baseStart_5097081 : Nat := 118140960795 + 5097081 * 2 ^ 59
def prefixEnd_5097081 : Nat := 4983230072969 + 3 ^ 40 * 5097081 * 2
def baseEnd_5097081 : Nat := 96935277329617680772091

theorem tailTrace_5097081 : CollatzResearch.WordTrace tailWord_5097081 prefixEnd_5097081 96935277329617680772091 := by
  unfold tailWord_5097081
  simp only [CollatzResearch.WordTrace]
  refine ⟨185905816847153523974899097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123937211231435682649932731 185905816847153523974899097)
  ·
    refine ⟨139429362635365142981174323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185905816847153523974899097 139429362635365142981174323)
    ·
      refine ⟨209144043953047714471761485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139429362635365142981174323 209144043953047714471761485)
      ·
        refine ⟨78429016482392892926910557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209144043953047714471761485 78429016482392892926910557)
        ·
          refine ⟨29410881180897334847591459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78429016482392892926910557 29410881180897334847591459)
          ·
            refine ⟨44116321771346002271387189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29410881180897334847591459 44116321771346002271387189)
            ·
              refine ⟨4135905166063687712942549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44116321771346002271387189 4135905166063687712942549)
              ·
                refine ⟨96935277329617680772091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4135905166063687712942549 96935277329617680772091)
                ·
                  rfl

theorem cell23_5097081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 7].length) (baseStart_5097081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097081 prefixEnd_5097081 := by exact prefixLift 5097081
  have htrace : WordTrace (prefixWord ++ tailWord_5097081) baseStart_5097081 baseEnd_5097081 := by
    simpa [prefixWord, tailWord_5097081, baseEnd_5097081] using wordTrace_append hprefix tailTrace_5097081
  have hstable : (prefixWord ++ tailWord_5097081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097081).length < 2 ^ (prefixWord ++ tailWord_5097081).sum := by decide
  have hdescent : baseEnd_5097081 < baseStart_5097081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097092 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_5097092 : Nat := 118140960795 + 5097092 * 2 ^ 59
def prefixEnd_5097092 : Nat := 4983230072969 + 3 ^ 40 * 5097092 * 2
def baseEnd_5097092 : Nat := 2617258136186876837808907

theorem tailTrace_5097092 : CollatzResearch.WordTrace tailWord_5097092 prefixEnd_5097092 2617258136186876837808907 := by
  unfold tailWord_5097092
  simp only [CollatzResearch.WordTrace]
  refine ⟨92953109025056836426774765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123937478700075781902366353 92953109025056836426774765)
  ·
    refine ⟨34857415884396313660040537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92953109025056836426774765 34857415884396313660040537)
    ·
      refine ⟨26143061913297235245030403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34857415884396313660040537 26143061913297235245030403)
      ·
        refine ⟨39214592869945852867545605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26143061913297235245030403 39214592869945852867545605)
        ·
          refine ⟨7352736163114847412664801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39214592869945852867545605 7352736163114847412664801)
          ·
            refine ⟨5514552122336135559498601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7352736163114847412664801 5514552122336135559498601)
            ·
              refine ⟨4135914091752101669623951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5514552122336135559498601 4135914091752101669623951)
              ·
                refine ⟨6203871137628152504435927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135914091752101669623951 6203871137628152504435927)
                ·
                  refine ⟨9305806706442228756653891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203871137628152504435927 9305806706442228756653891)
                  ·
                    refine ⟨13958710059663343134980837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9305806706442228756653891 13958710059663343134980837)
                    ·
                      refine ⟨2617258136186876837808907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13958710059663343134980837 2617258136186876837808907)
                      ·
                        rfl

theorem cell23_5097092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_5097092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097092 prefixEnd_5097092 := by exact prefixLift 5097092
  have htrace : WordTrace (prefixWord ++ tailWord_5097092) baseStart_5097092 baseEnd_5097092 := by
    simpa [prefixWord, tailWord_5097092, baseEnd_5097092] using wordTrace_append hprefix tailTrace_5097092
  have hstable : (prefixWord ++ tailWord_5097092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097092).length < 2 ^ (prefixWord ++ tailWord_5097092).sum := by decide
  have hdescent : baseEnd_5097092 < baseStart_5097092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097095 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_5097095 : Nat := 118140960795 + 5097095 * 2 ^ 59
def prefixEnd_5097095 : Nat := 4983230072969 + 3 ^ 40 * 5097095 * 2
def baseEnd_5097095 : Nat := 2617259676628840326071393

theorem tailTrace_5097095 : CollatzResearch.WordTrace tailWord_5097095 prefixEnd_5097095 2617259676628840326071393 := by
  unfold tailWord_5097095
  simp only [CollatzResearch.WordTrace]
  refine ⟨185906327469102804365908739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123937551646068536243939159 185906327469102804365908739)
  ·
    refine ⟨278859491203654206548863109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185906327469102804365908739 278859491203654206548863109)
    ·
      refine ⟨52286154600685163727911833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278859491203654206548863109 52286154600685163727911833)
      ·
        refine ⟨39214615950513872795933875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52286154600685163727911833 39214615950513872795933875)
        ·
          refine ⟨58821923925770809193900813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39214615950513872795933875 58821923925770809193900813)
          ·
            refine ⟨22058221472164053447712805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58821923925770809193900813 22058221472164053447712805)
            ·
              refine ⟨4135916526030760021446151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22058221472164053447712805 4135916526030760021446151)
              ·
                refine ⟨6203874789046140032169227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135916526030760021446151 6203874789046140032169227)
                ·
                  refine ⟨9305812183569210048253841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203874789046140032169227 9305812183569210048253841)
                  ·
                    refine ⟨6979359137676907536190381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9305812183569210048253841 6979359137676907536190381)
                    ·
                      refine ⟨2617259676628840326071393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979359137676907536190381 2617259676628840326071393)
                      ·
                        rfl

theorem cell23_5097095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_5097095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097095 prefixEnd_5097095 := by exact prefixLift 5097095
  have htrace : WordTrace (prefixWord ++ tailWord_5097095) baseStart_5097095 baseEnd_5097095 := by
    simpa [prefixWord, tailWord_5097095, baseEnd_5097095] using wordTrace_append hprefix tailTrace_5097095
  have hstable : (prefixWord ++ tailWord_5097095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097095).length < 2 ^ (prefixWord ++ tailWord_5097095).sum := by decide
  have hdescent : baseEnd_5097095 < baseStart_5097095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097122 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5097122 : Nat := 118140960795 + 5097122 * 2 ^ 59
def prefixEnd_5097122 : Nat := 4983230072969 + 3 ^ 40 * 5097122 * 2
def baseEnd_5097122 : Nat := 2617273540606511720433769

theorem tailTrace_5097122 : CollatzResearch.WordTrace tailWord_5097122 prefixEnd_5097122 2617273540606511720433769 := by
  unfold tailWord_5097122
  simp only [CollatzResearch.WordTrace]
  refine ⟨46476828060001246994285405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123938208160003325318094413 46476828060001246994285405)
  ·
    refine ⟨17428810522500467622857027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46476828060001246994285405 17428810522500467622857027)
    ·
      refine ⟨26143215783750701434285541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17428810522500467622857027 26143215783750701434285541)
      ·
        refine ⟨4901852959453256518928539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26143215783750701434285541 4901852959453256518928539)
        ·
          refine ⟨7352779439179884778392809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901852959453256518928539 7352779439179884778392809)
          ·
            refine ⟨5514584579384913583794607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7352779439179884778392809 5514584579384913583794607)
            ·
              refine ⟨8271876869077370375691911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514584579384913583794607 8271876869077370375691911)
              ·
                refine ⟨12407815303616055563537867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8271876869077370375691911 12407815303616055563537867)
                ·
                  refine ⟨18611722955424083345306801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12407815303616055563537867 18611722955424083345306801)
                  ·
                    refine ⟨13958792216568062508980101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18611722955424083345306801 13958792216568062508980101)
                    ·
                      refine ⟨2617273540606511720433769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13958792216568062508980101 2617273540606511720433769)
                      ·
                        rfl

theorem cell23_5097122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5097122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097122 prefixEnd_5097122 := by exact prefixLift 5097122
  have htrace : WordTrace (prefixWord ++ tailWord_5097122) baseStart_5097122 baseEnd_5097122 := by
    simpa [prefixWord, tailWord_5097122, baseEnd_5097122] using wordTrace_append hprefix tailTrace_5097122
  have hstable : (prefixWord ++ tailWord_5097122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097122).length < 2 ^ (prefixWord ++ tailWord_5097122).sum := by decide
  have hdescent : baseEnd_5097122 < baseStart_5097122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097135 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 1, 3, 2]
def baseStart_5097135 : Nat := 118140960795 + 5097135 * 2 ^ 59
def prefixEnd_5097135 : Nat := 4983230072969 + 3 ^ 40 * 5097135 * 2
def baseEnd_5097135 : Nat := 2617280215855020169571209

theorem tailTrace_5097135 : CollatzResearch.WordTrace tailWord_5097135 prefixEnd_5097135 2617280215855020169571209 := by
  unfold tailWord_5097135
  simp only [CollatzResearch.WordTrace]
  refine ⟨185907786388957891197364859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123938524259305260798243239 185907786388957891197364859)
  ·
    refine ⟨278861679583436836796047289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185907786388957891197364859 278861679583436836796047289)
    ·
      refine ⟨209146259687577627597035467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278861679583436836796047289 209146259687577627597035467)
      ·
        refine ⟨313719389531366441395553201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209146259687577627597035467 313719389531366441395553201)
        ·
          refine ⟨235289542148524831046664901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313719389531366441395553201 235289542148524831046664901)
          ·
            refine ⟨44116789152848405821249669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235289542148524831046664901 44116789152848405821249669)
            ·
              refine ⟨8271897966159076091484313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44116789152848405821249669 8271897966159076091484313)
              ·
                refine ⟨6203923474619307068613235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8271897966159076091484313 6203923474619307068613235)
                ·
                  refine ⟨9305885211928960602919853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6203923474619307068613235 9305885211928960602919853)
                  ·
                    refine ⟨3489706954473360226094945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9305885211928960602919853 3489706954473360226094945)
                    ·
                      refine ⟨2617280215855020169571209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489706954473360226094945 2617280215855020169571209)
                      ·
                        rfl

theorem cell23_5097135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 3, 2].length) (baseStart_5097135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097135 prefixEnd_5097135 := by exact prefixLift 5097135
  have htrace : WordTrace (prefixWord ++ tailWord_5097135) baseStart_5097135 baseEnd_5097135 := by
    simpa [prefixWord, tailWord_5097135, baseEnd_5097135] using wordTrace_append hprefix tailTrace_5097135
  have hstable : (prefixWord ++ tailWord_5097135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097135).length < 2 ^ (prefixWord ++ tailWord_5097135).sum := by decide
  have hdescent : baseEnd_5097135 < baseStart_5097135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097142 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5097142 : Nat := 118140960795 + 5097142 * 2 ^ 59
def prefixEnd_5097142 : Nat := 4983230072969 + 3 ^ 40 * 5097142 * 2
def baseEnd_5097142 : Nat := 2617283810219601642183677

theorem tailTrace_5097142 : CollatzResearch.WordTrace tailWord_5097142 prefixEnd_5097142 2617283810219601642183677 := by
  unfold tailWord_5097142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11619252606245783212054355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123938694466621687595246453 11619252606245783212054355)
  ·
    refine ⟨17428878909368674818081533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11619252606245783212054355 17428878909368674818081533)
    ·
      refine ⟨6535829591013253056780575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17428878909368674818081533 6535829591013253056780575)
      ·
        refine ⟨9803744386519879585170863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6535829591013253056780575 9803744386519879585170863)
        ·
          refine ⟨14705616579779819377756295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9803744386519879585170863 14705616579779819377756295)
          ·
            refine ⟨22058424869669729066634443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14705616579779819377756295 22058424869669729066634443)
            ·
              refine ⟨33087637304504593599951665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22058424869669729066634443 33087637304504593599951665)
              ·
                refine ⟨24815727978378445199963749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33087637304504593599951665 24815727978378445199963749)
                ·
                  refine ⟨4652948995945958474993203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24815727978378445199963749 4652948995945958474993203)
                  ·
                    refine ⟨6979423493918937712489805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652948995945958474993203 6979423493918937712489805)
                    ·
                      refine ⟨2617283810219601642183677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979423493918937712489805 2617283810219601642183677)
                      ·
                        rfl

theorem cell23_5097142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5097142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097142 prefixEnd_5097142 := by exact prefixLift 5097142
  have htrace : WordTrace (prefixWord ++ tailWord_5097142) baseStart_5097142 baseEnd_5097142 := by
    simpa [prefixWord, tailWord_5097142, baseEnd_5097142] using wordTrace_append hprefix tailTrace_5097142
  have hstable : (prefixWord ++ tailWord_5097142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097142).length < 2 ^ (prefixWord ++ tailWord_5097142).sum := by decide
  have hdescent : baseEnd_5097142 < baseStart_5097142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097151 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_5097151 : Nat := 118140960795 + 5097151 * 2 ^ 59
def prefixEnd_5097151 : Nat := 4983230072969 + 3 ^ 40 * 5097151 * 2
def baseEnd_5097151 : Nat := 2617288431545492106971135

theorem tailTrace_5097151 : CollatzResearch.WordTrace tailWord_5097151 prefixEnd_5097151 2617288431545492106971135 := by
  unfold tailWord_5097151
  simp only [CollatzResearch.WordTrace]
  refine ⟨185908369956899925929947307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123938913304599950619964871 185908369956899925929947307)
  ·
    refine ⟨278862554935349888894920961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185908369956899925929947307 278862554935349888894920961)
    ·
      refine ⟨209146916201512416671190721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278862554935349888894920961 209146916201512416671190721)
      ·
        refine ⟨156860187151134312503393041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209146916201512416671190721 156860187151134312503393041)
        ·
          refine ⟨117645140363350734377544781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156860187151134312503393041 117645140363350734377544781)
          ·
            refine ⟨44116927636256525391579293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117645140363350734377544781 44116927636256525391579293)
            ·
              refine ⟨16543847863596197021842235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44116927636256525391579293 16543847863596197021842235)
              ·
                refine ⟨24815771795394295532763353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16543847863596197021842235 24815771795394295532763353)
                ·
                  refine ⟨18611828846545721649572515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24815771795394295532763353 18611828846545721649572515)
                  ·
                    refine ⟨27917743269818582474358773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18611828846545721649572515 27917743269818582474358773)
                    ·
                      refine ⟨2617288431545492106971135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27917743269818582474358773 2617288431545492106971135)
                      ·
                        rfl

theorem cell23_5097151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_5097151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097151 prefixEnd_5097151 := by exact prefixLift 5097151
  have htrace : WordTrace (prefixWord ++ tailWord_5097151) baseStart_5097151 baseEnd_5097151 := by
    simpa [prefixWord, tailWord_5097151, baseEnd_5097151] using wordTrace_append hprefix tailTrace_5097151
  have hstable : (prefixWord ++ tailWord_5097151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097151).length < 2 ^ (prefixWord ++ tailWord_5097151).sum := by decide
  have hdescent : baseEnd_5097151 < baseStart_5097151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097221 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_5097221 : Nat := 118140960795 + 5097221 * 2 ^ 59
def prefixEnd_5097221 : Nat := 4983230072969 + 3 ^ 40 * 5097221 * 2
def baseEnd_5097221 : Nat := 2617324375191306833095813

theorem tailTrace_5097221 : CollatzResearch.WordTrace tailWord_5097221 prefixEnd_5097221 2617324375191306833095813 := by
  unfold tailWord_5097221
  simp only [CollatzResearch.WordTrace]
  refine ⟨185910923066646327884995517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123940615377764218589997011 185910923066646327884995517)
  ·
    refine ⟨69716596149992372956873319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185910923066646327884995517 69716596149992372956873319)
    ·
      refine ⟨104574894224988559435309979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69716596149992372956873319 104574894224988559435309979)
      ·
        refine ⟨156862341337482839152964969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104574894224988559435309979 156862341337482839152964969)
        ·
          refine ⟨117646756003112129364723727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156862341337482839152964969 117646756003112129364723727)
          ·
            refine ⟨176470134004668194047085591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117646756003112129364723727 176470134004668194047085591)
            ·
              refine ⟨264705201007002291070628387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176470134004668194047085591 264705201007002291070628387)
              ·
                refine ⟨397057801510503436605942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264705201007002291070628387 397057801510503436605942581)
                ·
                  refine ⟨37224168891609697181807117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397057801510503436605942581 37224168891609697181807117)
                  ·
                    refine ⟨13959063334353636443177669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37224168891609697181807117 13959063334353636443177669)
                    ·
                      refine ⟨2617324375191306833095813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13959063334353636443177669 2617324375191306833095813)
                      ·
                        rfl

theorem cell23_5097221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_5097221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097221 prefixEnd_5097221 := by exact prefixLift 5097221
  have htrace : WordTrace (prefixWord ++ tailWord_5097221) baseStart_5097221 baseEnd_5097221 := by
    simpa [prefixWord, tailWord_5097221, baseEnd_5097221] using wordTrace_append hprefix tailTrace_5097221
  have hstable : (prefixWord ++ tailWord_5097221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097221).length < 2 ^ (prefixWord ++ tailWord_5097221).sum := by decide
  have hdescent : baseEnd_5097221 < baseStart_5097221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097305 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 3]
def baseStart_5097305 : Nat := 118140960795 + 5097305 * 2 ^ 59
def prefixEnd_5097305 : Nat := 4983230072969 + 3 ^ 40 * 5097305 * 2
def baseEnd_5097305 : Nat := 2617367507566284504445427

theorem tailTrace_5097305 : CollatzResearch.WordTrace tailWord_5097305 prefixEnd_5097305 2617367507566284504445427 := by
  unfold tailWord_5097305
  simp only [CollatzResearch.WordTrace]
  refine ⟨185913986798342010231053369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123942657865561340154035579 185913986798342010231053369)
  ·
    refine ⟨139435490098756507673290027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185913986798342010231053369 139435490098756507673290027)
    ·
      refine ⟨209153235148134761509935041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139435490098756507673290027 209153235148134761509935041)
      ·
        refine ⟨156864926361101071132451281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209153235148134761509935041 156864926361101071132451281)
        ·
          refine ⟨117648694770825803349338461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156864926361101071132451281 117648694770825803349338461)
          ·
            refine ⟨44118260539059676256001923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117648694770825803349338461 44118260539059676256001923)
            ·
              refine ⟨66177390808589514384002885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44118260539059676256001923 66177390808589514384002885)
              ·
                refine ⟨12408260776610533947000541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66177390808589514384002885 12408260776610533947000541)
                ·
                  refine ⟨4653097791228950230125203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12408260776610533947000541 4653097791228950230125203)
                  ·
                    refine ⟨6979646686843425345187805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4653097791228950230125203 6979646686843425345187805)
                    ·
                      refine ⟨2617367507566284504445427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979646686843425345187805 2617367507566284504445427)
                      ·
                        rfl

theorem cell23_5097305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_5097305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097305 prefixEnd_5097305 := by exact prefixLift 5097305
  have htrace : WordTrace (prefixWord ++ tailWord_5097305) baseStart_5097305 baseEnd_5097305 := by
    simpa [prefixWord, tailWord_5097305, baseEnd_5097305] using wordTrace_append hprefix tailTrace_5097305
  have hstable : (prefixWord ++ tailWord_5097305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097305).length < 2 ^ (prefixWord ++ tailWord_5097305).sum := by decide
  have hdescent : baseEnd_5097305 < baseStart_5097305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097316 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_5097316 : Nat := 118140960795 + 5097316 * 2 ^ 59
def prefixEnd_5097316 : Nat := 4983230072969 + 3 ^ 40 * 5097316 * 2
def baseEnd_5097316 : Nat := 872457718617827987135959

theorem tailTrace_5097316 : CollatzResearch.WordTrace tailWord_5097316 prefixEnd_5097316 872457718617827987135959 := by
  unfold tailWord_5097316
  simp only [CollatzResearch.WordTrace]
  refine ⟨92957194000651079554851901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123942925334201439406469201 92957194000651079554851901)
  ·
    refine ⟨34858947750244154833069463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92957194000651079554851901 34858947750244154833069463)
    ·
      refine ⟨52288421625366232249604195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34858947750244154833069463 52288421625366232249604195)
      ·
        refine ⟨78432632438049348374406293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52288421625366232249604195 78432632438049348374406293)
        ·
          refine ⟨3676529645533563205050295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78432632438049348374406293 3676529645533563205050295)
          ·
            refine ⟨5514794468300344807575443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676529645533563205050295 5514794468300344807575443)
            ·
              refine ⟨8272191702450517211363165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514794468300344807575443 8272191702450517211363165)
              ·
                refine ⟨3102071888418943954261187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8272191702450517211363165 3102071888418943954261187)
                ·
                  refine ⟨4653107832628415931391781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102071888418943954261187 4653107832628415931391781)
                  ·
                    refine ⟨872457718617827987135959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653107832628415931391781 872457718617827987135959)
                    ·
                      rfl

theorem cell23_5097316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_5097316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097316 prefixEnd_5097316 := by exact prefixLift 5097316
  have htrace : WordTrace (prefixWord ++ tailWord_5097316) baseStart_5097316 baseEnd_5097316 := by
    simpa [prefixWord, tailWord_5097316, baseEnd_5097316] using wordTrace_append hprefix tailTrace_5097316
  have hstable : (prefixWord ++ tailWord_5097316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097316).length < 2 ^ (prefixWord ++ tailWord_5097316).sum := by decide
  have hdescent : baseEnd_5097316 < baseStart_5097316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097325 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5097325 : Nat := 118140960795 + 5097325 * 2 ^ 59
def prefixEnd_5097325 : Nat := 4983230072969 + 3 ^ 40 * 5097325 * 2
def baseEnd_5097325 : Nat := 872459259059791475398445

theorem tailTrace_5097325 : CollatzResearch.WordTrace tailWord_5097325 prefixEnd_5097325 872459259059791475398445 := by
  unfold tailWord_5097325
  simp only [CollatzResearch.WordTrace]
  refine ⟨185914716258269553646781429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123943144172179702431187619 185914716258269553646781429)
  ·
    refine ⟨17429504649212770654385759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185914716258269553646781429 17429504649212770654385759)
    ·
      refine ⟨26144256973819155981578639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17429504649212770654385759 26144256973819155981578639)
      ·
        refine ⟨39216385460728733972367959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26144256973819155981578639 39216385460728733972367959)
        ·
          refine ⟨58824578191093100958551939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39216385460728733972367959 58824578191093100958551939)
          ·
            refine ⟨88236867286639651437827909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58824578191093100958551939 88236867286639651437827909)
            ·
              refine ⟨16544412616244934644592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88236867286639651437827909 16544412616244934644592733)
              ·
                refine ⟨6204154731091850491722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16544412616244934644592733 6204154731091850491722275)
                ·
                  refine ⟨9306232096637775737583413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204154731091850491722275 9306232096637775737583413)
                  ·
                    refine ⟨872459259059791475398445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9306232096637775737583413 872459259059791475398445)
                    ·
                      rfl

theorem cell23_5097325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5097325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097325 prefixEnd_5097325 := by exact prefixLift 5097325
  have htrace : WordTrace (prefixWord ++ tailWord_5097325) baseStart_5097325 baseEnd_5097325 := by
    simpa [prefixWord, tailWord_5097325, baseEnd_5097325] using wordTrace_append hprefix tailTrace_5097325
  have hstable : (prefixWord ++ tailWord_5097325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097325).length < 2 ^ (prefixWord ++ tailWord_5097325).sum := by decide
  have hdescent : baseEnd_5097325 < baseStart_5097325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097328 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_5097328 : Nat := 118140960795 + 5097328 * 2 ^ 59
def prefixEnd_5097328 : Nat := 4983230072969 + 3 ^ 40 * 5097328 * 2
def baseEnd_5097328 : Nat := 2617379317621337914457821

theorem tailTrace_5097328 : CollatzResearch.WordTrace tailWord_5097328 prefixEnd_5097328 2617379317621337914457821 := by
  unfold tailWord_5097328
  simp only [CollatzResearch.WordTrace]
  refine ⟨92957412838629342579570319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123943217118172456772760425 92957412838629342579570319)
  ·
    refine ⟨139436119257944013869355479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92957412838629342579570319 139436119257944013869355479)
    ·
      refine ⟨209154178886916020804033219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139436119257944013869355479 209154178886916020804033219)
      ·
        refine ⟨313731268330374031206049829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209154178886916020804033219 313731268330374031206049829)
        ·
          refine ⟨58824612811945130851134343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313731268330374031206049829 58824612811945130851134343)
          ·
            refine ⟨88236919217917696276701515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58824612811945130851134343 88236919217917696276701515)
            ·
              refine ⟨132355378826876544415052273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88236919217917696276701515 132355378826876544415052273)
              ·
                refine ⟨99266534120157408311289205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132355378826876544415052273 99266534120157408311289205)
                ·
                  refine ⟨9306237573764757029183363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99266534120157408311289205 9306237573764757029183363)
                  ·
                    refine ⟨13959356360647135543775045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9306237573764757029183363 13959356360647135543775045)
                    ·
                      refine ⟨2617379317621337914457821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13959356360647135543775045 2617379317621337914457821)
                      ·
                        rfl

theorem cell23_5097328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_5097328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097328 prefixEnd_5097328 := by exact prefixLift 5097328
  have htrace : WordTrace (prefixWord ++ tailWord_5097328) baseStart_5097328 baseEnd_5097328 := by
    simpa [prefixWord, tailWord_5097328, baseEnd_5097328] using wordTrace_append hprefix tailTrace_5097328
  have hstable : (prefixWord ++ tailWord_5097328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097328).length < 2 ^ (prefixWord ++ tailWord_5097328).sum := by decide
  have hdescent : baseEnd_5097328 < baseStart_5097328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097362 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5097362 : Nat := 118140960795 + 5097362 * 2 ^ 59
def prefixEnd_5097362 : Nat := 4983230072969 + 3 ^ 40 * 5097362 * 2
def baseEnd_5097362 : Nat := 2617396775963590781432665

theorem tailTrace_5097362 : CollatzResearch.WordTrace tailWord_5097362 prefixEnd_5097362 2617396775963590781432665 := by
  unfold tailWord_5097362
  simp only [CollatzResearch.WordTrace]
  refine ⟨46479016439783877241469585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123944043839423672643918893 46479016439783877241469585)
  ·
    refine ⟨34859262329837907931102189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46479016439783877241469585 34859262329837907931102189)
    ·
      refine ⟨13072223373689215474163321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34859262329837907931102189 13072223373689215474163321)
      ·
        refine ⟨9804167530266911605622491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13072223373689215474163321 9804167530266911605622491)
        ·
          refine ⟨14706251295400367408433737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804167530266911605622491 14706251295400367408433737)
          ·
            refine ⟨11029688471550275556325303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14706251295400367408433737 11029688471550275556325303)
            ·
              refine ⟨16544532707325413334487955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11029688471550275556325303 16544532707325413334487955)
              ·
                refine ⟨24816799060988120001731933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16544532707325413334487955 24816799060988120001731933)
                ·
                  refine ⟨9306299647870545000649475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24816799060988120001731933 9306299647870545000649475)
                  ·
                    refine ⟨13959449471805817500974213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9306299647870545000649475 13959449471805817500974213)
                    ·
                      refine ⟨2617396775963590781432665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13959449471805817500974213 2617396775963590781432665)
                      ·
                        rfl

theorem cell23_5097362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5097362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097362 prefixEnd_5097362 := by exact prefixLift 5097362
  have htrace : WordTrace (prefixWord ++ tailWord_5097362) baseStart_5097362 baseEnd_5097362 := by
    simpa [prefixWord, tailWord_5097362, baseEnd_5097362] using wordTrace_append hprefix tailTrace_5097362
  have hstable : (prefixWord ++ tailWord_5097362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097362).length < 2 ^ (prefixWord ++ tailWord_5097362).sum := by decide
  have hdescent : baseEnd_5097362 < baseStart_5097362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097365 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_5097365 : Nat := 118140960795 + 5097365 * 2 ^ 59
def prefixEnd_5097365 : Nat := 4983230072969 + 3 ^ 40 * 5097365 * 2
def baseEnd_5097365 : Nat := 2617398316405554269695151

theorem tailTrace_5097365 : CollatzResearch.WordTrace tailWord_5097365 prefixEnd_5097365 2617398316405554269695151 := by
  unfold tailWord_5097365
  simp only [CollatzResearch.WordTrace]
  refine ⟨185916175178124640478237549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123944116785416426985491699 185916175178124640478237549)
  ·
    refine ⟨69718565691796740179339081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185916175178124640478237549 69718565691796740179339081)
    ·
      refine ⟨52288924268847555134504311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69718565691796740179339081 52288924268847555134504311)
      ·
        refine ⟨78433386403271332701756467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52288924268847555134504311 78433386403271332701756467)
        ·
          refine ⟨117650079604906999052634701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78433386403271332701756467 117650079604906999052634701)
          ·
            refine ⟨44118779851840124644738013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117650079604906999052634701 44118779851840124644738013)
            ·
              refine ⟨16544542444440046741776755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44118779851840124644738013 16544542444440046741776755)
              ·
                refine ⟨24816813666660070112665133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16544542444440046741776755 24816813666660070112665133)
                ·
                  refine ⟨9306305124997526292249425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24816813666660070112665133 9306305124997526292249425)
                  ·
                    refine ⟨6979728843748144719187069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9306305124997526292249425 6979728843748144719187069)
                    ·
                      refine ⟨2617398316405554269695151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979728843748144719187069 2617398316405554269695151)
                      ·
                        rfl

theorem cell23_5097365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_5097365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097365 prefixEnd_5097365 := by exact prefixLift 5097365
  have htrace : WordTrace (prefixWord ++ tailWord_5097365) baseStart_5097365 baseEnd_5097365 := by
    simpa [prefixWord, tailWord_5097365, baseEnd_5097365] using wordTrace_append hprefix tailTrace_5097365
  have hstable : (prefixWord ++ tailWord_5097365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097365).length < 2 ^ (prefixWord ++ tailWord_5097365).sum := by decide
  have hdescent : baseEnd_5097365 < baseStart_5097365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097379 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 1, 2, 2]
def baseStart_5097379 : Nat := 118140960795 + 5097379 * 2 ^ 59
def prefixEnd_5097379 : Nat := 4983230072969 + 3 ^ 40 * 5097379 * 2
def baseEnd_5097379 : Nat := 2617405505134717214920087

theorem tailTrace_5097379 : CollatzResearch.WordTrace tailWord_5097379 prefixEnd_5097379 2617405505134717214920087 := by
  unfold tailWord_5097379
  simp only [CollatzResearch.WordTrace]
  refine ⟨185916685800073920869247191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123944457200049280579498127 185916685800073920869247191)
  ·
    refine ⟨278875028700110881303870787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185916685800073920869247191 278875028700110881303870787)
    ·
      refine ⟨418312543050166321955806181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278875028700110881303870787 418312543050166321955806181)
      ·
        refine ⟨78433601821906185366713659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418312543050166321955806181 78433601821906185366713659)
        ·
          refine ⟨117650402732859278050070489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78433601821906185366713659 117650402732859278050070489)
          ·
            refine ⟨88237802049644458537552867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117650402732859278050070489 88237802049644458537552867)
            ·
              refine ⟨132356703074466687806329301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88237802049644458537552867 132356703074466687806329301)
              ·
                refine ⟨3102110228307812995460843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132356703074466687806329301 3102110228307812995460843)
                ·
                  refine ⟨4653165342461719493191265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102110228307812995460843 4653165342461719493191265)
                  ·
                    refine ⟨3489874006846289619893449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653165342461719493191265 3489874006846289619893449)
                    ·
                      refine ⟨2617405505134717214920087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489874006846289619893449 2617405505134717214920087)
                      ·
                        rfl

theorem cell23_5097379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_5097379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097379 prefixEnd_5097379 := by exact prefixLift 5097379
  have htrace : WordTrace (prefixWord ++ tailWord_5097379) baseStart_5097379 baseEnd_5097379 := by
    simpa [prefixWord, tailWord_5097379, baseEnd_5097379] using wordTrace_append hprefix tailTrace_5097379
  have hstable : (prefixWord ++ tailWord_5097379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097379).length < 2 ^ (prefixWord ++ tailWord_5097379).sum := by decide
  have hdescent : baseEnd_5097379 < baseStart_5097379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097390 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5097390 : Nat := 118140960795 + 5097390 * 2 ^ 59
def prefixEnd_5097390 : Nat := 4983230072969 + 3 ^ 40 * 5097390 * 2
def baseEnd_5097390 : Nat := 2617411153421916671882537

theorem tailTrace_5097390 : CollatzResearch.WordTrace tailWord_5097390 prefixEnd_5097390 2617411153421916671882537 := by
  unfold tailWord_5097390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239635875379258718487203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123944724668689379831931749 23239635875379258718487203)
  ·
    refine ⟨34859453813068888077730805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23239635875379258718487203 34859453813068888077730805)
    ·
      refine ⟨3268073794975208257287263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34859453813068888077730805 3268073794975208257287263)
      ·
        refine ⟨4902110692462812385930895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268073794975208257287263 4902110692462812385930895)
        ·
          refine ⟨7353166038694218578896343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902110692462812385930895 7353166038694218578896343)
          ·
            refine ⟨11029749058041327868344515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353166038694218578896343 11029749058041327868344515)
            ·
              refine ⟨16544623587061991802516773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11029749058041327868344515 16544623587061991802516773)
              ·
                refine ⟨3102116922574123462971895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16544623587061991802516773 3102116922574123462971895)
                ·
                  refine ⟨4653175383861185194457843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102116922574123462971895 4653175383861185194457843)
                  ·
                    refine ⟨6979763075791777791686765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4653175383861185194457843 6979763075791777791686765)
                    ·
                      refine ⟨2617411153421916671882537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979763075791777791686765 2617411153421916671882537)
                      ·
                        rfl

theorem cell23_5097390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5097390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097390 prefixEnd_5097390 := by exact prefixLift 5097390
  have htrace : WordTrace (prefixWord ++ tailWord_5097390) baseStart_5097390 baseEnd_5097390 := by
    simpa [prefixWord, tailWord_5097390, baseEnd_5097390] using wordTrace_append hprefix tailTrace_5097390
  have hstable : (prefixWord ++ tailWord_5097390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097390).length < 2 ^ (prefixWord ++ tailWord_5097390).sum := by decide
  have hdescent : baseEnd_5097390 < baseStart_5097390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097422 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2]
def baseStart_5097422 : Nat := 118140960795 + 5097422 * 2 ^ 59
def prefixEnd_5097422 : Nat := 4983230072969 + 3 ^ 40 * 5097422 * 2
def baseEnd_5097422 : Nat := 2617427584802860546682389

theorem tailTrace_5097422 : CollatzResearch.WordTrace tailWord_5097422 prefixEnd_5097422 2617427584802860546682389 := by
  unfold tailWord_5097422
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239781767364767401632815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123945502759278759475375013 23239781767364767401632815)
  ·
    refine ⟨34859672651047151102449223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23239781767364767401632815 34859672651047151102449223)
    ·
      refine ⟨52289508976570726653673835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34859672651047151102449223 52289508976570726653673835)
      ·
        refine ⟨78434263464856089980510753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52289508976570726653673835 78434263464856089980510753)
        ·
          refine ⟨58825697598642067485383065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78434263464856089980510753 58825697598642067485383065)
          ·
            refine ⟨44119273198981550614037299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58825697598642067485383065 44119273198981550614037299)
            ·
              refine ⟨66178909798472325921055949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44119273198981550614037299 66178909798472325921055949)
              ·
                refine ⟨24817091174427122220395981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66178909798472325921055949 24817091174427122220395981)
                ·
                  refine ⟨9306409190410170832648493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24817091174427122220395981 9306409190410170832648493)
                  ·
                    refine ⟨3489903446403814062243185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9306409190410170832648493 3489903446403814062243185)
                    ·
                      refine ⟨2617427584802860546682389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489903446403814062243185 2617427584802860546682389)
                      ·
                        rfl

theorem cell23_5097422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_5097422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097422 prefixEnd_5097422 := by exact prefixLift 5097422
  have htrace : WordTrace (prefixWord ++ tailWord_5097422) baseStart_5097422 baseEnd_5097422 := by
    simpa [prefixWord, tailWord_5097422, baseEnd_5097422] using wordTrace_append hprefix tailTrace_5097422
  have hstable : (prefixWord ++ tailWord_5097422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097422).length < 2 ^ (prefixWord ++ tailWord_5097422).sum := by decide
  have hdescent : baseEnd_5097422 < baseStart_5097422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097430 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5097430 : Nat := 118140960795 + 5097430 * 2 ^ 59
def prefixEnd_5097430 : Nat := 4983230072969 + 3 ^ 40 * 5097430 * 2
def baseEnd_5097430 : Nat := 2617431692648096515382353

theorem tailTrace_5097430 : CollatzResearch.WordTrace tailWord_5097430 prefixEnd_5097430 2617431692648096515382353 := by
  unfold tailWord_5097430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11619909120180572286209609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123945697281926104386235829 11619909120180572286209609)
  ·
    refine ⟨8714931840135429214657207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11619909120180572286209609 8714931840135429214657207)
    ·
      refine ⟨13072397760203143821985811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8714931840135429214657207 13072397760203143821985811)
      ·
        refine ⟨19608596640304715732978717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13072397760203143821985811 19608596640304715732978717)
        ·
          refine ⟨7353223740114268399867019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19608596640304715732978717 7353223740114268399867019)
          ·
            refine ⟨11029835610171402599800529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353223740114268399867019 11029835610171402599800529)
            ·
              refine ⟨8272376707628551949850397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11029835610171402599800529 8272376707628551949850397)
              ·
                refine ⟨3102141265360706981193899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8272376707628551949850397 3102141265360706981193899)
                ·
                  refine ⟨4653211898041060471790849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102141265360706981193899 4653211898041060471790849)
                  ·
                    refine ⟨3489908923530795353843137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653211898041060471790849 3489908923530795353843137)
                    ·
                      refine ⟨2617431692648096515382353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489908923530795353843137 2617431692648096515382353)
                      ·
                        rfl

theorem cell23_5097430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5097430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097430 prefixEnd_5097430 := by exact prefixLift 5097430
  have htrace : WordTrace (prefixWord ++ tailWord_5097430) baseStart_5097430 baseEnd_5097430 := by
    simpa [prefixWord, tailWord_5097430, baseEnd_5097430] using wordTrace_append hprefix tailTrace_5097430
  have hstable : (prefixWord ++ tailWord_5097430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097430).length < 2 ^ (prefixWord ++ tailWord_5097430).sum := by decide
  have hdescent : baseEnd_5097430 < baseStart_5097430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097439 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 1, 3, 2]
def baseStart_5097439 : Nat := 118140960795 + 5097439 * 2 ^ 59
def prefixEnd_5097439 : Nat := 4983230072969 + 3 ^ 40 * 5097439 * 2
def baseEnd_5097439 : Nat := 2617436313973986980169811

theorem tailTrace_5097439 : CollatzResearch.WordTrace tailWord_5097439 prefixEnd_5097439 2617436313973986980169811 := by
  unfold tailWord_5097439
  simp only [CollatzResearch.WordTrace]
  refine ⟨185918874179856551116431371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123945916119904367410954247 185918874179856551116431371)
  ·
    refine ⟨278878311269784826674647057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185918874179856551116431371 278878311269784826674647057)
    ·
      refine ⟨209158733452338620005985293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278878311269784826674647057 209158733452338620005985293)
      ·
        refine ⟨78434525044626982502244485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209158733452338620005985293 78434525044626982502244485)
        ·
          refine ⟨14706473445867559219170841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78434525044626982502244485 14706473445867559219170841)
          ·
            refine ⟨11029855084400669414378131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14706473445867559219170841 11029855084400669414378131)
            ·
              refine ⟨16544782626601004121567197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11029855084400669414378131 16544782626601004121567197)
              ·
                refine ⟨6204293484975376545587699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16544782626601004121567197 6204293484975376545587699)
                ·
                  refine ⟨9306440227463064818381549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204293484975376545587699 9306440227463064818381549)
                  ·
                    refine ⟨3489915085298649306893081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9306440227463064818381549 3489915085298649306893081)
                    ·
                      refine ⟨2617436313973986980169811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489915085298649306893081 2617436313973986980169811)
                      ·
                        rfl

theorem cell23_5097439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_5097439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097439 prefixEnd_5097439 := by exact prefixLift 5097439
  have htrace : WordTrace (prefixWord ++ tailWord_5097439) baseStart_5097439 baseEnd_5097439 := by
    simpa [prefixWord, tailWord_5097439, baseEnd_5097439] using wordTrace_append hprefix tailTrace_5097439
  have hstable : (prefixWord ++ tailWord_5097439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097439).length < 2 ^ (prefixWord ++ tailWord_5097439).sum := by decide
  have hdescent : baseEnd_5097439 < baseStart_5097439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097465 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_5097465 : Nat := 118140960795 + 5097465 * 2 ^ 59
def prefixEnd_5097465 : Nat := 4983230072969 + 3 ^ 40 * 5097465 * 2
def baseEnd_5097465 : Nat := 2617449664471003878444691

theorem tailTrace_5097465 : CollatzResearch.WordTrace tailWord_5097465 prefixEnd_5097465 2617449664471003878444691 := by
  unfold tailWord_5097465
  simp only [CollatzResearch.WordTrace]
  refine ⟨185919822477762357556877849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123946548318508238371251899 185919822477762357556877849)
  ·
    refine ⟨139439866858321768167658387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185919822477762357556877849 139439866858321768167658387)
    ·
      refine ⟨209159800287482652251487581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139439866858321768167658387 209159800287482652251487581)
      ·
        refine ⟨78434925107805994594307843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209159800287482652251487581 78434925107805994594307843)
        ·
          refine ⟨117652387661708991891461765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78434925107805994594307843 117652387661708991891461765)
          ·
            refine ⟨22059822686570435979649081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117652387661708991891461765 22059822686570435979649081)
            ·
              refine ⟨16544867014927826984736811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22059822686570435979649081 16544867014927826984736811)
              ·
                refine ⟨24817300522391740477105217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16544867014927826984736811 24817300522391740477105217)
                ·
                  refine ⟨18612975391793805357828913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24817300522391740477105217 18612975391793805357828913)
                  ·
                    refine ⟨13959731543845354018371685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18612975391793805357828913 13959731543845354018371685)
                    ·
                      refine ⟨2617449664471003878444691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13959731543845354018371685 2617449664471003878444691)
                      ·
                        rfl

theorem cell23_5097465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_5097465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097465 prefixEnd_5097465 := by exact prefixLift 5097465
  have htrace : WordTrace (prefixWord ++ tailWord_5097465) baseStart_5097465 baseEnd_5097465 := by
    simpa [prefixWord, tailWord_5097465, baseEnd_5097465] using wordTrace_append hprefix tailTrace_5097465
  have hstable : (prefixWord ++ tailWord_5097465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097465).length < 2 ^ (prefixWord ++ tailWord_5097465).sum := by decide
  have hdescent : baseEnd_5097465 < baseStart_5097465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097469 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 2, 2, 2]
def baseStart_5097469 : Nat := 118140960795 + 5097469 * 2 ^ 59
def prefixEnd_5097469 : Nat := 4983230072969 + 3 ^ 40 * 5097469 * 2
def baseEnd_5097469 : Nat := 2617451718393621862794673

theorem tailTrace_5097469 : CollatzResearch.WordTrace tailWord_5097469 prefixEnd_5097469 2617451718393621862794673 := by
  unfold tailWord_5097469
  simp only [CollatzResearch.WordTrace]
  refine ⟨185919968369747866240023461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123946645579831910826682307 185919968369747866240023461)
  ·
    refine ⟨34859994069327724920004399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185919968369747866240023461 34859994069327724920004399)
    ·
      refine ⟨52289991103991587380006599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34859994069327724920004399 52289991103991587380006599)
      ·
        refine ⟨78434986655987381070009899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52289991103991587380006599 78434986655987381070009899)
        ·
          refine ⟨117652479983981071605014849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78434986655987381070009899 117652479983981071605014849)
          ·
            refine ⟨88239359987985803703761137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117652479983981071605014849 88239359987985803703761137)
            ·
              refine ⟨66179519990989352777820853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88239359987985803703761137 66179519990989352777820853)
              ·
                refine ⟨6204329999155251822920705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66179519990989352777820853 6204329999155251822920705)
                ·
                  refine ⟨4653247499366438867190529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204329999155251822920705 4653247499366438867190529)
                  ·
                    refine ⟨3489935624524829150392897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653247499366438867190529 3489935624524829150392897)
                    ·
                      refine ⟨2617451718393621862794673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3489935624524829150392897 2617451718393621862794673)
                      ·
                        rfl

theorem cell23_5097469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_5097469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097469 prefixEnd_5097469 := by exact prefixLift 5097469
  have htrace : WordTrace (prefixWord ++ tailWord_5097469) baseStart_5097469 baseEnd_5097469 := by
    simpa [prefixWord, tailWord_5097469, baseEnd_5097469] using wordTrace_append hprefix tailTrace_5097469
  have hstable : (prefixWord ++ tailWord_5097469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097469).length < 2 ^ (prefixWord ++ tailWord_5097469).sum := by decide
  have hdescent : baseEnd_5097469 < baseStart_5097469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097509 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 5]
def baseStart_5097509 : Nat := 118140960795 + 5097509 * 2 ^ 59
def prefixEnd_5097509 : Nat := 4983230072969 + 3 ^ 40 * 5097509 * 2
def baseEnd_5097509 : Nat := 290830250846644634032721

theorem tailTrace_5097509 : CollatzResearch.WordTrace tailWord_5097509 prefixEnd_5097509 290830250846644634032721 := by
  unfold tailWord_5097509
  simp only [CollatzResearch.WordTrace]
  refine ⟨185921427289602953071479581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123947618193068635380986387 185921427289602953071479581)
  ·
    refine ⟨69720535233601107401804843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185921427289602953071479581 69720535233601107401804843)
    ·
      refine ⟨104580802850401661102707265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69720535233601107401804843 104580802850401661102707265)
      ·
        refine ⟨78435602137801245827030449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104580802850401661102707265 78435602137801245827030449)
        ·
          refine ⟨58826701603350934370272837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78435602137801245827030449 58826701603350934370272837)
          ·
            refine ⟨11030006550628300194426157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58826701603350934370272837 11030006550628300194426157)
            ·
              refine ⟨4136252456485612572909809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11030006550628300194426157 4136252456485612572909809)
              ·
                refine ⟨3102189342364209429682357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136252456485612572909809 3102189342364209429682357)
                ·
                  refine ⟨290830250846644634032721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102189342364209429682357 290830250846644634032721)
                  ·
                    rfl

theorem cell23_5097509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_5097509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097509 prefixEnd_5097509 := by exact prefixLift 5097509
  have htrace : WordTrace (prefixWord ++ tailWord_5097509) baseStart_5097509 baseEnd_5097509 := by
    simpa [prefixWord, tailWord_5097509, baseEnd_5097509] using wordTrace_append hprefix tailTrace_5097509
  have hstable : (prefixWord ++ tailWord_5097509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097509).length < 2 ^ (prefixWord ++ tailWord_5097509).sum := by decide
  have hdescent : baseEnd_5097509 < baseStart_5097509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097525 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5097525 : Nat := 118140960795 + 5097525 * 2 ^ 59
def prefixEnd_5097525 : Nat := 4983230072969 + 3 ^ 40 * 5097525 * 2
def baseEnd_5097525 : Nat := 2617480473310273643694415

theorem tailTrace_5097525 : CollatzResearch.WordTrace tailWord_5097525 prefixEnd_5097525 2617480473310273643694415 := by
  unfold tailWord_5097525
  simp only [CollatzResearch.WordTrace]
  refine ⟨185922010857544987804062029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123948007238363325202708019 185922010857544987804062029)
  ·
    refine ⟨69720754071579370426523261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185922010857544987804062029 69720754071579370426523261)
    ·
      refine ⟨26145282776842263909946223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69720754071579370426523261 26145282776842263909946223)
      ·
        refine ⟨39217924165263395864919335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26145282776842263909946223 39217924165263395864919335)
        ·
          refine ⟨58826886247895093797379003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39217924165263395864919335 58826886247895093797379003)
          ·
            refine ⟨88240329371842640696068505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58826886247895093797379003 88240329371842640696068505)
            ·
              refine ⟨66180247028881980522051379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88240329371842640696068505 66180247028881980522051379)
              ·
                refine ⟨99270370543322970783077069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66180247028881980522051379 99270370543322970783077069)
                ·
                  refine ⟨37226388953746114043653901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99270370543322970783077069 37226388953746114043653901)
                  ·
                    refine ⟨13959895857654792766370213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37226388953746114043653901 13959895857654792766370213)
                    ·
                      refine ⟨2617480473310273643694415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13959895857654792766370213 2617480473310273643694415)
                      ·
                        rfl

theorem cell23_5097525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5097525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097525 prefixEnd_5097525 := by exact prefixLift 5097525
  have htrace : WordTrace (prefixWord ++ tailWord_5097525) baseStart_5097525 baseEnd_5097525 := by
    simpa [prefixWord, tailWord_5097525, baseEnd_5097525] using wordTrace_append hprefix tailTrace_5097525
  have hstable : (prefixWord ++ tailWord_5097525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097525).length < 2 ^ (prefixWord ++ tailWord_5097525).sum := by decide
  have hdescent : baseEnd_5097525 < baseStart_5097525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097562 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_5097562 : Nat := 118140960795 + 5097562 * 2 ^ 59
def prefixEnd_5097562 : Nat := 4983230072969 + 3 ^ 40 * 5097562 * 2
def baseEnd_5097562 : Nat := 2617499472094489998931745

theorem tailTrace_5097562 : CollatzResearch.WordTrace tailWord_5097562 prefixEnd_5097562 2617499472094489998931745 := by
  unfold tailWord_5097562
  simp only [CollatzResearch.WordTrace]
  refine ⟨46480840089602735780789735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123948906905607295415439293 46480840089602735780789735)
  ·
    refine ⟨69721260134404103671184603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46480840089602735780789735 69721260134404103671184603)
    ·
      refine ⟨104581890201606155506776905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69721260134404103671184603 104581890201606155506776905)
      ·
        refine ⟨78436417651204616630082679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104581890201606155506776905 78436417651204616630082679)
        ·
          refine ⟨117654626476806924945124019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78436417651204616630082679 117654626476806924945124019)
          ·
            refine ⟨176481939715210387417686029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117654626476806924945124019 176481939715210387417686029)
            ·
              refine ⟨66180727393203895281632261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176481939715210387417686029 66180727393203895281632261)
              ·
                refine ⟨12408886386225730365306049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66180727393203895281632261 12408886386225730365306049)
                ·
                  refine ⟨9306664789669297773979537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12408886386225730365306049 9306664789669297773979537)
                  ·
                    refine ⟨6979998592251973330484653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9306664789669297773979537 6979998592251973330484653)
                    ·
                      refine ⟨2617499472094489998931745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6979998592251973330484653 2617499472094489998931745)
                      ·
                        rfl

theorem cell23_5097562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_5097562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097562 prefixEnd_5097562 := by exact prefixLift 5097562
  have htrace : WordTrace (prefixWord ++ tailWord_5097562) baseStart_5097562 baseEnd_5097562 := by
    simpa [prefixWord, tailWord_5097562, baseEnd_5097562] using wordTrace_append hprefix tailTrace_5097562
  have hstable : (prefixWord ++ tailWord_5097562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097562).length < 2 ^ (prefixWord ++ tailWord_5097562).sum := by decide
  have hdescent : baseEnd_5097562 < baseStart_5097562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097582 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_5097582 : Nat := 118140960795 + 5097582 * 2 ^ 59
def prefixEnd_5097582 : Nat := 4983230072969 + 3 ^ 40 * 5097582 * 2
def baseEnd_5097582 : Nat := 290834415745286657853517

theorem tailTrace_5097582 : CollatzResearch.WordTrace tailWord_5097582 prefixEnd_5097582 290834415745286657853517 := by
  unfold tailWord_5097582
  simp only [CollatzResearch.WordTrace]
  refine ⟨23240511227292310817360875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123949393212225657692591333 23240511227292310817360875)
  ·
    refine ⟨34860766840938466226041313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23240511227292310817360875 34860766840938466226041313)
    ·
      refine ⟨26145575130703849669530985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34860766840938466226041313 26145575130703849669530985)
      ·
        refine ⟨19609181348027887252148239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26145575130703849669530985 19609181348027887252148239)
        ·
          refine ⟨29413772022041830878222359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19609181348027887252148239 29413772022041830878222359)
          ·
            refine ⟨44120658033062746317333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29413772022041830878222359 44120658033062746317333539)
            ·
              refine ⟨66180987049594119476000309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44120658033062746317333539 66180987049594119476000309)
              ·
                refine ⟨6204467535899448700875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66180987049594119476000309 6204467535899448700875029)
                ·
                  refine ⟨290834415745286657853517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6204467535899448700875029 290834415745286657853517)
                  ·
                    rfl

theorem cell23_5097582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_5097582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097582 prefixEnd_5097582 := by exact prefixLift 5097582
  have htrace : WordTrace (prefixWord ++ tailWord_5097582) baseStart_5097582 baseEnd_5097582 := by
    simpa [prefixWord, tailWord_5097582, baseEnd_5097582] using wordTrace_append hprefix tailTrace_5097582
  have hstable : (prefixWord ++ tailWord_5097582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097582).length < 2 ^ (prefixWord ++ tailWord_5097582).sum := by decide
  have hdescent : baseEnd_5097582 < baseStart_5097582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097625 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_5097625 : Nat := 118140960795 + 5097625 * 2 ^ 59
def prefixEnd_5097625 : Nat := 4983230072969 + 3 ^ 40 * 5097625 * 2
def baseEnd_5097625 : Nat := 872510607125241084147985

theorem tailTrace_5097625 : CollatzResearch.WordTrace tailWord_5097625 prefixEnd_5097625 872510607125241084147985 := by
  unfold tailWord_5097625
  simp only [CollatzResearch.WordTrace]
  refine ⟨185925658157182704882702329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123950438771455136588468219 185925658157182704882702329)
  ·
    refine ⟨139444243617887028662026747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185925658157182704882702329 139444243617887028662026747)
    ·
      refine ⟨209166365426830542993040121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139444243617887028662026747 209166365426830542993040121)
      ·
        refine ⟨156874774070122907244780091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209166365426830542993040121 156874774070122907244780091)
        ·
          refine ⟨235312161105184360867170137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156874774070122907244780091 235312161105184360867170137)
          ·
            refine ⟨176484120828888270650377603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235312161105184360867170137 176484120828888270650377603)
            ·
              refine ⟨264726181243332405975566405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176484120828888270650377603 264726181243332405975566405)
              ·
                refine ⟨49636158983124826120418701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264726181243332405975566405 49636158983124826120418701)
                ·
                  refine ⟨18613559618671809795157013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49636158983124826120418701 18613559618671809795157013)
                  ·
                    refine ⟨872510607125241084147985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18613559618671809795157013 872510607125241084147985)
                    ·
                      rfl

theorem cell23_5097625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_5097625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097625 prefixEnd_5097625 := by exact prefixLift 5097625
  have htrace : WordTrace (prefixWord ++ tailWord_5097625) baseStart_5097625 baseEnd_5097625 := by
    simpa [prefixWord, tailWord_5097625, baseEnd_5097625] using wordTrace_append hprefix tailTrace_5097625
  have hstable : (prefixWord ++ tailWord_5097625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097625).length < 2 ^ (prefixWord ++ tailWord_5097625).sum := by decide
  have hdescent : baseEnd_5097625 < baseStart_5097625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097660 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_5097660 : Nat := 118140960795 + 5097660 * 2 ^ 59
def prefixEnd_5097660 : Nat := 4983230072969 + 3 ^ 40 * 5097660 * 2
def baseEnd_5097660 : Nat := 2617549793198630615506295

theorem tailTrace_5097660 : CollatzResearch.WordTrace tailWord_5097660 prefixEnd_5097660 2617549793198630615506295 := by
  unfold tailWord_5097660
  simp only [CollatzResearch.WordTrace]
  refine ⟨92963467356027952930113217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123951289808037270573484289 92963467356027952930113217)
  ·
    refine ⟨69722600517020964697584913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92963467356027952930113217 69722600517020964697584913)
    ·
      refine ⟨52291950387765723523188685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69722600517020964697584913 52291950387765723523188685)
      ·
        refine ⟨19609481395412146321195757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52291950387765723523188685 19609481395412146321195757)
        ·
          refine ⟨7353555523279554870448409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19609481395412146321195757 7353555523279554870448409)
          ·
            refine ⟨5515166642459666152836307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7353555523279554870448409 5515166642459666152836307)
            ·
              refine ⟨8272749963689499229254461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515166642459666152836307 8272749963689499229254461)
              ·
                refine ⟨3102281236383562210970423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8272749963689499229254461 3102281236383562210970423)
                ·
                  refine ⟨4653421854575343316455635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102281236383562210970423 4653421854575343316455635)
                  ·
                    refine ⟨6980132781863014974683453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4653421854575343316455635 6980132781863014974683453)
                    ·
                      refine ⟨2617549793198630615506295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980132781863014974683453 2617549793198630615506295)
                      ·
                        rfl

theorem cell23_5097660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_5097660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097660 prefixEnd_5097660 := by exact prefixLift 5097660
  have htrace : WordTrace (prefixWord ++ tailWord_5097660) baseStart_5097660 baseEnd_5097660 := by
    simpa [prefixWord, tailWord_5097660, baseEnd_5097660] using wordTrace_append hprefix tailTrace_5097660
  have hstable : (prefixWord ++ tailWord_5097660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097660).length < 2 ^ (prefixWord ++ tailWord_5097660).sum := by decide
  have hdescent : baseEnd_5097660 < baseStart_5097660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097669 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_5097669 : Nat := 118140960795 + 5097669 * 2 ^ 59
def prefixEnd_5097669 : Nat := 4983230072969 + 3 ^ 40 * 5097669 * 2
def baseEnd_5097669 : Nat := 2617554414524521080293753

theorem tailTrace_5097669 : CollatzResearch.WordTrace tailWord_5097669 prefixEnd_5097669 2617554414524521080293753 := by
  unfold tailWord_5097669
  simp only [CollatzResearch.WordTrace]
  refine ⟨185927262969023300397304061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123951508646015533598202707 185927262969023300397304061)
  ·
    refine ⟨69722723613383737648989023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185927262969023300397304061 69722723613383737648989023)
    ·
      refine ⟨104584085420075606473483535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69722723613383737648989023 104584085420075606473483535)
      ·
        refine ⟨156876128130113409710225303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104584085420075606473483535 156876128130113409710225303)
        ·
          refine ⟨235314192195170114565337955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156876128130113409710225303 235314192195170114565337955)
          ·
            refine ⟨352971288292755171848006933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235314192195170114565337955 352971288292755171848006933)
            ·
              refine ⟨16545529138722898680375325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 352971288292755171848006933 16545529138722898680375325)
              ·
                refine ⟨6204573427021087005140747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16545529138722898680375325 6204573427021087005140747)
                ·
                  refine ⟨9306860140531630507711121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204573427021087005140747 9306860140531630507711121)
                  ·
                    refine ⟨6980145105398722880783341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9306860140531630507711121 6980145105398722880783341)
                    ·
                      refine ⟨2617554414524521080293753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980145105398722880783341 2617554414524521080293753)
                      ·
                        rfl

theorem cell23_5097669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_5097669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097669 prefixEnd_5097669 := by exact prefixLift 5097669
  have htrace : WordTrace (prefixWord ++ tailWord_5097669) baseStart_5097669 baseEnd_5097669 := by
    simpa [prefixWord, tailWord_5097669, baseEnd_5097669] using wordTrace_append hprefix tailTrace_5097669
  have hstable : (prefixWord ++ tailWord_5097669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097669).length < 2 ^ (prefixWord ++ tailWord_5097669).sum := by decide
  have hdescent : baseEnd_5097669 < baseStart_5097669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097686 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5097686 : Nat := 118140960795 + 5097686 * 2 ^ 59
def prefixEnd_5097686 : Nat := 4983230072969 + 3 ^ 40 * 5097686 * 2
def baseEnd_5097686 : Nat := 2617563143695647513781175

theorem tailTrace_5097686 : CollatzResearch.WordTrace tailWord_5097686 prefixEnd_5097686 2617563143695647513781175 := by
  unfold tailWord_5097686
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620492688122607018792057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123951922006641141533781941 11620492688122607018792057)
  ·
    refine ⟨8715369516091955264094043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11620492688122607018792057 8715369516091955264094043)
    ·
      refine ⟨13073054274137932896141065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715369516091955264094043 13073054274137932896141065)
      ·
        refine ⟨9804790705603449672105799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13073054274137932896141065 9804790705603449672105799)
        ·
          refine ⟨14707186058405174508158699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804790705603449672105799 14707186058405174508158699)
          ·
            refine ⟨22060779087607761762238049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14707186058405174508158699 22060779087607761762238049)
            ·
              refine ⟨16545584315705821321678537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22060779087607761762238049 16545584315705821321678537)
              ·
                refine ⟨12409188236779365991258903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16545584315705821321678537 12409188236779365991258903)
                ·
                  refine ⟨18613782355169048986888355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12409188236779365991258903 18613782355169048986888355)
                  ·
                    refine ⟨27920673532753573480332533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18613782355169048986888355 27920673532753573480332533)
                    ·
                      refine ⟨2617563143695647513781175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27920673532753573480332533 2617563143695647513781175)
                      ·
                        rfl

theorem cell23_5097686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5097686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097686 prefixEnd_5097686 := by exact prefixLift 5097686
  have htrace : WordTrace (prefixWord ++ tailWord_5097686) baseStart_5097686 baseEnd_5097686 := by
    simpa [prefixWord, tailWord_5097686, baseEnd_5097686] using wordTrace_append hprefix tailTrace_5097686
  have hstable : (prefixWord ++ tailWord_5097686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097686).length < 2 ^ (prefixWord ++ tailWord_5097686).sum := by decide
  have hdescent : baseEnd_5097686 < baseStart_5097686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097693 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5097693 : Nat := 118140960795 + 5097693 * 2 ^ 59
def prefixEnd_5097693 : Nat := 4983230072969 + 3 ^ 40 * 5097693 * 2
def baseEnd_5097693 : Nat := 872522246020076328797881

theorem tailTrace_5097693 : CollatzResearch.WordTrace tailWord_5097693 prefixEnd_5097693 872522246020076328797881 := by
  unfold tailWord_5097693
  simp only [CollatzResearch.WordTrace]
  refine ⟨185928138320936352496177733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123952092213957568330785155 185928138320936352496177733)
  ·
    refine ⟨34861525935175566093033325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185928138320936352496177733 34861525935175566093033325)
    ·
      refine ⟨13073072225690837284887497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34861525935175566093033325 13073072225690837284887497)
      ·
        refine ⟨9804804169268127963665623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13073072225690837284887497 9804804169268127963665623)
        ·
          refine ⟨14707206253902191945498435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804804169268127963665623 14707206253902191945498435)
          ·
            refine ⟨22060809380853287918247653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14707206253902191945498435 22060809380853287918247653)
            ·
              refine ⟨4136401758909991484671435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22060809380853287918247653 4136401758909991484671435)
              ·
                refine ⟨6204602638364987227007153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136401758909991484671435 6204602638364987227007153)
                ·
                  refine ⟨4653451978773740420255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204602638364987227007153 4653451978773740420255365)
                  ·
                    refine ⟨872522246020076328797881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653451978773740420255365 872522246020076328797881)
                    ·
                      rfl

theorem cell23_5097693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5097693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097693 prefixEnd_5097693 := by exact prefixLift 5097693
  have htrace : WordTrace (prefixWord ++ tailWord_5097693) baseStart_5097693 baseEnd_5097693 := by
    simpa [prefixWord, tailWord_5097693, baseEnd_5097693] using wordTrace_append hprefix tailTrace_5097693
  have hstable : (prefixWord ++ tailWord_5097693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097693).length < 2 ^ (prefixWord ++ tailWord_5097693).sum := by decide
  have hdescent : baseEnd_5097693 < baseStart_5097693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097703 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5097703 : Nat := 118140960795 + 5097703 * 2 ^ 59
def prefixEnd_5097703 : Nat := 4983230072969 + 3 ^ 40 * 5097703 * 2
def baseEnd_5097703 : Nat := 2617571872866773947268597

theorem tailTrace_5097703 : CollatzResearch.WordTrace tailWord_5097703 prefixEnd_5097703 2617571872866773947268597 := by
  unfold tailWord_5097703
  simp only [CollatzResearch.WordTrace]
  refine ⟨185928503050900124204041763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123952335367266749469361175 185928503050900124204041763)
  ·
    refine ⟨278892754576350186306062645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185928503050900124204041763 278892754576350186306062645)
    ·
      refine ⟨26146195741532829966193373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278892754576350186306062645 26146195741532829966193373)
      ·
        refine ⟨9804823403074811237322515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26146195741532829966193373 9804823403074811237322515)
        ·
          refine ⟨14707235104612216855983773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804823403074811237322515 14707235104612216855983773)
          ·
            refine ⟨5515213164229581320993915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14707235104612216855983773 5515213164229581320993915)
            ·
              refine ⟨8272819746344371981490873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515213164229581320993915 8272819746344371981490873)
              ·
                refine ⟨6204614809758278986118155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8272819746344371981490873 6204614809758278986118155)
                ·
                  refine ⟨9306922214637418479177233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204614809758278986118155 9306922214637418479177233)
                  ·
                    refine ⟨6980191660978063859382925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9306922214637418479177233 6980191660978063859382925)
                    ·
                      refine ⟨2617571872866773947268597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980191660978063859382925 2617571872866773947268597)
                      ·
                        rfl

theorem cell23_5097703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5097703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097703 prefixEnd_5097703 := by exact prefixLift 5097703
  have htrace : WordTrace (prefixWord ++ tailWord_5097703) baseStart_5097703 baseEnd_5097703 := by
    simpa [prefixWord, tailWord_5097703, baseEnd_5097703] using wordTrace_append hprefix tailTrace_5097703
  have hstable : (prefixWord ++ tailWord_5097703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097703).length < 2 ^ (prefixWord ++ tailWord_5097703).sum := by decide
  have hdescent : baseEnd_5097703 < baseStart_5097703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097739 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 4, 2]
def baseStart_5097739 : Nat := 118140960795 + 5097739 * 2 ^ 59
def prefixEnd_5097739 : Nat := 4983230072969 + 3 ^ 40 * 5097739 * 2
def baseEnd_5097739 : Nat := 2617590358170335806418431

theorem tailTrace_5097739 : CollatzResearch.WordTrace tailWord_5097739 prefixEnd_5097739 2617590358170335806418431 := by
  unfold tailWord_5097739
  simp only [CollatzResearch.WordTrace]
  refine ⟨185929816078769702352352271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123953210719179801568234847 185929816078769702352352271)
  ·
    refine ⟨278894724118154553528528407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185929816078769702352352271 278894724118154553528528407)
    ·
      refine ⟨418342086177231830292792611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278894724118154553528528407 418342086177231830292792611)
      ·
        refine ⟨627513129265847745439188917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418342086177231830292792611 627513129265847745439188917)
        ·
          refine ⟨58829355868673226134923961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 627513129265847745439188917 58829355868673226134923961)
          ·
            refine ⟨44122016901504919601192971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58829355868673226134923961 44122016901504919601192971)
            ·
              refine ⟨66183025352257379401789457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44122016901504919601192971 66183025352257379401789457)
              ·
                refine ⟨49637269014193034551342093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66183025352257379401789457 49637269014193034551342093)
                ·
                  refine ⟨18613975880322387956753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49637269014193034551342093 18613975880322387956753285)
                  ·
                    refine ⟨3490120477560447741891241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18613975880322387956753285 3490120477560447741891241)
                    ·
                      refine ⟨2617590358170335806418431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490120477560447741891241 2617590358170335806418431)
                      ·
                        rfl

theorem cell23_5097739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 4, 2].length) (baseStart_5097739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097739 prefixEnd_5097739 := by exact prefixLift 5097739
  have htrace : WordTrace (prefixWord ++ tailWord_5097739) baseStart_5097739 baseEnd_5097739 := by
    simpa [prefixWord, tailWord_5097739, baseEnd_5097739] using wordTrace_append hprefix tailTrace_5097739
  have hstable : (prefixWord ++ tailWord_5097739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097739).length < 2 ^ (prefixWord ++ tailWord_5097739).sum := by decide
  have hdescent : baseEnd_5097739 < baseStart_5097739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097756 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_5097756 : Nat := 118140960795 + 5097756 * 2 ^ 59
def prefixEnd_5097756 : Nat := 4983230072969 + 3 ^ 40 * 5097756 * 2
def baseEnd_5097756 : Nat := 2617599087341462239905853

theorem tailTrace_5097756 : CollatzResearch.WordTrace tailWord_5097756 prefixEnd_5097756 2617599087341462239905853 := by
  unfold tailWord_5097756
  simp only [CollatzResearch.WordTrace]
  refine ⟨92965218059854057127860561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123953624079805409503814081 92965218059854057127860561)
  ·
    refine ⟨69723913544890542845895421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92965218059854057127860561 69723913544890542845895421)
    ·
      refine ⟨26146467579333953567210783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69723913544890542845895421 26146467579333953567210783)
      ·
        refine ⟨39219701369000930350816175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26146467579333953567210783 39219701369000930350816175)
        ·
          refine ⟨58829552053501395526224263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39219701369000930350816175 58829552053501395526224263)
          ·
            refine ⟨88244328080252093289336395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58829552053501395526224263 88244328080252093289336395)
            ·
              refine ⟨132366492120378139934004593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88244328080252093289336395 132366492120378139934004593)
              ·
                refine ⟨99274869090283604950503445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132366492120378139934004593 99274869090283604950503445)
                ·
                  refine ⟨4653509488607043982054849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99274869090283604950503445 4653509488607043982054849)
                  ·
                    refine ⟨3490132116455282986541137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653509488607043982054849 3490132116455282986541137)
                    ·
                      refine ⟨2617599087341462239905853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490132116455282986541137 2617599087341462239905853)
                      ·
                        rfl

theorem cell23_5097756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_5097756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097756 prefixEnd_5097756 := by exact prefixLift 5097756
  have htrace : WordTrace (prefixWord ++ tailWord_5097756) baseStart_5097756 baseEnd_5097756 := by
    simpa [prefixWord, tailWord_5097756, baseEnd_5097756] using wordTrace_append hprefix tailTrace_5097756
  have hstable : (prefixWord ++ tailWord_5097756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097756).length < 2 ^ (prefixWord ++ tailWord_5097756).sum := by decide
  have hdescent : baseEnd_5097756 < baseStart_5097756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097777 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5097777 : Nat := 118140960795 + 5097777 * 2 ^ 59
def prefixEnd_5097777 : Nat := 4983230072969 + 3 ^ 40 * 5097777 * 2
def baseEnd_5097777 : Nat := 2617609870435206657743257

theorem tailTrace_5097777 : CollatzResearch.WordTrace tailWord_5097777 prefixEnd_5097777 2617609870435206657743257 := by
  unfold tailWord_5097777
  simp only [CollatzResearch.WordTrace]
  refine ⟨185931202052632034842235585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123954134701754689894823723 185931202052632034842235585)
  ·
    refine ⟨139448401539474026131676689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185931202052632034842235585 139448401539474026131676689)
    ·
      refine ⟨104586301154605519598757517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139448401539474026131676689 104586301154605519598757517)
      ·
        refine ⟨39219862932977069849534069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104586301154605519598757517 39219862932977069849534069)
        ·
          refine ⟨3676862149966600298393819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39219862932977069849534069 3676862149966600298393819)
          ·
            refine ⟨5515293224949900447590729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676862149966600298393819 5515293224949900447590729)
            ·
              refine ⟨4136469918712425335693047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5515293224949900447590729 4136469918712425335693047)
              ·
                refine ⟨6204704878068638003539571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136469918712425335693047 6204704878068638003539571)
                ·
                  refine ⟨9307057317102957005309357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204704878068638003539571 9307057317102957005309357)
                  ·
                    refine ⟨3490146493913608876991009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9307057317102957005309357 3490146493913608876991009)
                    ·
                      refine ⟨2617609870435206657743257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490146493913608876991009 2617609870435206657743257)
                      ·
                        rfl

theorem cell23_5097777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5097777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097777 prefixEnd_5097777 := by exact prefixLift 5097777
  have htrace : WordTrace (prefixWord ++ tailWord_5097777) baseStart_5097777 baseEnd_5097777 := by
    simpa [prefixWord, tailWord_5097777, baseEnd_5097777] using wordTrace_append hprefix tailTrace_5097777
  have hstable : (prefixWord ++ tailWord_5097777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097777).length < 2 ^ (prefixWord ++ tailWord_5097777).sum := by decide
  have hdescent : baseEnd_5097777 < baseStart_5097777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097790 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5097790 : Nat := 118140960795 + 5097790 * 2 ^ 59
def prefixEnd_5097790 : Nat := 4983230072969 + 3 ^ 40 * 5097790 * 2
def baseEnd_5097790 : Nat := 2617616545683715106880697

theorem tailTrace_5097790 : CollatzResearch.WordTrace tailWord_5097790 prefixEnd_5097790 2617616545683715106880697 := by
  unfold tailWord_5097790
  simp only [CollatzResearch.WordTrace]
  refine ⟨23241459525198117257807353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123954450801056625374972549 23241459525198117257807353)
  ·
    refine ⟨17431094643898587943355515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23241459525198117257807353 17431094643898587943355515)
    ·
      refine ⟨26146641965847881915033273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17431094643898587943355515 26146641965847881915033273)
      ·
        refine ⟨19609981474385911436274955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26146641965847881915033273 19609981474385911436274955)
        ·
          refine ⟨29414972211578867154412433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19609981474385911436274955 29414972211578867154412433)
          ·
            refine ⟨22061229158684150365809325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29414972211578867154412433 22061229158684150365809325)
            ·
              refine ⟨8272960934506556387178497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22061229158684150365809325 8272960934506556387178497)
              ·
                refine ⟨6204720700879917290383873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8272960934506556387178497 6204720700879917290383873)
                ·
                  refine ⟨4653540525659937967787905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204720700879917290383873 4653540525659937967787905)
                  ·
                    refine ⟨3490155394244953475840929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653540525659937967787905 3490155394244953475840929)
                    ·
                      refine ⟨2617616545683715106880697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490155394244953475840929 2617616545683715106880697)
                      ·
                        rfl

theorem cell23_5097790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5097790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097790 prefixEnd_5097790 := by exact prefixLift 5097790
  have htrace : WordTrace (prefixWord ++ tailWord_5097790) baseStart_5097790 baseEnd_5097790 := by
    simpa [prefixWord, tailWord_5097790, baseEnd_5097790] using wordTrace_append hprefix tailTrace_5097790
  have hstable : (prefixWord ++ tailWord_5097790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097790).length < 2 ^ (prefixWord ++ tailWord_5097790).sum := by decide
  have hdescent : baseEnd_5097790 < baseStart_5097790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097829 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5097829 : Nat := 118140960795 + 5097829 * 2 ^ 59
def prefixEnd_5097829 : Nat := 4983230072969 + 3 ^ 40 * 5097829 * 2
def baseEnd_5097829 : Nat := 2617636571429240454293017

theorem tailTrace_5097829 : CollatzResearch.WordTrace tailWord_5097829 prefixEnd_5097829 2617636571429240454293017 := by
  unfold tailWord_5097829
  simp only [CollatzResearch.WordTrace]
  refine ⟨185933098648443647723128541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123955399098962431815419027 185933098648443647723128541)
  ·
    refine ⟨69724911993166367896173203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185933098648443647723128541 69724911993166367896173203)
    ·
      refine ⟨104587367989749551844259805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69724911993166367896173203 104587367989749551844259805)
      ·
        refine ⟨39220262996156081941597427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104587367989749551844259805 39220262996156081941597427)
        ·
          refine ⟨58830394494234122912396141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39220262996156081941597427 58830394494234122912396141)
          ·
            refine ⟨22061397935337796092148553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58830394494234122912396141 22061397935337796092148553)
            ·
              refine ⟨16546048451503347069111415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22061397935337796092148553 16546048451503347069111415)
              ·
                refine ⟨24819072677255020603667123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16546048451503347069111415 24819072677255020603667123)
                ·
                  refine ⟨37228609015882530905500685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24819072677255020603667123 37228609015882530905500685)
                  ·
                    refine ⟨13960728380955949089562757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37228609015882530905500685 13960728380955949089562757)
                    ·
                      refine ⟨2617636571429240454293017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13960728380955949089562757 2617636571429240454293017)
                      ·
                        rfl

theorem cell23_5097829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5097829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097829 prefixEnd_5097829 := by exact prefixLift 5097829
  have htrace : WordTrace (prefixWord ++ tailWord_5097829) baseStart_5097829 baseEnd_5097829 := by
    simpa [prefixWord, tailWord_5097829, baseEnd_5097829] using wordTrace_append hprefix tailTrace_5097829
  have hstable : (prefixWord ++ tailWord_5097829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097829).length < 2 ^ (prefixWord ++ tailWord_5097829).sum := by decide
  have hdescent : baseEnd_5097829 < baseStart_5097829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097879 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_5097879 : Nat := 118140960795 + 5097879 * 2 ^ 59
def prefixEnd_5097879 : Nat := 4983230072969 + 3 ^ 40 * 5097879 * 2
def baseEnd_5097879 : Nat := 2617662245461965258667787

theorem tailTrace_5097879 : CollatzResearch.WordTrace tailWord_5097879 prefixEnd_5097879 2617662245461965258667787 := by
  unfold tailWord_5097879
  simp only [CollatzResearch.WordTrace]
  refine ⟨185934922298262506262448691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123956614865508337508299127 185934922298262506262448691)
  ·
    refine ⟨278902383447393759393673037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185934922298262506262448691 278902383447393759393673037)
    ·
      refine ⟨104588393792772659772627389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278902383447393759393673037 104588393792772659772627389)
      ·
        refine ⟨39220647672289747414735271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104588393792772659772627389 39220647672289747414735271)
        ·
          refine ⟨58830971508434621122102907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39220647672289747414735271 58830971508434621122102907)
          ·
            refine ⟨88246457262651931683154361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58830971508434621122102907 88246457262651931683154361)
            ·
              refine ⟨66184842946988948762365771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88246457262651931683154361 66184842946988948762365771)
              ·
                refine ⟨99277264420483423143548657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66184842946988948762365771 99277264420483423143548657)
                ·
                  refine ⟨74457948315362567357661493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99277264420483423143548657 74457948315362567357661493)
                  ·
                    refine ⟨6980432654565240689780765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74457948315362567357661493 6980432654565240689780765)
                    ·
                      refine ⟨2617662245461965258667787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980432654565240689780765 2617662245461965258667787)
                      ·
                        rfl

theorem cell23_5097879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_5097879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097879 prefixEnd_5097879 := by exact prefixLift 5097879
  have htrace : WordTrace (prefixWord ++ tailWord_5097879) baseStart_5097879 baseEnd_5097879 := by
    simpa [prefixWord, tailWord_5097879, baseEnd_5097879] using wordTrace_append hprefix tailTrace_5097879
  have hstable : (prefixWord ++ tailWord_5097879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097879).length < 2 ^ (prefixWord ++ tailWord_5097879).sum := by decide
  have hdescent : baseEnd_5097879 < baseStart_5097879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097916 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_5097916 : Nat := 118140960795 + 5097916 * 2 ^ 59
def prefixEnd_5097916 : Nat := 4983230072969 + 3 ^ 40 * 5097916 * 2
def baseEnd_5097916 : Nat := 872560414748727204635039

theorem tailTrace_5097916 : CollatzResearch.WordTrace tailWord_5097916 prefixEnd_5097916 872560414748727204635039 := by
  unfold tailWord_5097916
  simp only [CollatzResearch.WordTrace]
  refine ⟨92968135899564230790772801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123957514532752307721030401 92968135899564230790772801)
  ·
    refine ⟨69726101924673173093079601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92968135899564230790772801 69726101924673173093079601)
    ·
      refine ⟨52294576443504879819809701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69726101924673173093079601 52294576443504879819809701)
      ·
        refine ⟨9805233083157164966214319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52294576443504879819809701 9805233083157164966214319)
        ·
          refine ⟨14707849624735747449321479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9805233083157164966214319 14707849624735747449321479)
          ·
            refine ⟨22061774437103621173982219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14707849624735747449321479 22061774437103621173982219)
            ·
              refine ⟨33092661655655431760973329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22061774437103621173982219 33092661655655431760973329)
              ·
                refine ⟨24819496241741573820729997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33092661655655431760973329 24819496241741573820729997)
                ·
                  refine ⟨9307311090653090182773749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24819496241741573820729997 9307311090653090182773749)
                  ·
                    refine ⟨872560414748727204635039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9307311090653090182773749 872560414748727204635039)
                    ·
                      rfl

theorem cell23_5097916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_5097916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097916 prefixEnd_5097916 := by exact prefixLift 5097916
  have htrace : WordTrace (prefixWord ++ tailWord_5097916) baseStart_5097916 baseEnd_5097916 := by
    simpa [prefixWord, tailWord_5097916, baseEnd_5097916] using wordTrace_append hprefix tailTrace_5097916
  have hstable : (prefixWord ++ tailWord_5097916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097916).length < 2 ^ (prefixWord ++ tailWord_5097916).sum := by decide
  have hdescent : baseEnd_5097916 < baseStart_5097916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097929 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_5097929 : Nat := 118140960795 + 5097929 * 2 ^ 59
def prefixEnd_5097929 : Nat := 4983230072969 + 3 ^ 40 * 5097929 * 2
def baseEnd_5097929 : Nat := 872562639831563354347519

theorem tailTrace_5097929 : CollatzResearch.WordTrace tailWord_5097929 prefixEnd_5097929 872562639831563354347519 := by
  unfold tailWord_5097929
  simp only [CollatzResearch.WordTrace]
  refine ⟨185936745948081364801768841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123957830632054243201179227 185936745948081364801768841)
  ·
    refine ⟨139452559461061023601326631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185936745948081364801768841 139452559461061023601326631)
    ·
      refine ⟨209178839191591535401989947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139452559461061023601326631 209178839191591535401989947)
      ·
        refine ⟨313768258787387303102984921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209178839191591535401989947 313768258787387303102984921)
        ·
          refine ⟨235326194090540477327238691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313768258787387303102984921 235326194090540477327238691)
          ·
            refine ⟨352989291135810715990858037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235326194090540477327238691 352989291135810715990858037)
            ·
              refine ⟨33092746043982254624142941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352989291135810715990858037 33092746043982254624142941)
              ·
                refine ⟨12409779766493345484053603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33092746043982254624142941 12409779766493345484053603)
                ·
                  refine ⟨18614669649740018226080405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12409779766493345484053603 18614669649740018226080405)
                  ·
                    refine ⟨872562639831563354347519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18614669649740018226080405 872562639831563354347519)
                    ·
                      rfl

theorem cell23_5097929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_5097929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097929 prefixEnd_5097929 := by exact prefixLift 5097929
  have htrace : WordTrace (prefixWord ++ tailWord_5097929) baseStart_5097929 baseEnd_5097929 := by
    simpa [prefixWord, tailWord_5097929, baseEnd_5097929] using wordTrace_append hprefix tailTrace_5097929
  have hstable : (prefixWord ++ tailWord_5097929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097929).length < 2 ^ (prefixWord ++ tailWord_5097929).sum := by decide
  have hdescent : baseEnd_5097929 < baseStart_5097929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097940 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5097940 : Nat := 118140960795 + 5097940 * 2 ^ 59
def prefixEnd_5097940 : Nat := 4983230072969 + 3 ^ 40 * 5097940 * 2
def baseEnd_5097940 : Nat := 2617693567781889520005007

theorem tailTrace_5097940 : CollatzResearch.WordTrace tailWord_5097940 prefixEnd_5097940 2617693567781889520005007 := by
  unfold tailWord_5097940
  simp only [CollatzResearch.WordTrace]
  refine ⟨92968573575520756840209637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123958098100694342453612849 92968573575520756840209637)
  ·
    refine ⟨17431607545410141907539307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92968573575520756840209637 17431607545410141907539307)
    ·
      refine ⟨26147411318115212861308961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17431607545410141907539307 26147411318115212861308961)
      ·
        refine ⟨19610558488586409645981721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26147411318115212861308961 19610558488586409645981721)
        ·
          refine ⟨14707918866439807234486291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19610558488586409645981721 14707918866439807234486291)
          ·
            refine ⟨22061878299659710851729437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14707918866439807234486291 22061878299659710851729437)
            ·
              refine ⟨8273204362372391569398539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22061878299659710851729437 8273204362372391569398539)
              ·
                refine ⟨12409806543558587354097809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273204362372391569398539 12409806543558587354097809)
                ·
                  refine ⟨9307354907668940515573357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12409806543558587354097809 9307354907668940515573357)
                  ·
                    refine ⟨3490258090375852693340009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9307354907668940515573357 3490258090375852693340009)
                    ·
                      refine ⟨2617693567781889520005007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490258090375852693340009 2617693567781889520005007)
                      ·
                        rfl

theorem cell23_5097940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5097940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097940 prefixEnd_5097940 := by exact prefixLift 5097940
  have htrace : WordTrace (prefixWord ++ tailWord_5097940) baseStart_5097940 baseEnd_5097940 := by
    simpa [prefixWord, tailWord_5097940, baseEnd_5097940] using wordTrace_append hprefix tailTrace_5097940
  have hstable : (prefixWord ++ tailWord_5097940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097940).length < 2 ^ (prefixWord ++ tailWord_5097940).sum := by decide
  have hdescent : baseEnd_5097940 < baseStart_5097940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097946 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_5097946 : Nat := 118140960795 + 5097946 * 2 ^ 59
def prefixEnd_5097946 : Nat := 4983230072969 + 3 ^ 40 * 5097946 * 2
def baseEnd_5097946 : Nat := 872565549555272165509993

theorem tailTrace_5097946 : CollatzResearch.WordTrace tailWord_5097946 prefixEnd_5097946 872565549555272165509993 := by
  unfold tailWord_5097946
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484341497254944176284423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123958243992679851136758461 46484341497254944176284423)
  ·
    refine ⟨69726512245882416264426635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46484341497254944176284423 69726512245882416264426635)
    ·
      refine ⟨104589768368823624396639953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69726512245882416264426635 104589768368823624396639953)
      ·
        refine ⟨78442326276617718297479965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104589768368823624396639953 78442326276617718297479965)
        ·
          refine ⟨29415872353731644361554987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78442326276617718297479965 29415872353731644361554987)
          ·
            refine ⟨44123808530597466542332481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29415872353731644361554987 44123808530597466542332481)
            ·
              refine ⟨33092856397948099906749361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44123808530597466542332481 33092856397948099906749361)
              ·
                refine ⟨24819642298461074930062021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33092856397948099906749361 24819642298461074930062021)
                ·
                  refine ⟨4653682930961451549386629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24819642298461074930062021 4653682930961451549386629)
                  ·
                    refine ⟨872565549555272165509993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653682930961451549386629 872565549555272165509993)
                    ·
                      rfl

theorem cell23_5097946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_5097946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097946 prefixEnd_5097946 := by exact prefixLift 5097946
  have htrace : WordTrace (prefixWord ++ tailWord_5097946) baseStart_5097946 baseEnd_5097946 := by
    simpa [prefixWord, tailWord_5097946, baseEnd_5097946] using wordTrace_append hprefix tailTrace_5097946
  have hstable : (prefixWord ++ tailWord_5097946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097946).length < 2 ^ (prefixWord ++ tailWord_5097946).sum := by decide
  have hdescent : baseEnd_5097946 < baseStart_5097946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097953 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_5097953 : Nat := 118140960795 + 5097953 * 2 ^ 59
def prefixEnd_5097953 : Nat := 4983230072969 + 3 ^ 40 * 5097953 * 2
def baseEnd_5097953 : Nat := 2617700243030397969142447

theorem tailTrace_5097953 : CollatzResearch.WordTrace tailWord_5097953 prefixEnd_5097953 2617700243030397969142447 := by
  unfold tailWord_5097953
  simp only [CollatzResearch.WordTrace]
  refine ⟨185937621299994416900642513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123958414199996277933761675 185937621299994416900642513)
  ·
    refine ⟨139453215974995812675481885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185937621299994416900642513 139453215974995812675481885)
    ·
      refine ⟨52294955990623429753305707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139453215974995812675481885 52294955990623429753305707)
      ·
        refine ⟨78442433985935144629958561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52294955990623429753305707 78442433985935144629958561)
        ·
          refine ⟨58831825489451358472468921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78442433985935144629958561 58831825489451358472468921)
          ·
            refine ⟨44123869117088518854351691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58831825489451358472468921 44123869117088518854351691)
            ·
              refine ⟨66185803675632778281527537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44123869117088518854351691 66185803675632778281527537)
              ·
                refine ⟨49639352756724583711145653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66185803675632778281527537 49639352756724583711145653)
                ·
                  refine ⟨4653689320942929722919905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49639352756724583711145653 4653689320942929722919905)
                  ·
                    refine ⟨3490266990707197292189929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653689320942929722919905 3490266990707197292189929)
                    ·
                      refine ⟨2617700243030397969142447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490266990707197292189929 2617700243030397969142447)
                      ·
                        rfl

theorem cell23_5097953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_5097953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097953 prefixEnd_5097953 := by exact prefixLift 5097953
  have htrace : WordTrace (prefixWord ++ tailWord_5097953) baseStart_5097953 baseEnd_5097953 := by
    simpa [prefixWord, tailWord_5097953, baseEnd_5097953] using wordTrace_append hprefix tailTrace_5097953
  have hstable : (prefixWord ++ tailWord_5097953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097953).length < 2 ^ (prefixWord ++ tailWord_5097953).sum := by decide
  have hdescent : baseEnd_5097953 < baseStart_5097953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097959 : List Nat := [1, 1, 5, 2, 1, 1, 12]
def baseStart_5097959 : Nat := 118140960795 + 5097959 * 2 ^ 59
def prefixEnd_5097959 : Nat := 4983230072969 + 3 ^ 40 * 5097959 * 2
def baseEnd_5097959 : Nat := 32317324986596604267499

theorem tailTrace_5097959 : CollatzResearch.WordTrace tailWord_5097959 prefixEnd_5097959 32317324986596604267499 := by
  unfold tailWord_5097959
  simp only [CollatzResearch.WordTrace]
  refine ⟨185937840137972679925360931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123958560091981786616907287 185937840137972679925360931)
  ·
    refine ⟨278906760206959019888041397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185937840137972679925360931 278906760206959019888041397)
    ·
      refine ⟨26147508769402408114503881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 278906760206959019888041397 26147508769402408114503881)
      ·
        refine ⟨19610631577051806085877911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26147508769402408114503881 19610631577051806085877911)
        ·
          refine ⟨29415947365577709128816867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19610631577051806085877911 29415947365577709128816867)
          ·
            refine ⟨44123921048366563693225301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29415947365577709128816867 44123921048366563693225301)
            ·
              refine ⟨32317324986596604267499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44123921048366563693225301 32317324986596604267499)
              ·
                rfl

theorem cell23_5097959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 12].length) (baseStart_5097959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097959 prefixEnd_5097959 := by exact prefixLift 5097959
  have htrace : WordTrace (prefixWord ++ tailWord_5097959) baseStart_5097959 baseEnd_5097959 := by
    simpa [prefixWord, tailWord_5097959, baseEnd_5097959] using wordTrace_append hprefix tailTrace_5097959
  have hstable : (prefixWord ++ tailWord_5097959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097959).length < 2 ^ (prefixWord ++ tailWord_5097959).sum := by decide
  have hdescent : baseEnd_5097959 < baseStart_5097959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097989 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_5097989 : Nat := 118140960795 + 5097989 * 2 ^ 59
def prefixEnd_5097989 : Nat := 4983230072969 + 3 ^ 40 * 5097989 * 2
def baseEnd_5097989 : Nat := 872572909444653276097427

theorem tailTrace_5097989 : CollatzResearch.WordTrace tailWord_5097989 prefixEnd_5097989 872572909444653276097427 := by
  unfold tailWord_5097989
  simp only [CollatzResearch.WordTrace]
  refine ⟨185938934327863995048953021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123959289551909330032635347 185938934327863995048953021)
  ·
    refine ⟨69727100372948998143357383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185938934327863995048953021 69727100372948998143357383)
    ·
      refine ⟨104590650559423497215036075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69727100372948998143357383 104590650559423497215036075)
      ·
        refine ⟨156885975839135245822554113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104590650559423497215036075 156885975839135245822554113)
        ·
          refine ⟨117664481879351434366915585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156885975839135245822554113 117664481879351434366915585)
          ·
            refine ⟨88248361409513575775186689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117664481879351434366915585 88248361409513575775186689)
            ·
              refine ⟨66186271057135181831390017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88248361409513575775186689 66186271057135181831390017)
              ·
                refine ⟨49639703292851386373542513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66186271057135181831390017 49639703292851386373542513)
                ·
                  refine ⟨37229777469638539780156885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49639703292851386373542513 37229777469638539780156885)
                  ·
                    refine ⟨872572909444653276097427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37229777469638539780156885 872572909444653276097427)
                    ·
                      rfl

theorem cell23_5097989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_5097989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097989 prefixEnd_5097989 := by exact prefixLift 5097989
  have htrace : WordTrace (prefixWord ++ tailWord_5097989) baseStart_5097989 baseEnd_5097989 := by
    simpa [prefixWord, tailWord_5097989, baseEnd_5097989] using wordTrace_append hprefix tailTrace_5097989
  have hstable : (prefixWord ++ tailWord_5097989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097989).length < 2 ^ (prefixWord ++ tailWord_5097989).sum := by decide
  have hdescent : baseEnd_5097989 < baseStart_5097989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5097999 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_5097999 : Nat := 118140960795 + 5097999 * 2 ^ 59
def prefixEnd_5097999 : Nat := 4983230072969 + 3 ^ 40 * 5097999 * 2
def baseEnd_5097999 : Nat := 2617723863140504789167235

theorem tailTrace_5097999 : CollatzResearch.WordTrace tailWord_5097999 prefixEnd_5097999 2617723863140504789167235 := by
  unfold tailWord_5097999
  simp only [CollatzResearch.WordTrace]
  refine ⟨185939299057827766756817051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123959532705218511171211367 185939299057827766756817051)
  ·
    refine ⟨278908948586741650135225577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185939299057827766756817051 278908948586741650135225577)
    ·
      refine ⟨209181711440056237601419183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278908948586741650135225577 209181711440056237601419183)
      ·
        refine ⟨313772567160084356402128775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209181711440056237601419183 313772567160084356402128775)
        ·
          refine ⟨470658850740126534603193163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313772567160084356402128775 470658850740126534603193163)
          ·
            refine ⟨705988276110189801904789745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470658850740126534603193163 705988276110189801904789745)
            ·
              refine ⟨529491207082642351428592309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705988276110189801904789745 529491207082642351428592309)
              ·
                refine ⟨49639800663997720446430529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529491207082642351428592309 49639800663997720446430529)
                ·
                  refine ⟨37229850497998290334822897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49639800663997720446430529 37229850497998290334822897)
                  ·
                    refine ⟨27922387873498717751117173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37229850497998290334822897 27922387873498717751117173)
                    ·
                      refine ⟨2617723863140504789167235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27922387873498717751117173 2617723863140504789167235)
                      ·
                        rfl

theorem cell23_5097999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_5097999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5097999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5097999 prefixEnd_5097999 := by exact prefixLift 5097999
  have htrace : WordTrace (prefixWord ++ tailWord_5097999) baseStart_5097999 baseEnd_5097999 := by
    simpa [prefixWord, tailWord_5097999, baseEnd_5097999] using wordTrace_append hprefix tailTrace_5097999
  have hstable : (prefixWord ++ tailWord_5097999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5097999).length < 2 ^ (prefixWord ++ tailWord_5097999).sum := by decide
  have hdescent : baseEnd_5097999 < baseStart_5097999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5097999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098083 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 5]
def baseStart_5098083 : Nat := 118140960795 + 5098083 * 2 ^ 59
def prefixEnd_5098083 : Nat := 4983230072969 + 3 ^ 40 * 5098083 * 2
def baseEnd_5098083 : Nat := 290862999501720273390761

theorem tailTrace_5098083 : CollatzResearch.WordTrace tailWord_5098083 prefixEnd_5098083 290862999501720273390761 := by
  unfold tailWord_5098083
  simp only [CollatzResearch.WordTrace]
  refine ⟨185942362789523449102874903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123961575193015632735249935 185942362789523449102874903)
  ·
    refine ⟨278913544184285173654312355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185942362789523449102874903 278913544184285173654312355)
    ·
      refine ⟨418370316276427760481468533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278913544184285173654312355 418370316276427760481468533)
      ·
        refine ⟨39222217150915102545137675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 418370316276427760481468533 39222217150915102545137675)
        ·
          refine ⟨58833325726372653817706513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39222217150915102545137675 58833325726372653817706513)
          ·
            refine ⟨44124994294779490363279885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58833325726372653817706513 44124994294779490363279885)
            ·
              refine ⟨16546872860542308886229957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44124994294779490363279885 16546872860542308886229957)
              ·
                refine ⟨3102538661351682916168117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16546872860542308886229957 3102538661351682916168117)
                ·
                  refine ⟨290862999501720273390761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3102538661351682916168117 290862999501720273390761)
                  ·
                    rfl

theorem cell23_5098083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 5].length) (baseStart_5098083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098083 prefixEnd_5098083 := by exact prefixLift 5098083
  have htrace : WordTrace (prefixWord ++ tailWord_5098083) baseStart_5098083 baseEnd_5098083 := by
    simpa [prefixWord, tailWord_5098083, baseEnd_5098083] using wordTrace_append hprefix tailTrace_5098083
  have hstable : (prefixWord ++ tailWord_5098083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098083).length < 2 ^ (prefixWord ++ tailWord_5098083).sum := by decide
  have hdescent : baseEnd_5098083 < baseStart_5098083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098093 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5098093 : Nat := 118140960795 + 5098093 * 2 ^ 59
def prefixEnd_5098093 : Nat := 4983230072969 + 3 ^ 40 * 5098093 * 2
def baseEnd_5098093 : Nat := 2617772130322027421391803

theorem tailTrace_5098093 : CollatzResearch.WordTrace tailWord_5098093 prefixEnd_5098093 2617772130322027421391803 := by
  unfold tailWord_5098093
  simp only [CollatzResearch.WordTrace]
  refine ⟨185942727519487220810738933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123961818346324813873825955 185942727519487220810738933)
  ·
    refine ⟨17432130704951926951006775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185942727519487220810738933 17432130704951926951006775)
    ·
      refine ⟨26148196057427890426510163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17432130704951926951006775 26148196057427890426510163)
      ·
        refine ⟨39222294086141835639765245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26148196057427890426510163 39222294086141835639765245)
        ·
          refine ⟨14708360282303188364911967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39222294086141835639765245 14708360282303188364911967)
          ·
            refine ⟨22062540423454782547367951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14708360282303188364911967 22062540423454782547367951)
            ·
              refine ⟨33093810635182173821051927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22062540423454782547367951 33093810635182173821051927)
              ·
                refine ⟨49640715952773260731577891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33093810635182173821051927 49640715952773260731577891)
                ·
                  refine ⟨74461073929159891097366837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49640715952773260731577891 74461073929159891097366837)
                  ·
                    refine ⟨6980725680858739790378141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74461073929159891097366837 6980725680858739790378141)
                    ·
                      refine ⟨2617772130322027421391803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980725680858739790378141 2617772130322027421391803)
                      ·
                        rfl

theorem cell23_5098093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5098093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098093 prefixEnd_5098093 := by exact prefixLift 5098093
  have htrace : WordTrace (prefixWord ++ tailWord_5098093) baseStart_5098093 baseEnd_5098093 := by
    simpa [prefixWord, tailWord_5098093, baseEnd_5098093] using wordTrace_append hprefix tailTrace_5098093
  have hstable : (prefixWord ++ tailWord_5098093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098093).length < 2 ^ (prefixWord ++ tailWord_5098093).sum := by decide
  have hdescent : baseEnd_5098093 < baseStart_5098093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098194 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5098194 : Nat := 118140960795 + 5098194 * 2 ^ 59
def prefixEnd_5098194 : Nat := 4983230072969 + 3 ^ 40 * 5098194 * 2
def baseEnd_5098194 : Nat := 872607997289377175409613

theorem tailTrace_5098194 : CollatzResearch.WordTrace tailWord_5098194 prefixEnd_5098194 872607997289377175409613 := by
  unfold tailWord_5098194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46486602823030328765041409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123964274194747543373443757 46486602823030328765041409)
  ·
    refine ⟨34864952117272746573781057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46486602823030328765041409 34864952117272746573781057)
    ·
      refine ⟨26148714087954559930335793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34864952117272746573781057 26148714087954559930335793)
      ·
        refine ⟨19611535565965919947751845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26148714087954559930335793 19611535565965919947751845)
        ·
          refine ⟨3677162918618609990203471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19611535565965919947751845 3677162918618609990203471)
          ·
            refine ⟨5515744377927914985305207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677162918618609990203471 5515744377927914985305207)
            ·
              refine ⟨8273616566891872477957811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515744377927914985305207 8273616566891872477957811)
              ·
                refine ⟨12410424850337808716936717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273616566891872477957811 12410424850337808716936717)
                ·
                  refine ⟨4653909318876678268851269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12410424850337808716936717 4653909318876678268851269)
                  ·
                    refine ⟨872607997289377175409613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653909318876678268851269 872607997289377175409613)
                    ·
                      rfl

theorem cell23_5098194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5098194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098194 prefixEnd_5098194 := by exact prefixLift 5098194
  have htrace : WordTrace (prefixWord ++ tailWord_5098194) baseStart_5098194 baseEnd_5098194 := by
    simpa [prefixWord, tailWord_5098194, baseEnd_5098194] using wordTrace_append hprefix tailTrace_5098194
  have hstable : (prefixWord ++ tailWord_5098194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098194).length < 2 ^ (prefixWord ++ tailWord_5098194).sum := by decide
  have hdescent : baseEnd_5098194 < baseStart_5098194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098233 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 6, 4]
def baseStart_5098233 : Nat := 118140960795 + 5098233 * 2 ^ 59
def prefixEnd_5098233 : Nat := 4983230072969 + 3 ^ 40 * 5098233 * 2
def baseEnd_5098233 : Nat := 872614672537885624547053

theorem tailTrace_5098233 : CollatzResearch.WordTrace tailWord_5098233 prefixEnd_5098233 872614672537885624547053 := by
  unfold tailWord_5098233
  simp only [CollatzResearch.WordTrace]
  refine ⟨185947833738980024720835353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123965222492653349813890235 185947833738980024720835353)
  ·
    refine ⟨139460875304235018540626515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185947833738980024720835353 139460875304235018540626515)
    ·
      refine ⟨209191312956352527810939773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139460875304235018540626515 209191312956352527810939773)
      ·
        refine ⟨78446742358632197929102415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209191312956352527810939773 78446742358632197929102415)
        ·
          refine ⟨117670113537948296893653623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78446742358632197929102415 117670113537948296893653623)
          ·
            refine ⟨176505170306922445340480435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117670113537948296893653623 176505170306922445340480435)
            ·
              refine ⟨264757755460383668010720653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176505170306922445340480435 264757755460383668010720653)
              ·
                refine ⟨99284158297643875504020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264757755460383668010720653 99284158297643875504020245)
                ·
                  refine ⟨4653944920202056664250949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99284158297643875504020245 4653944920202056664250949)
                  ·
                    refine ⟨872614672537885624547053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653944920202056664250949 872614672537885624547053)
                    ·
                      rfl

theorem cell23_5098233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 4].length) (baseStart_5098233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098233 prefixEnd_5098233 := by exact prefixLift 5098233
  have htrace : WordTrace (prefixWord ++ tailWord_5098233) baseStart_5098233 baseEnd_5098233 := by
    simpa [prefixWord, tailWord_5098233, baseEnd_5098233] using wordTrace_append hprefix tailTrace_5098233
  have hstable : (prefixWord ++ tailWord_5098233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098233).length < 2 ^ (prefixWord ++ tailWord_5098233).sum := by decide
  have hdescent : baseEnd_5098233 < baseStart_5098233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098274 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_5098274 : Nat := 118140960795 + 5098274 * 2 ^ 59
def prefixEnd_5098274 : Nat := 4983230072969 + 3 ^ 40 * 5098274 * 2
def baseEnd_5098274 : Nat := 2617865070320491213228471

theorem tailTrace_5098274 : CollatzResearch.WordTrace tailWord_5098274 prefixEnd_5098274 2617865070320491213228471 := by
  unfold tailWord_5098274
  simp only [CollatzResearch.WordTrace]
  refine ⟨46487332282957872180769469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123966219421220992482051917 46487332282957872180769469)
  ·
    refine ⟨17432749606109202067788551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46487332282957872180769469 17432749606109202067788551)
    ·
      refine ⟨26149124409163803101682827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17432749606109202067788551 26149124409163803101682827)
      ·
        refine ⟨39223686613745704652524241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26149124409163803101682827 39223686613745704652524241)
        ·
          refine ⟨29417764960309278489393181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39223686613745704652524241 29417764960309278489393181)
          ·
            refine ⟨11031661860115979433522443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29417764960309278489393181 11031661860115979433522443)
            ·
              refine ⟨16547492790173969150283665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11031661860115979433522443 16547492790173969150283665)
              ·
                refine ⟨12410619592630476862712749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16547492790173969150283665 12410619592630476862712749)
                ·
                  refine ⟨4653982347236428823517281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12410619592630476862712749 4653982347236428823517281)
                  ·
                    refine ⟨3490486760427321617637961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653982347236428823517281 3490486760427321617637961)
                    ·
                      refine ⟨2617865070320491213228471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490486760427321617637961 2617865070320491213228471)
                      ·
                        rfl

theorem cell23_5098274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_5098274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098274 prefixEnd_5098274 := by exact prefixLift 5098274
  have htrace : WordTrace (prefixWord ++ tailWord_5098274) baseStart_5098274 baseEnd_5098274 := by
    simpa [prefixWord, tailWord_5098274, baseEnd_5098274] using wordTrace_append hprefix tailTrace_5098274
  have hstable : (prefixWord ++ tailWord_5098274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098274).length < 2 ^ (prefixWord ++ tailWord_5098274).sum := by decide
  have hdescent : baseEnd_5098274 < baseStart_5098274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098280 : List Nat := [2, 1, 5, 1, 1, 1, 5, 7]
def baseStart_5098280 : Nat := 118140960795 + 5098280 * 2 ^ 59
def prefixEnd_5098280 : Nat := 4983230072969 + 3 ^ 40 * 5098280 * 2
def baseEnd_5098280 : Nat := 96958079674237710731609

theorem tailTrace_5098280 : CollatzResearch.WordTrace tailWord_5098280 prefixEnd_5098280 96958079674237710731609 := by
  unfold tailWord_5098280
  simp only [CollatzResearch.WordTrace]
  refine ⟨92974773984904875873898147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123966365313206501165197529 92974773984904875873898147)
  ·
    refine ⟨139462160977357313810847221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92974773984904875873898147 139462160977357313810847221)
    ·
      refine ⟨13074577591627248169766927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139462160977357313810847221 13074577591627248169766927)
      ·
        refine ⟨19611866387440872254650391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13074577591627248169766927 19611866387440872254650391)
        ·
          refine ⟨29417799581161308381975587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19611866387440872254650391 29417799581161308381975587)
          ·
            refine ⟨44126699371741962572963381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29417799581161308381975587 44126699371741962572963381)
            ·
              refine ⟨4136878066100808991215317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44126699371741962572963381 4136878066100808991215317)
              ·
                refine ⟨96958079674237710731609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4136878066100808991215317 96958079674237710731609)
                ·
                  rfl

theorem cell23_5098280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 7].length) (baseStart_5098280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098280 prefixEnd_5098280 := by exact prefixLift 5098280
  have htrace : WordTrace (prefixWord ++ tailWord_5098280) baseStart_5098280 baseEnd_5098280 := by
    simpa [prefixWord, tailWord_5098280, baseEnd_5098280] using wordTrace_append hprefix tailTrace_5098280
  have hstable : (prefixWord ++ tailWord_5098280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098280).length < 2 ^ (prefixWord ++ tailWord_5098280).sum := by decide
  have hdescent : baseEnd_5098280 < baseStart_5098280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098290 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_5098290 : Nat := 118140960795 + 5098290 * 2 ^ 59
def prefixEnd_5098290 : Nat := 4983230072969 + 3 ^ 40 * 5098290 * 2
def baseEnd_5098290 : Nat := 2617873286010963150628397

theorem tailTrace_5098290 : CollatzResearch.WordTrace tailWord_5098290 prefixEnd_5098290 2617873286010963150628397 := by
  unfold tailWord_5098290
  simp only [CollatzResearch.WordTrace]
  refine ⟨46487478174943380863915081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123966608466515682303773549 46487478174943380863915081)
  ·
    refine ⟨34865608631207535647936311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46487478174943380863915081 34865608631207535647936311)
    ·
      refine ⟨52298412946811303471904467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34865608631207535647936311 52298412946811303471904467)
      ·
        refine ⟨78447619420216955207856701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52298412946811303471904467 78447619420216955207856701)
        ·
          refine ⟨29417857282581358202946263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78447619420216955207856701 29417857282581358202946263)
          ·
            refine ⟨44126785923872037304419395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29417857282581358202946263 44126785923872037304419395)
            ·
              refine ⟨66190178885808055956629093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44126785923872037304419395 66190178885808055956629093)
              ·
                refine ⟨12410658541089010491867955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66190178885808055956629093 12410658541089010491867955)
                ·
                  refine ⟨18615987811633515737801933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12410658541089010491867955 18615987811633515737801933)
                  ·
                    refine ⟨6980995429362568401675725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18615987811633515737801933 6980995429362568401675725)
                    ·
                      refine ⟨2617873286010963150628397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6980995429362568401675725 2617873286010963150628397)
                      ·
                        rfl

theorem cell23_5098290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_5098290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098290 prefixEnd_5098290 := by exact prefixLift 5098290
  have htrace : WordTrace (prefixWord ++ tailWord_5098290) baseStart_5098290 baseEnd_5098290 := by
    simpa [prefixWord, tailWord_5098290, baseEnd_5098290] using wordTrace_append hprefix tailTrace_5098290
  have hstable : (prefixWord ++ tailWord_5098290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098290).length < 2 ^ (prefixWord ++ tailWord_5098290).sum := by decide
  have hdescent : baseEnd_5098290 < baseStart_5098290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098291 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 1, 2, 2]
def baseStart_5098291 : Nat := 118140960795 + 5098291 * 2 ^ 59
def prefixEnd_5098291 : Nat := 4983230072969 + 3 ^ 40 * 5098291 * 2
def baseEnd_5098291 : Nat := 2617873799491617646715893

theorem tailTrace_5098291 : CollatzResearch.WordTrace tailWord_5098291 prefixEnd_5098291 2617873799491617646715893 := by
  unfold tailWord_5098291
  simp only [CollatzResearch.WordTrace]
  refine ⟨185949949172769900626446727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123966632781846600417631151 185949949172769900626446727)
  ·
    refine ⟨278924923759154850939670091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185949949172769900626446727 278924923759154850939670091)
    ·
      refine ⟨418387385638732276409505137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278924923759154850939670091 418387385638732276409505137)
      ·
        refine ⟨313790539229049207307128853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418387385638732276409505137 313790539229049207307128853)
        ·
          refine ⟨14708931526361681592521665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 313790539229049207307128853 14708931526361681592521665)
          ·
            refine ⟨11031698644771261194391249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14708931526361681592521665 11031698644771261194391249)
            ·
              refine ⟨8273773983578445895793437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11031698644771261194391249 8273773983578445895793437)
              ·
                refine ⟨3102665243841917210922539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8273773983578445895793437 3102665243841917210922539)
                ·
                  refine ⟨4653997865762875816383809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102665243841917210922539 4653997865762875816383809)
                  ·
                    refine ⟨3490498399322156862287857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4653997865762875816383809 3490498399322156862287857)
                    ·
                      refine ⟨2617873799491617646715893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490498399322156862287857 2617873799491617646715893)
                      ·
                        rfl

theorem cell23_5098291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 2, 2].length) (baseStart_5098291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098291 prefixEnd_5098291 := by exact prefixLift 5098291
  have htrace : WordTrace (prefixWord ++ tailWord_5098291) baseStart_5098291 baseEnd_5098291 := by
    simpa [prefixWord, tailWord_5098291, baseEnd_5098291] using wordTrace_append hprefix tailTrace_5098291
  have hstable : (prefixWord ++ tailWord_5098291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098291).length < 2 ^ (prefixWord ++ tailWord_5098291).sum := by decide
  have hdescent : baseEnd_5098291 < baseStart_5098291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098301 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_5098301 : Nat := 118140960795 + 5098301 * 2 ^ 59
def prefixEnd_5098301 : Nat := 4983230072969 + 3 ^ 40 * 5098301 * 2
def baseEnd_5098301 : Nat := 872626311432720869196949

theorem tailTrace_5098301 : CollatzResearch.WordTrace tailWord_5098301 prefixEnd_5098301 872626311432720869196949 := by
  unfold tailWord_5098301
  simp only [CollatzResearch.WordTrace]
  refine ⟨185950313902733672334310757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123966875935155781556207171 185950313902733672334310757)
  ·
    refine ⟨34865683856762563562683267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185950313902733672334310757 34865683856762563562683267)
    ·
      refine ⟨52298525785143845344024901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34865683856762563562683267 52298525785143845344024901)
      ·
        refine ⟨9805973584714471002004669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52298525785143845344024901 9805973584714471002004669)
        ·
          refine ⟨3677240094267926625751751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9805973584714471002004669 3677240094267926625751751)
          ·
            refine ⟨5515860141401889938627627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677240094267926625751751 5515860141401889938627627)
            ·
              refine ⟨8273790212102834907941441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515860141401889938627627 8273790212102834907941441)
              ·
                refine ⟨6205342659077126180956081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273790212102834907941441 6205342659077126180956081)
                ·
                  refine ⟨4654006994307844635717061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6205342659077126180956081 4654006994307844635717061)
                  ·
                    refine ⟨872626311432720869196949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4654006994307844635717061 872626311432720869196949)
                    ·
                      rfl

theorem cell23_5098301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_5098301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098301 prefixEnd_5098301 := by exact prefixLift 5098301
  have htrace : WordTrace (prefixWord ++ tailWord_5098301) baseStart_5098301 baseEnd_5098301 := by
    simpa [prefixWord, tailWord_5098301, baseEnd_5098301] using wordTrace_append hprefix tailTrace_5098301
  have hstable : (prefixWord ++ tailWord_5098301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098301).length < 2 ^ (prefixWord ++ tailWord_5098301).sum := by decide
  have hdescent : baseEnd_5098301 < baseStart_5098301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098308 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5098308 : Nat := 118140960795 + 5098308 * 2 ^ 59
def prefixEnd_5098308 : Nat := 4983230072969 + 3 ^ 40 * 5098308 * 2
def baseEnd_5098308 : Nat := 2617882528662744080203315

theorem tailTrace_5098308 : CollatzResearch.WordTrace tailWord_5098308 prefixEnd_5098308 2617882528662744080203315 := by
  unfold tailWord_5098308
  simp only [CollatzResearch.WordTrace]
  refine ⟨92975284606854156264907789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123967046142472208353210385 92975284606854156264907789)
  ·
    refine ⟨34865731727570308599340421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92975284606854156264907789 34865731727570308599340421)
    ·
      refine ⟨6537324698919432862376329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34865731727570308599340421 6537324698919432862376329)
      ·
        refine ⟨4902993524189574646782247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6537324698919432862376329 4902993524189574646782247)
        ·
          refine ⟨7354490286284361970173371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902993524189574646782247 7354490286284361970173371)
          ·
            refine ⟨11031735429426542955260057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354490286284361970173371 11031735429426542955260057)
            ·
              refine ⟨8273801572069907216445043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11031735429426542955260057 8273801572069907216445043)
              ·
                refine ⟨12410702358104860824667565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273801572069907216445043 12410702358104860824667565)
                ·
                  refine ⟨4654013384289322809250337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12410702358104860824667565 4654013384289322809250337)
                  ·
                    refine ⟨3490510038216992106937753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654013384289322809250337 3490510038216992106937753)
                    ·
                      refine ⟨2617882528662744080203315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490510038216992106937753 2617882528662744080203315)
                      ·
                        rfl

theorem cell23_5098308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5098308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098308 prefixEnd_5098308 := by exact prefixLift 5098308
  have htrace : WordTrace (prefixWord ++ tailWord_5098308) baseStart_5098308 baseEnd_5098308 := by
    simpa [prefixWord, tailWord_5098308, baseEnd_5098308] using wordTrace_append hprefix tailTrace_5098308
  have hstable : (prefixWord ++ tailWord_5098308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098308).length < 2 ^ (prefixWord ++ tailWord_5098308).sum := by decide
  have hdescent : baseEnd_5098308 < baseStart_5098308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098324 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_5098324 : Nat := 118140960795 + 5098324 * 2 ^ 59
def prefixEnd_5098324 : Nat := 4983230072969 + 3 ^ 40 * 5098324 * 2
def baseEnd_5098324 : Nat := 2617890744353216017603241

theorem tailTrace_5098324 : CollatzResearch.WordTrace tailWord_5098324 prefixEnd_5098324 2617890744353216017603241 := by
  unfold tailWord_5098324
  simp only [CollatzResearch.WordTrace]
  refine ⟨92975576390825173631199013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123967435187766898174932017 92975576390825173631199013)
  ·
    refine ⟨17432920573279720055849815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92975576390825173631199013 17432920573279720055849815)
    ·
      refine ⟨26149380859919580083774723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17432920573279720055849815 26149380859919580083774723)
      ·
        refine ⟨39224071289879370125662085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26149380859919580083774723 39224071289879370125662085)
        ·
          refine ⟨7354513366852381898561641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39224071289879370125662085 7354513366852381898561641)
          ·
            refine ⟨5515885025139286423921231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354513366852381898561641 5515885025139286423921231)
            ·
              refine ⟨8273827537708929635881847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515885025139286423921231 8273827537708929635881847)
              ·
                refine ⟨12410741306563394453822771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273827537708929635881847 12410741306563394453822771)
                ·
                  refine ⟨18616111959845091680734157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12410741306563394453822771 18616111959845091680734157)
                  ·
                    refine ⟨6981041984941909380275309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18616111959845091680734157 6981041984941909380275309)
                    ·
                      refine ⟨2617890744353216017603241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981041984941909380275309 2617890744353216017603241)
                      ·
                        rfl

theorem cell23_5098324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_5098324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098324 prefixEnd_5098324 := by exact prefixLift 5098324
  have htrace : WordTrace (prefixWord ++ tailWord_5098324) baseStart_5098324 baseEnd_5098324 := by
    simpa [prefixWord, tailWord_5098324, baseEnd_5098324] using wordTrace_append hprefix tailTrace_5098324
  have hstable : (prefixWord ++ tailWord_5098324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098324).length < 2 ^ (prefixWord ++ tailWord_5098324).sum := by decide
  have hdescent : baseEnd_5098324 < baseStart_5098324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098347 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 4, 2, 2]
def baseStart_5098347 : Nat := 118140960795 + 5098347 * 2 ^ 59
def prefixEnd_5098347 : Nat := 4983230072969 + 3 ^ 40 * 5098347 * 2
def baseEnd_5098347 : Nat := 2617902554408269427615635

theorem tailTrace_5098347 : CollatzResearch.WordTrace tailWord_5098347 prefixEnd_5098347 2617902554408269427615635 := by
  unfold tailWord_5098347
  simp only [CollatzResearch.WordTrace]
  refine ⟨185951991660567022190485295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123967994440378014793656863 185951991660567022190485295)
  ·
    refine ⟨278927987490850533285727943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185951991660567022190485295 278927987490850533285727943)
    ·
      refine ⟨418391981236275799928591915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278927987490850533285727943 418391981236275799928591915)
      ·
        refine ⟨627587971854413699892887873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418391981236275799928591915 627587971854413699892887873)
        ·
          refine ⟨470690978890810274919665905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627587971854413699892887873 470690978890810274919665905)
          ·
            refine ⟨353018234168107706189749429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470690978890810274919665905 353018234168107706189749429)
            ·
              refine ⟨33095459453260097455289009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353018234168107706189749429 33095459453260097455289009)
              ·
                refine ⟨24821594589945073091466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33095459453260097455289009 24821594589945073091466757)
                ·
                  refine ⟨4654048985614701204650017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24821594589945073091466757 4654048985614701204650017)
                  ·
                    refine ⟨3490536739211025903487513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654048985614701204650017 3490536739211025903487513)
                    ·
                      refine ⟨2617902554408269427615635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490536739211025903487513 2617902554408269427615635)
                      ·
                        rfl

theorem cell23_5098347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 2, 2].length) (baseStart_5098347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098347 prefixEnd_5098347 := by exact prefixLift 5098347
  have htrace : WordTrace (prefixWord ++ tailWord_5098347) baseStart_5098347 baseEnd_5098347 := by
    simpa [prefixWord, tailWord_5098347, baseEnd_5098347] using wordTrace_append hprefix tailTrace_5098347
  have hstable : (prefixWord ++ tailWord_5098347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098347).length < 2 ^ (prefixWord ++ tailWord_5098347).sum := by decide
  have hdescent : baseEnd_5098347 < baseStart_5098347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098380 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_5098380 : Nat := 118140960795 + 5098380 * 2 ^ 59
def prefixEnd_5098380 : Nat := 4983230072969 + 3 ^ 40 * 5098380 * 2
def baseEnd_5098380 : Nat := 2617919499269867798502983

theorem tailTrace_5098380 : CollatzResearch.WordTrace tailWord_5098380 prefixEnd_5098380 2617919499269867798502983 := by
  unfold tailWord_5098380
  simp only [CollatzResearch.WordTrace]
  refine ⟨92976597634723734413218297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123968796846298312550957729 92976597634723734413218297)
  ·
    refine ⟨69732448226042800809913723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92976597634723734413218297 69732448226042800809913723)
    ·
      refine ⟨104598672339064201214870585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69732448226042800809913723 104598672339064201214870585)
      ·
        refine ⟨78449004254298150911152939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104598672339064201214870585 78449004254298150911152939)
        ·
          refine ⟨117673506381447226366729409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78449004254298150911152939 117673506381447226366729409)
          ·
            refine ⟨88255129786085419775047057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117673506381447226366729409 88255129786085419775047057)
            ·
              refine ⟨66191347339564064831285293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88255129786085419775047057 66191347339564064831285293)
              ·
                refine ⟨24821755252336524311731985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66191347339564064831285293 24821755252336524311731985)
                ·
                  refine ⟨18616316439252393233798989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24821755252336524311731985 18616316439252393233798989)
                  ·
                    refine ⟨6981118664719647462674621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18616316439252393233798989 6981118664719647462674621)
                    ·
                      refine ⟨2617919499269867798502983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981118664719647462674621 2617919499269867798502983)
                      ·
                        rfl

theorem cell23_5098380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_5098380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098380 prefixEnd_5098380 := by exact prefixLift 5098380
  have htrace : WordTrace (prefixWord ++ tailWord_5098380) baseStart_5098380 baseEnd_5098380 := by
    simpa [prefixWord, tailWord_5098380, baseEnd_5098380] using wordTrace_append hprefix tailTrace_5098380
  have hstable : (prefixWord ++ tailWord_5098380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098380).length < 2 ^ (prefixWord ++ tailWord_5098380).sum := by decide
  have hdescent : baseEnd_5098380 < baseStart_5098380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098393 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_5098393 : Nat := 118140960795 + 5098393 * 2 ^ 59
def prefixEnd_5098393 : Nat := 4983230072969 + 3 ^ 40 * 5098393 * 2
def baseEnd_5098393 : Nat := 2617926174518376247640423

theorem tailTrace_5098393 : CollatzResearch.WordTrace tailWord_5098393 prefixEnd_5098393 2617926174518376247640423 := by
  unfold tailWord_5098393
  simp only [CollatzResearch.WordTrace]
  refine ⟨185953669418400372046659833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123969112945600248031106555 185953669418400372046659833)
  ·
    refine ⟨139465252063800279034994875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185953669418400372046659833 139465252063800279034994875)
    ·
      refine ⟨209197878095700418552492313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139465252063800279034994875 209197878095700418552492313)
      ·
        refine ⟨156898408571775313914369235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209197878095700418552492313 156898408571775313914369235)
        ·
          refine ⟨235347612857662970871553853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156898408571775313914369235 235347612857662970871553853)
          ·
            refine ⟨88255354821623614076832695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235347612857662970871553853 88255354821623614076832695)
            ·
              refine ⟨132383032232435421115249043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88255354821623614076832695 132383032232435421115249043)
              ·
                refine ⟨198574548348653131672873565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132383032232435421115249043 198574548348653131672873565)
                ·
                  refine ⟨74465455630744924377327587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198574548348653131672873565 74465455630744924377327587)
                  ·
                    refine ⟨111698183446117386565991381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74465455630744924377327587 111698183446117386565991381)
                    ·
                      refine ⟨2617926174518376247640423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111698183446117386565991381 2617926174518376247640423)
                      ·
                        rfl

theorem cell23_5098393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_5098393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098393 prefixEnd_5098393 := by exact prefixLift 5098393
  have htrace : WordTrace (prefixWord ++ tailWord_5098393) baseStart_5098393 baseEnd_5098393 := by
    simpa [prefixWord, tailWord_5098393, baseEnd_5098393] using wordTrace_append hprefix tailTrace_5098393
  have hstable : (prefixWord ++ tailWord_5098393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098393).length < 2 ^ (prefixWord ++ tailWord_5098393).sum := by decide
  have hdescent : baseEnd_5098393 < baseStart_5098393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098400 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_5098400 : Nat := 118140960795 + 5098400 * 2 ^ 59
def prefixEnd_5098400 : Nat := 4983230072969 + 3 ^ 40 * 5098400 * 2
def baseEnd_5098400 : Nat := 872643256294319240084297

theorem tailTrace_5098400 : CollatzResearch.WordTrace tailWord_5098400 prefixEnd_5098400 872643256294319240084297 := by
  unfold tailWord_5098400
  simp only [CollatzResearch.WordTrace]
  refine ⟨92976962364687506121082327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123969283152916674828109769 92976962364687506121082327)
  ·
    refine ⟨139465443547031259181623491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92976962364687506121082327 139465443547031259181623491)
    ·
      refine ⟨209198165320546888772435237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139465443547031259181623491 209198165320546888772435237)
      ·
        refine ⟨39224655997602541644831607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209198165320546888772435237 39224655997602541644831607)
        ·
          refine ⟨58836983996403812467247411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39224655997602541644831607 58836983996403812467247411)
          ·
            refine ⟨88255475994605718700871117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58836983996403812467247411 88255475994605718700871117)
            ·
              refine ⟨33095803497977144512826669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88255475994605718700871117 33095803497977144512826669)
              ·
                refine ⟨12410926311741429192310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33095803497977144512826669 12410926311741429192310001)
                ·
                  refine ⟨9308194733806071894232501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12410926311741429192310001 9308194733806071894232501)
                  ·
                    refine ⟨872643256294319240084297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9308194733806071894232501 872643256294319240084297)
                    ·
                      rfl

theorem cell23_5098400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_5098400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098400 prefixEnd_5098400 := by exact prefixLift 5098400
  have htrace : WordTrace (prefixWord ++ tailWord_5098400) baseStart_5098400 baseEnd_5098400 := by
    simpa [prefixWord, tailWord_5098400, baseEnd_5098400] using wordTrace_append hprefix tailTrace_5098400
  have hstable : (prefixWord ++ tailWord_5098400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098400).length < 2 ^ (prefixWord ++ tailWord_5098400).sum := by decide
  have hdescent : baseEnd_5098400 < baseStart_5098400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098438 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5098438 : Nat := 118140960795 + 5098438 * 2 ^ 59
def prefixEnd_5098438 : Nat := 4983230072969 + 3 ^ 40 * 5098438 * 2
def baseEnd_5098438 : Nat := 290883253460869841286413

theorem tailTrace_5098438 : CollatzResearch.WordTrace tailWord_5098438 prefixEnd_5098438 290883253460869841286413 := by
  unfold tailWord_5098438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811103459476167022876499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123970207135491563154698645 5811103459476167022876499)
  ·
    refine ⟨8716655189214250534314749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5811103459476167022876499 8716655189214250534314749)
    ·
      refine ⟨3268745695955343950368031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8716655189214250534314749 3268745695955343950368031)
      ·
        refine ⟨4903118543933015925552047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268745695955343950368031 4903118543933015925552047)
        ·
          refine ⟨7354677815899523888328071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903118543933015925552047 7354677815899523888328071)
          ·
            refine ⟨11032016723849285832492107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354677815899523888328071 11032016723849285832492107)
            ·
              refine ⟨16548025085773928748738161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032016723849285832492107 16548025085773928748738161)
              ·
                refine ⟨12411018814330446561553621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16548025085773928748738161 12411018814330446561553621)
                ·
                  refine ⟨290883253460869841286413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12411018814330446561553621 290883253460869841286413)
                  ·
                    rfl

theorem cell23_5098438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5098438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098438 prefixEnd_5098438 := by exact prefixLift 5098438
  have htrace : WordTrace (prefixWord ++ tailWord_5098438) baseStart_5098438 baseEnd_5098438 := by
    simpa [prefixWord, tailWord_5098438, baseEnd_5098438] using wordTrace_append hprefix tailTrace_5098438
  have hstable : (prefixWord ++ tailWord_5098438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098438).length < 2 ^ (prefixWord ++ tailWord_5098438).sum := by decide
  have hdescent : baseEnd_5098438 < baseStart_5098438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098447 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 3, 4]
def baseStart_5098447 : Nat := 118140960795 + 5098447 * 2 ^ 59
def prefixEnd_5098447 : Nat := 4983230072969 + 3 ^ 40 * 5098447 * 2
def baseEnd_5098447 : Nat := 872651300824573012121725

theorem tailTrace_5098447 : CollatzResearch.WordTrace tailWord_5098447 prefixEnd_5098447 872651300824573012121725 := by
  unfold tailWord_5098447
  simp only [CollatzResearch.WordTrace]
  refine ⟨185955638960204739269125595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123970425973469826179417063 185955638960204739269125595)
  ·
    refine ⟨278933458440307108903688393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185955638960204739269125595 278933458440307108903688393)
    ·
      refine ⟨209200093830230331677766295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278933458440307108903688393 209200093830230331677766295)
      ·
        refine ⟨313800140745345497516649443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209200093830230331677766295 313800140745345497516649443)
        ·
          refine ⟨470700211118018246274974165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313800140745345497516649443 470700211118018246274974165)
          ·
            refine ⟨11032036198078552647069707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 470700211118018246274974165 11032036198078552647069707)
            ·
              refine ⟨16548054297117828970604561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032036198078552647069707 16548054297117828970604561)
              ·
                refine ⟨12411040722838371727953421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16548054297117828970604561 12411040722838371727953421)
                ·
                  refine ⟨4654140271064389397982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12411040722838371727953421 4654140271064389397982533)
                  ·
                    refine ⟨872651300824573012121725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4654140271064389397982533 872651300824573012121725)
                    ·
                      rfl

theorem cell23_5098447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 4].length) (baseStart_5098447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098447 prefixEnd_5098447 := by exact prefixLift 5098447
  have htrace : WordTrace (prefixWord ++ tailWord_5098447) baseStart_5098447 baseEnd_5098447 := by
    simpa [prefixWord, tailWord_5098447, baseEnd_5098447] using wordTrace_append hprefix tailTrace_5098447
  have hstable : (prefixWord ++ tailWord_5098447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098447).length < 2 ^ (prefixWord ++ tailWord_5098447).sum := by decide
  have hdescent : baseEnd_5098447 < baseStart_5098447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098454 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_5098454 : Nat := 118140960795 + 5098454 * 2 ^ 59
def prefixEnd_5098454 : Nat := 4983230072969 + 3 ^ 40 * 5098454 * 2
def baseEnd_5098454 : Nat := 2617957496838300508977643

theorem tailTrace_5098454 : CollatzResearch.WordTrace tailWord_5098454 prefixEnd_5098454 2617957496838300508977643 := by
  unfold tailWord_5098454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622243391948711216539401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 123970596180786252976420277 11622243391948711216539401)
  ·
    refine ⟨8716682543961533412404551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11622243391948711216539401 8716682543961533412404551)
    ·
      refine ⟨13075023815942300118606827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8716682543961533412404551 13075023815942300118606827)
      ·
        refine ⟨19612535723913450177910241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13075023815942300118606827 19612535723913450177910241)
        ·
          refine ⟨14709401792935087633432681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19612535723913450177910241 14709401792935087633432681)
          ·
            refine ⟨11032051344701315725074511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14709401792935087633432681 11032051344701315725074511)
            ·
              refine ⟨16548077017051973587611767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032051344701315725074511 16548077017051973587611767)
              ·
                refine ⟨24822115525577960381417651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548077017051973587611767 24822115525577960381417651)
                ·
                  refine ⟨37233173288366940572126477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24822115525577960381417651 37233173288366940572126477)
                  ·
                    refine ⟨13962439983137602714547429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37233173288366940572126477 13962439983137602714547429)
                    ·
                      refine ⟨2617957496838300508977643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13962439983137602714547429 2617957496838300508977643)
                      ·
                        rfl

theorem cell23_5098454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_5098454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098454 prefixEnd_5098454 := by exact prefixLift 5098454
  have htrace : WordTrace (prefixWord ++ tailWord_5098454) baseStart_5098454 baseEnd_5098454 := by
    simpa [prefixWord, tailWord_5098454, baseEnd_5098454] using wordTrace_append hprefix tailTrace_5098454
  have hstable : (prefixWord ++ tailWord_5098454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098454).length < 2 ^ (prefixWord ++ tailWord_5098454).sum := by decide
  have hdescent : baseEnd_5098454 < baseStart_5098454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098457 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_5098457 : Nat := 118140960795 + 5098457 * 2 ^ 59
def prefixEnd_5098457 : Nat := 4983230072969 + 3 ^ 40 * 5098457 * 2
def baseEnd_5098457 : Nat := 2617959037280263997240129

theorem tailTrace_5098457 : CollatzResearch.WordTrace tailWord_5098457 prefixEnd_5098457 2617959037280263997240129 := by
  unfold tailWord_5098457
  simp only [CollatzResearch.WordTrace]
  refine ⟨185956003690168510976989625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123970669126779007317993083 185956003690168510976989625)
  ·
    refine ⟨139467002767626383232742219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185956003690168510976989625 139467002767626383232742219)
    ·
      refine ⟨209200504151439574849113329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139467002767626383232742219 209200504151439574849113329)
      ·
        refine ⟨156900378113579681136834997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209200504151439574849113329 156900378113579681136834997)
        ·
          refine ⟨14709410448148095106578281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156900378113579681136834997 14709410448148095106578281)
          ·
            refine ⟨11032057836111071329933711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14709410448148095106578281 11032057836111071329933711)
            ·
              refine ⟨16548086754166606994900567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032057836111071329933711 16548086754166606994900567)
              ·
                refine ⟨24822130131249910492350851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548086754166606994900567 24822130131249910492350851)
                ·
                  refine ⟨37233195196874865738526277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24822130131249910492350851 37233195196874865738526277)
                  ·
                    refine ⟨6981224099414037325973677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37233195196874865738526277 6981224099414037325973677)
                    ·
                      refine ⟨2617959037280263997240129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981224099414037325973677 2617959037280263997240129)
                      ·
                        rfl

theorem cell23_5098457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_5098457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098457 prefixEnd_5098457 := by exact prefixLift 5098457
  have htrace : WordTrace (prefixWord ++ tailWord_5098457) baseStart_5098457 baseEnd_5098457 := by
    simpa [prefixWord, tailWord_5098457, baseEnd_5098457] using wordTrace_append hprefix tailTrace_5098457
  have hstable : (prefixWord ++ tailWord_5098457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098457).length < 2 ^ (prefixWord ++ tailWord_5098457).sum := by decide
  have hdescent : baseEnd_5098457 < baseStart_5098457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098490 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_5098490 : Nat := 118140960795 + 5098490 * 2 ^ 59
def prefixEnd_5098490 : Nat := 4983230072969 + 3 ^ 40 * 5098490 * 2
def baseEnd_5098490 : Nat := 872658660713954122709159

theorem tailTrace_5098490 : CollatzResearch.WordTrace tailWord_5098490 prefixEnd_5098490 872658660713954122709159 := by
  unfold tailWord_5098490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489301824762239403235231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123971471532699305075293949 46489301824762239403235231)
  ·
    refine ⟨69733952737143359104852847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46489301824762239403235231 69733952737143359104852847)
    ·
      refine ⟨104600929105715038657279271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69733952737143359104852847 104600929105715038657279271)
      ·
        refine ⟨156901393658572557985918907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104600929105715038657279271 156901393658572557985918907)
        ·
          refine ⟨235352090487858836978878361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156901393658572557985918907 235352090487858836978878361)
          ·
            refine ⟨176514067865894127734158771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235352090487858836978878361 176514067865894127734158771)
            ·
              refine ⟨264771101798841191601238157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176514067865894127734158771 264771101798841191601238157)
              ·
                refine ⟨99289163174565446850464309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264771101798841191601238157 99289163174565446850464309)
                ·
                  refine ⟨9308359047615510642231029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99289163174565446850464309 9308359047615510642231029)
                  ·
                    refine ⟨872658660713954122709159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9308359047615510642231029 872658660713954122709159)
                    ·
                      rfl

theorem cell23_5098490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_5098490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098490 prefixEnd_5098490 := by exact prefixLift 5098490
  have htrace : WordTrace (prefixWord ++ tailWord_5098490) baseStart_5098490 baseEnd_5098490 := by
    simpa [prefixWord, tailWord_5098490, baseEnd_5098490] using wordTrace_append hprefix tailTrace_5098490
  have hstable : (prefixWord ++ tailWord_5098490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098490).length < 2 ^ (prefixWord ++ tailWord_5098490).sum := by decide
  have hdescent : baseEnd_5098490 < baseStart_5098490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098504 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_5098504 : Nat := 118140960795 + 5098504 * 2 ^ 59
def prefixEnd_5098504 : Nat := 4983230072969 + 3 ^ 40 * 5098504 * 2
def baseEnd_5098504 : Nat := 2617983170871025313352413

theorem tailTrace_5098504 : CollatzResearch.WordTrace tailWord_5098504 prefixEnd_5098504 2617983170871025313352413 := by
  unfold tailWord_5098504
  simp only [CollatzResearch.WordTrace]
  refine ⟨92978858960499119001975283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123971811947332158669300377 92978858960499119001975283)
  ·
    refine ⟨139468288440748678502962925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92978858960499119001975283 139468288440748678502962925)
    ·
      refine ⟨52300608165280754438611097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139468288440748678502962925 52300608165280754438611097)
      ·
        refine ⟨39225456123960565828958323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52300608165280754438611097 39225456123960565828958323)
        ·
          refine ⟨58838184185940848743437485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39225456123960565828958323 58838184185940848743437485)
          ·
            refine ⟨22064319069727818278789057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58838184185940848743437485 22064319069727818278789057)
            ·
              refine ⟨16548239302295863709091793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22064319069727818278789057 16548239302295863709091793)
              ·
                refine ⟨12411179476721897781818845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16548239302295863709091793 12411179476721897781818845)
                ·
                  refine ⟨4654192303770711668182067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12411179476721897781818845 4654192303770711668182067)
                  ·
                    refine ⟨6981288455656067502273101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4654192303770711668182067 6981288455656067502273101)
                    ·
                      refine ⟨2617983170871025313352413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981288455656067502273101 2617983170871025313352413)
                      ·
                        rfl

theorem cell23_5098504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_5098504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098504 prefixEnd_5098504 := by exact prefixLift 5098504
  have htrace : WordTrace (prefixWord ++ tailWord_5098504) baseStart_5098504 baseEnd_5098504 := by
    simpa [prefixWord, tailWord_5098504, baseEnd_5098504] using wordTrace_append hprefix tailTrace_5098504
  have hstable : (prefixWord ++ tailWord_5098504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098504).length < 2 ^ (prefixWord ++ tailWord_5098504).sum := by decide
  have hdescent : baseEnd_5098504 < baseStart_5098504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098507 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 1, 5]
def baseStart_5098507 : Nat := 118140960795 + 5098507 * 2 ^ 59
def prefixEnd_5098507 : Nat := 4983230072969 + 3 ^ 40 * 5098507 * 2
def baseEnd_5098507 : Nat := 872661570437662933871633

theorem tailTrace_5098507 : CollatzResearch.WordTrace tailWord_5098507 prefixEnd_5098507 872661570437662933871633 := by
  unfold tailWord_5098507
  simp only [CollatzResearch.WordTrace]
  refine ⟨185957827339987369516309775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123971884893324913010873183 185957827339987369516309775)
  ·
    refine ⟨278936741009981054274464663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185957827339987369516309775 278936741009981054274464663)
    ·
      refine ⟨418405111514971581411696995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278936741009981054274464663 418405111514971581411696995)
      ·
        refine ⟨627607667272457372117545493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418405111514971581411696995 627607667272457372117545493)
        ·
          refine ⟨29419109403396439318009945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 627607667272457372117545493 29419109403396439318009945)
          ·
            refine ⟨22064332052547329488507459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29419109403396439318009945 22064332052547329488507459)
            ·
              refine ⟨33096498078820994232761189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22064332052547329488507459 33096498078820994232761189)
              ·
                refine ⟨6205593389778936418642723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33096498078820994232761189 6205593389778936418642723)
                ·
                  refine ⟨9308390084668404627964085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205593389778936418642723 9308390084668404627964085)
                  ·
                    refine ⟨872661570437662933871633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9308390084668404627964085 872661570437662933871633)
                    ·
                      rfl

theorem cell23_5098507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 5].length) (baseStart_5098507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098507 prefixEnd_5098507 := by exact prefixLift 5098507
  have htrace : WordTrace (prefixWord ++ tailWord_5098507) baseStart_5098507 baseEnd_5098507 := by
    simpa [prefixWord, tailWord_5098507, baseEnd_5098507] using wordTrace_append hprefix tailTrace_5098507
  have hstable : (prefixWord ++ tailWord_5098507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098507).length < 2 ^ (prefixWord ++ tailWord_5098507).sum := by decide
  have hdescent : baseEnd_5098507 < baseStart_5098507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098521 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 1, 1, 3]
def baseStart_5098521 : Nat := 118140960795 + 5098521 * 2 ^ 59
def prefixEnd_5098521 : Nat := 4983230072969 + 3 ^ 40 * 5098521 * 2
def baseEnd_5098521 : Nat := 2617991900042151746839835

theorem tailTrace_5098521 : CollatzResearch.WordTrace tailWord_5098521 prefixEnd_5098521 2617991900042151746839835 := by
  unfold tailWord_5098521
  simp only [CollatzResearch.WordTrace]
  refine ⟨185958337961936649907319417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123972225307957766604879611 185958337961936649907319417)
  ·
    refine ⟨139468753471452487430489563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185958337961936649907319417 139468753471452487430489563)
    ·
      refine ⟨209203130207178731145734345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139468753471452487430489563 209203130207178731145734345)
      ·
        refine ⟨156902347655384048359300759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209203130207178731145734345 156902347655384048359300759)
        ·
          refine ⟨235353521483076072538951139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156902347655384048359300759 235353521483076072538951139)
          ·
            refine ⟨353030282224614108808426709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235353521483076072538951139 353030282224614108808426709)
            ·
              refine ⟨8274147239639393175197501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 353030282224614108808426709 8274147239639393175197501)
              ·
                refine ⟨3102805214864772440699063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8274147239639393175197501 3102805214864772440699063)
                ·
                  refine ⟨4654207822297158661048595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102805214864772440699063 4654207822297158661048595)
                  ·
                    refine ⟨6981311733445737991572893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4654207822297158661048595 6981311733445737991572893)
                    ·
                      refine ⟨2617991900042151746839835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981311733445737991572893 2617991900042151746839835)
                      ·
                        rfl

theorem cell23_5098521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_5098521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098521 prefixEnd_5098521 := by exact prefixLift 5098521
  have htrace : WordTrace (prefixWord ++ tailWord_5098521) baseStart_5098521 baseEnd_5098521 := by
    simpa [prefixWord, tailWord_5098521, baseEnd_5098521] using wordTrace_append hprefix tailTrace_5098521
  have hstable : (prefixWord ++ tailWord_5098521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098521).length < 2 ^ (prefixWord ++ tailWord_5098521).sum := by decide
  have hdescent : baseEnd_5098521 < baseStart_5098521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098538 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5098538 : Nat := 118140960795 + 5098538 * 2 ^ 59
def prefixEnd_5098538 : Nat := 4983230072969 + 3 ^ 40 * 5098538 * 2
def baseEnd_5098538 : Nat := 2618000629213278180327257

theorem tailTrace_5098538 : CollatzResearch.WordTrace tailWord_5098538 prefixEnd_5098538 2618000629213278180327257 := by
  unfold tailWord_5098538
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489739500718765452672067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123972638668583374540458845 46489739500718765452672067)
  ·
    refine ⟨69734609251078148179008101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46489739500718765452672067 69734609251078148179008101)
    ·
      refine ⟨13075239234577152783564019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69734609251078148179008101 13075239234577152783564019)
      ·
        refine ⟨19612858851865729175346029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13075239234577152783564019 19612858851865729175346029)
        ·
          refine ⟨7354822069449648440754761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19612858851865729175346029 7354822069449648440754761)
          ·
            refine ⟨5516116552087236330566071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354822069449648440754761 5516116552087236330566071)
            ·
              refine ⟨8274174828130854495849107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516116552087236330566071 8274174828130854495849107)
              ·
                refine ⟨12411262242196281743773661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8274174828130854495849107 12411262242196281743773661)
                ·
                  refine ⟨4654223340823605653915123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12411262242196281743773661 4654223340823605653915123)
                  ·
                    refine ⟨6981335011235408480872685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4654223340823605653915123 6981335011235408480872685)
                    ·
                      refine ⟨2618000629213278180327257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981335011235408480872685 2618000629213278180327257)
                      ·
                        rfl

theorem cell23_5098538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5098538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098538 prefixEnd_5098538 := by exact prefixLift 5098538
  have htrace : WordTrace (prefixWord ++ tailWord_5098538) baseStart_5098538 baseEnd_5098538 := by
    simpa [prefixWord, tailWord_5098538, baseEnd_5098538] using wordTrace_append hprefix tailTrace_5098538
  have hstable : (prefixWord ++ tailWord_5098538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098538).length < 2 ^ (prefixWord ++ tailWord_5098538).sum := by decide
  have hdescent : baseEnd_5098538 < baseStart_5098538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098540 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_5098540 : Nat := 118140960795 + 5098540 * 2 ^ 59
def prefixEnd_5098540 : Nat := 4983230072969 + 3 ^ 40 * 5098540 * 2
def baseEnd_5098540 : Nat := 2618001656174587172502247

theorem tailTrace_5098540 : CollatzResearch.WordTrace tailWord_5098540 prefixEnd_5098540 2618001656174587172502247 := by
  unfold tailWord_5098540
  simp only [CollatzResearch.WordTrace]
  refine ⟨92979515474433908076130537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123972687299245210768174049 92979515474433908076130537)
  ·
    refine ⟨69734636605825431057097903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92979515474433908076130537 69734636605825431057097903)
    ·
      refine ⟨104601954908738146585646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69734636605825431057097903 104601954908738146585646855)
      ·
        refine ⟨156902932363107219878470283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104601954908738146585646855 156902932363107219878470283)
        ·
          refine ⟨235354398544660829817705425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156902932363107219878470283 235354398544660829817705425)
          ·
            refine ⟨176515798908495622363279069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235354398544660829817705425 176515798908495622363279069)
            ·
              refine ⟨66193424590685858386229651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176515798908495622363279069 66193424590685858386229651)
              ·
                refine ⟨99290136886028787579344477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66193424590685858386229651 99290136886028787579344477)
                ·
                  refine ⟨37233801332260795342254179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99290136886028787579344477 37233801332260795342254179)
                  ·
                    refine ⟨55850701998391193013381269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37233801332260795342254179 55850701998391193013381269)
                    ·
                      refine ⟨2618001656174587172502247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55850701998391193013381269 2618001656174587172502247)
                      ·
                        rfl

theorem cell23_5098540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_5098540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098540 prefixEnd_5098540 := by exact prefixLift 5098540
  have htrace : WordTrace (prefixWord ++ tailWord_5098540) baseStart_5098540 baseEnd_5098540 := by
    simpa [prefixWord, tailWord_5098540, baseEnd_5098540] using wordTrace_append hprefix tailTrace_5098540
  have hstable : (prefixWord ++ tailWord_5098540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098540).length < 2 ^ (prefixWord ++ tailWord_5098540).sum := by decide
  have hdescent : baseEnd_5098540 < baseStart_5098540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098547 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3]
def baseStart_5098547 : Nat := 118140960795 + 5098547 * 2 ^ 59
def prefixEnd_5098547 : Nat := 4983230072969 + 3 ^ 40 * 5098547 * 2
def baseEnd_5098547 : Nat := 2618005250539168645114715

theorem tailTrace_5098547 : CollatzResearch.WordTrace tailWord_5098547 prefixEnd_5098547 2618005250539168645114715 := by
  unfold tailWord_5098547
  simp only [CollatzResearch.WordTrace]
  refine ⟨185959286259842456347765895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123972857506561637565177263 185959286259842456347765895)
  ·
    refine ⟨278938929389763684521648843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185959286259842456347765895 278938929389763684521648843)
    ·
      refine ⟨418408394084645526782473265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278938929389763684521648843 418408394084645526782473265)
      ·
        refine ⟨313806295563484145086854949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418408394084645526782473265 313806295563484145086854949)
        ·
          refine ⟨58838680418153277203785303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313806295563484145086854949 58838680418153277203785303)
          ·
            refine ⟨88258020627229915805677955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58838680418153277203785303 88258020627229915805677955)
            ·
              refine ⟨132387030940844873708516933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88258020627229915805677955 132387030940844873708516933)
              ·
                refine ⟨24822568301408413820346925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132387030940844873708516933 24822568301408413820346925)
                ·
                  refine ⟨9308463113028155182630097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24822568301408413820346925 9308463113028155182630097)
                  ·
                    refine ⟨6981347334771116386972573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9308463113028155182630097 6981347334771116386972573)
                    ·
                      refine ⟨2618005250539168645114715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981347334771116386972573 2618005250539168645114715)
                      ·
                        rfl

theorem cell23_5098547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_5098547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098547 prefixEnd_5098547 := by exact prefixLift 5098547
  have htrace : WordTrace (prefixWord ++ tailWord_5098547) baseStart_5098547 baseEnd_5098547 := by
    simpa [prefixWord, tailWord_5098547, baseEnd_5098547] using wordTrace_append hprefix tailTrace_5098547
  have hstable : (prefixWord ++ tailWord_5098547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098547).length < 2 ^ (prefixWord ++ tailWord_5098547).sum := by decide
  have hdescent : baseEnd_5098547 < baseStart_5098547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098557 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5098557 : Nat := 118140960795 + 5098557 * 2 ^ 59
def prefixEnd_5098557 : Nat := 4983230072969 + 3 ^ 40 * 5098557 * 2
def baseEnd_5098557 : Nat := 2618010385345713605989669

theorem tailTrace_5098557 : CollatzResearch.WordTrace tailWord_5098557 prefixEnd_5098557 2618010385345713605989669 := by
  unfold tailWord_5098557
  simp only [CollatzResearch.WordTrace]
  refine ⟨185959650989806228055629925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123973100659870818703753283 185959650989806228055629925)
  ·
    refine ⟨34867434560588667760430611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185959650989806228055629925 34867434560588667760430611)
    ·
      refine ⟨52301151840883001640645917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34867434560588667760430611 52301151840883001640645917)
      ·
        refine ⟨19612931940331125615242219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52301151840883001640645917 19612931940331125615242219)
        ·
          refine ⟨29419397910496688422863329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19612931940331125615242219 29419397910496688422863329)
          ·
            refine ⟨22064548432872516317147497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29419397910496688422863329 22064548432872516317147497)
            ·
              refine ⟨16548411324654387237860623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22064548432872516317147497 16548411324654387237860623)
              ·
                refine ⟨24822616986981580856790935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548411324654387237860623 24822616986981580856790935)
                ·
                  refine ⟨37233925480472371285186403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24822616986981580856790935 37233925480472371285186403)
                  ·
                    refine ⟨55850888220708556927779605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37233925480472371285186403 55850888220708556927779605)
                    ·
                      refine ⟨2618010385345713605989669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55850888220708556927779605 2618010385345713605989669)
                      ·
                        rfl

theorem cell23_5098557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5098557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098557 prefixEnd_5098557 := by exact prefixLift 5098557
  have htrace : WordTrace (prefixWord ++ tailWord_5098557) baseStart_5098557 baseEnd_5098557 := by
    simpa [prefixWord, tailWord_5098557, baseEnd_5098557] using wordTrace_append hprefix tailTrace_5098557
  have hstable : (prefixWord ++ tailWord_5098557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098557).length < 2 ^ (prefixWord ++ tailWord_5098557).sum := by decide
  have hdescent : baseEnd_5098557 < baseStart_5098557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098577 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_5098577 : Nat := 118140960795 + 5098577 * 2 ^ 59
def prefixEnd_5098577 : Nat := 4983230072969 + 3 ^ 40 * 5098577 * 2
def baseEnd_5098577 : Nat := 2618020654958803527739577

theorem tailTrace_5098577 : CollatzResearch.WordTrace tailWord_5098577 prefixEnd_5098577 2618020654958803527739577 := by
  unfold tailWord_5098577
  simp only [CollatzResearch.WordTrace]
  refine ⟨185960380449733771471357985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123973586966489180980905323 185960380449733771471357985)
  ·
    refine ⟨139470285337300328603518489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185960380449733771471357985 139470285337300328603518489)
    ·
      refine ⟨104602714002975246452638867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139470285337300328603518489 104602714002975246452638867)
      ·
        refine ⟨156904071004462869678958301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104602714002975246452638867 156904071004462869678958301)
        ·
          refine ⟨58839026626673576129609363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156904071004462869678958301 58839026626673576129609363)
          ·
            refine ⟨88258539940010364194414045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58839026626673576129609363 88258539940010364194414045)
            ·
              refine ⟨33096952477503886572905267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88258539940010364194414045 33096952477503886572905267)
              ·
                refine ⟨49645428716255829859357901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33096952477503886572905267 49645428716255829859357901)
                ·
                  refine ⟨18617035768595936197259213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49645428716255829859357901 18617035768595936197259213)
                  ·
                    refine ⟨6981388413223476073972205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18617035768595936197259213 6981388413223476073972205)
                    ·
                      refine ⟨2618020654958803527739577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981388413223476073972205 2618020654958803527739577)
                      ·
                        rfl

theorem cell23_5098577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_5098577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098577 prefixEnd_5098577 := by exact prefixLift 5098577
  have htrace : WordTrace (prefixWord ++ tailWord_5098577) baseStart_5098577 baseEnd_5098577 := by
    simpa [prefixWord, tailWord_5098577, baseEnd_5098577] using wordTrace_append hprefix tailTrace_5098577
  have hstable : (prefixWord ++ tailWord_5098577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098577).length < 2 ^ (prefixWord ++ tailWord_5098577).sum := by decide
  have hdescent : baseEnd_5098577 < baseStart_5098577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098581 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5098581 : Nat := 118140960795 + 5098581 * 2 ^ 59
def prefixEnd_5098581 : Nat := 4983230072969 + 3 ^ 40 * 5098581 * 2
def baseEnd_5098581 : Nat := 2618022708881421512089559

theorem tailTrace_5098581 : CollatzResearch.WordTrace tailWord_5098581 prefixEnd_5098581 2618022708881421512089559 := by
  unfold tailWord_5098581
  simp only [CollatzResearch.WordTrace]
  refine ⟨185960526341719280154503597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123973684227812853436335731 185960526341719280154503597)
  ·
    refine ⟨69735197378144730057938849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185960526341719280154503597 69735197378144730057938849)
    ·
      refine ⟨52301398033608547543454137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69735197378144730057938849 52301398033608547543454137)
      ·
        refine ⟨39226048525206410657590603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52301398033608547543454137 39226048525206410657590603)
        ·
          refine ⟨58839072787809615986385905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39226048525206410657590603 58839072787809615986385905)
          ·
            refine ⟨44129304590857211989789429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58839072787809615986385905 44129304590857211989789429)
            ·
              refine ⟨4137122305392863624042759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44129304590857211989789429 4137122305392863624042759)
              ·
                refine ⟨6205683458089295436064139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137122305392863624042759 6205683458089295436064139)
                ·
                  refine ⟨9308525187133943154096209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205683458089295436064139 9308525187133943154096209)
                  ·
                    refine ⟨6981393890350457365572157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9308525187133943154096209 6981393890350457365572157)
                    ·
                      refine ⟨2618022708881421512089559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981393890350457365572157 2618022708881421512089559)
                      ·
                        rfl

theorem cell23_5098581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5098581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098581 prefixEnd_5098581 := by exact prefixLift 5098581
  have htrace : WordTrace (prefixWord ++ tailWord_5098581) baseStart_5098581 baseEnd_5098581 := by
    simpa [prefixWord, tailWord_5098581, baseEnd_5098581] using wordTrace_append hprefix tailTrace_5098581
  have hstable : (prefixWord ++ tailWord_5098581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098581).length < 2 ^ (prefixWord ++ tailWord_5098581).sum := by decide
  have hdescent : baseEnd_5098581 < baseStart_5098581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098589 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5098589 : Nat := 118140960795 + 5098589 * 2 ^ 59
def prefixEnd_5098589 : Nat := 4983230072969 + 3 ^ 40 * 5098589 * 2
def baseEnd_5098589 : Nat := 2618026816726657480789523

theorem tailTrace_5098589 : CollatzResearch.WordTrace tailWord_5098589 prefixEnd_5098589 2618026816726657480789523 := by
  unfold tailWord_5098589
  simp only [CollatzResearch.WordTrace]
  refine ⟨185960818125690297520794821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123973878750460198347196547 185960818125690297520794821)
  ·
    refine ⟨34867653398566930785149029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185960818125690297520794821 34867653398566930785149029)
    ·
      refine ⟨6537685012231299522215443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34867653398566930785149029 6537685012231299522215443)
      ·
        refine ⟨9806527518346949283323165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6537685012231299522215443 9806527518346949283323165)
        ·
          refine ⟨3677447819380105981246187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9806527518346949283323165 3677447819380105981246187)
          ·
            refine ⟨5516171729070158971869281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677447819380105981246187 5516171729070158971869281)
            ·
              refine ⟨4137128796802619228901961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5516171729070158971869281 4137128796802619228901961)
              ·
                refine ⟨3102846597601964421676471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4137128796802619228901961 3102846597601964421676471)
                ·
                  refine ⟨4654269896402946632514707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102846597601964421676471 4654269896402946632514707)
                  ·
                    refine ⟨6981404844604419948772061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4654269896402946632514707 6981404844604419948772061)
                    ·
                      refine ⟨2618026816726657480789523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981404844604419948772061 2618026816726657480789523)
                      ·
                        rfl

theorem cell23_5098589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5098589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098589 prefixEnd_5098589 := by exact prefixLift 5098589
  have htrace : WordTrace (prefixWord ++ tailWord_5098589) baseStart_5098589 baseEnd_5098589 := by
    simpa [prefixWord, tailWord_5098589, baseEnd_5098589] using wordTrace_append hprefix tailTrace_5098589
  have hstable : (prefixWord ++ tailWord_5098589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098589).length < 2 ^ (prefixWord ++ tailWord_5098589).sum := by decide
  have hdescent : baseEnd_5098589 < baseStart_5098589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098604 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 5, 3, 2]
def baseStart_5098604 : Nat := 118140960795 + 5098604 * 2 ^ 59
def prefixEnd_5098604 : Nat := 4983230072969 + 3 ^ 40 * 5098604 * 2
def baseEnd_5098604 : Nat := 2618034518936474922101953

theorem tailTrace_5098604 : CollatzResearch.WordTrace tailWord_5098604 prefixEnd_5098604 2618034518936474922101953 := by
  unfold tailWord_5098604
  simp only [CollatzResearch.WordTrace]
  refine ⟨92980682610317977541295433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123974243480423970055060577 92980682610317977541295433)
  ·
    refine ⟨69735511957738483155971575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92980682610317977541295433 69735511957738483155971575)
    ·
      refine ⟨104603267936607724733957363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69735511957738483155971575 104603267936607724733957363)
      ·
        refine ⟨156904901904911587100936045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104603267936607724733957363 156904901904911587100936045)
        ·
          refine ⟨58839338214341845162851017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156904901904911587100936045 58839338214341845162851017)
          ·
            refine ⟨44129503660756383872138263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58839338214341845162851017 44129503660756383872138263)
            ·
              refine ⟨66194255491134575808207395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44129503660756383872138263 66194255491134575808207395)
              ·
                refine ⟨99291383236701863712311093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66194255491134575808207395 99291383236701863712311093)
                ·
                  refine ⟨9308567178440799723029165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99291383236701863712311093 9308567178440799723029165)
                  ·
                    refine ⟨3490712691915299896135937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9308567178440799723029165 3490712691915299896135937)
                    ·
                      refine ⟨2618034518936474922101953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490712691915299896135937 2618034518936474922101953)
                      ·
                        rfl

theorem cell23_5098604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_5098604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098604 prefixEnd_5098604 := by exact prefixLift 5098604
  have htrace : WordTrace (prefixWord ++ tailWord_5098604) baseStart_5098604 baseEnd_5098604 := by
    simpa [prefixWord, tailWord_5098604, baseEnd_5098604] using wordTrace_append hprefix tailTrace_5098604
  have hstable : (prefixWord ++ tailWord_5098604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098604).length < 2 ^ (prefixWord ++ tailWord_5098604).sum := by decide
  have hdescent : baseEnd_5098604 < baseStart_5098604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098621 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 1, 3, 2]
def baseStart_5098621 : Nat := 118140960795 + 5098621 * 2 ^ 59
def prefixEnd_5098621 : Nat := 4983230072969 + 3 ^ 40 * 5098621 * 2
def baseEnd_5098621 : Nat := 2618043248107601355589375

theorem tailTrace_5098621 : CollatzResearch.WordTrace tailWord_5098621 prefixEnd_5098621 2618043248107601355589375 := by
  unfold tailWord_5098621
  simp only [CollatzResearch.WordTrace]
  refine ⟨185961985261574366985959717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123974656841049577990639811 185961985261574366985959717)
  ·
    refine ⟨34867872236545193809867447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185961985261574366985959717 34867872236545193809867447)
    ·
      refine ⟨52301808354817790714801171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34867872236545193809867447 52301808354817790714801171)
      ·
        refine ⟨78452712532226686072201757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52301808354817790714801171 78452712532226686072201757)
        ·
          refine ⟨29419767199585007277075659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78452712532226686072201757 29419767199585007277075659)
          ·
            refine ⟨44129650799377510915613489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29419767199585007277075659 44129650799377510915613489)
            ·
              refine ⟨33097238099533133186710117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44129650799377510915613489 33097238099533133186710117)
              ·
                refine ⟨6205732143662462472508147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33097238099533133186710117 6205732143662462472508147)
                ·
                  refine ⟨9308598215493693708762221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205732143662462472508147 9308598215493693708762221)
                  ·
                    refine ⟨3490724330810135140785833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9308598215493693708762221 3490724330810135140785833)
                    ·
                      refine ⟨2618043248107601355589375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490724330810135140785833 2618043248107601355589375)
                      ·
                        rfl

theorem cell23_5098621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_5098621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098621 prefixEnd_5098621 := by exact prefixLift 5098621
  have htrace : WordTrace (prefixWord ++ tailWord_5098621) baseStart_5098621 baseEnd_5098621 := by
    simpa [prefixWord, tailWord_5098621, baseEnd_5098621] using wordTrace_append hprefix tailTrace_5098621
  have hstable : (prefixWord ++ tailWord_5098621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098621).length < 2 ^ (prefixWord ++ tailWord_5098621).sum := by decide
  have hdescent : baseEnd_5098621 < baseStart_5098621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098638 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5098638 : Nat := 118140960795 + 5098638 * 2 ^ 59
def prefixEnd_5098638 : Nat := 4983230072969 + 3 ^ 40 * 5098638 * 2
def baseEnd_5098638 : Nat := 2618051977278727789076797

theorem tailTrace_5098638 : CollatzResearch.WordTrace tailWord_5098638 prefixEnd_5098638 2618051977278727789076797 := by
  unfold tailWord_5098638
  simp only [CollatzResearch.WordTrace]
  refine ⟨23245325662814097361166071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123975070201675185926219045 23245325662814097361166071)
  ·
    refine ⟨34867988494221146041749107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23245325662814097361166071 34867988494221146041749107)
    ·
      refine ⟨52301982741331719062623661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34867988494221146041749107 52301982741331719062623661)
      ·
        refine ⟨19613243527999394648483873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52301982741331719062623661 19613243527999394648483873)
        ·
          refine ⟨14709932645999545986362905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19613243527999394648483873 14709932645999545986362905)
          ·
            refine ⟨11032449484499659489772179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14709932645999545986362905 11032449484499659489772179)
            ·
              refine ⟨16548674226749489234658269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032449484499659489772179 16548674226749489234658269)
              ·
                refine ⟨6205752835031058462996851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16548674226749489234658269 6205752835031058462996851)
                ·
                  refine ⟨9308629252546587694495277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6205752835031058462996851 9308629252546587694495277)
                  ·
                    refine ⟨3490735969704970385435729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9308629252546587694495277 3490735969704970385435729)
                    ·
                      refine ⟨2618051977278727789076797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490735969704970385435729 2618051977278727789076797)
                      ·
                        rfl

theorem cell23_5098638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5098638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098638 prefixEnd_5098638 := by exact prefixLift 5098638
  have htrace : WordTrace (prefixWord ++ tailWord_5098638) baseStart_5098638 baseEnd_5098638 := by
    simpa [prefixWord, tailWord_5098638, baseEnd_5098638] using wordTrace_append hprefix tailTrace_5098638
  have hstable : (prefixWord ++ tailWord_5098638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098638).length < 2 ^ (prefixWord ++ tailWord_5098638).sum := by decide
  have hdescent : baseEnd_5098638 < baseStart_5098638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098687 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 7]
def baseStart_5098687 : Nat := 118140960795 + 5098687 * 2 ^ 59
def prefixEnd_5098687 : Nat := 4983230072969 + 3 ^ 40 * 5098687 * 2
def baseEnd_5098687 : Nat := 872692379276932699121357

theorem tailTrace_5098687 : CollatzResearch.WordTrace tailWord_5098687 prefixEnd_5098687 872692379276932699121357 := by
  unfold tailWord_5098687
  simp only [CollatzResearch.WordTrace]
  refine ⟨185964392479335260257862315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123976261652890173505241543 185964392479335260257862315)
  ·
    refine ⟨278946588719002890386793473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185964392479335260257862315 278946588719002890386793473)
    ·
      refine ⟨209209941539252167790095105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278946588719002890386793473 209209941539252167790095105)
      ·
        refine ⟨156907456154439125842571329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209209941539252167790095105 156907456154439125842571329)
        ·
          refine ⟨117680592115829344381928497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156907456154439125842571329 117680592115829344381928497)
          ·
            refine ⟨88260444086872008286446373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117680592115829344381928497 88260444086872008286446373)
            ·
              refine ⟨16548833266288501553708695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88260444086872008286446373 16548833266288501553708695)
              ·
                refine ⟨24823249899432752330563043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16548833266288501553708695 24823249899432752330563043)
                ·
                  refine ⟨37234874849149128495844565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24823249899432752330563043 37234874849149128495844565)
                  ·
                    refine ⟨872692379276932699121357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37234874849149128495844565 872692379276932699121357)
                    ·
                      rfl

theorem cell23_5098687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 7].length) (baseStart_5098687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098687 prefixEnd_5098687 := by exact prefixLift 5098687
  have htrace : WordTrace (prefixWord ++ tailWord_5098687) baseStart_5098687 baseEnd_5098687 := by
    simpa [prefixWord, tailWord_5098687, baseEnd_5098687] using wordTrace_append hprefix tailTrace_5098687
  have hstable : (prefixWord ++ tailWord_5098687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098687).length < 2 ^ (prefixWord ++ tailWord_5098687).sum := by decide
  have hdescent : baseEnd_5098687 < baseStart_5098687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098708 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 7]
def baseStart_5098708 : Nat := 118140960795 + 5098708 * 2 ^ 59
def prefixEnd_5098708 : Nat := 4983230072969 + 3 ^ 40 * 5098708 * 2
def baseEnd_5098708 : Nat := 290898657880504723911275

theorem tailTrace_5098708 : CollatzResearch.WordTrace tailWord_5098708 prefixEnd_5098708 290898657880504723911275 := by
  unfold tailWord_5098708
  simp only [CollatzResearch.WordTrace]
  refine ⟨92982579206129590422188389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123976772274839453896251185 92982579206129590422188389)
  ·
    refine ⟨17434233601149298204160323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92982579206129590422188389 17434233601149298204160323)
    ·
      refine ⟨26151350401723947306240485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434233601149298204160323 26151350401723947306240485)
      ·
        refine ⟨4903378200323240119920091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26151350401723947306240485 4903378200323240119920091)
        ·
          refine ⟨7355067300484860179880137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903378200323240119920091 7355067300484860179880137)
          ·
            refine ⟨5516300475363645134910103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7355067300484860179880137 5516300475363645134910103)
            ·
              refine ⟨8274450713045467702365155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516300475363645134910103 8274450713045467702365155)
              ·
                refine ⟨12411676069568201553547733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8274450713045467702365155 12411676069568201553547733)
                ·
                  refine ⟨290898657880504723911275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12411676069568201553547733 290898657880504723911275)
                  ·
                    rfl

theorem cell23_5098708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_5098708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098708 prefixEnd_5098708 := by exact prefixLift 5098708
  have htrace : WordTrace (prefixWord ++ tailWord_5098708) baseStart_5098708 baseEnd_5098708 := by
    simpa [prefixWord, tailWord_5098708, baseEnd_5098708] using wordTrace_append hprefix tailTrace_5098708
  have hstable : (prefixWord ++ tailWord_5098708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098708).length < 2 ^ (prefixWord ++ tailWord_5098708).sum := by decide
  have hdescent : baseEnd_5098708 < baseStart_5098708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098737 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_5098737 : Nat := 118140960795 + 5098737 * 2 ^ 59
def prefixEnd_5098737 : Nat := 4983230072969 + 3 ^ 40 * 5098737 * 2
def baseEnd_5098737 : Nat := 2618102811863522901738841

theorem tailTrace_5098737 : CollatzResearch.WordTrace tailWord_5098737 prefixEnd_5098737 2618102811863522901738841 := by
  unfold tailWord_5098737
  simp only [CollatzResearch.WordTrace]
  refine ⟨185966216129154118797182465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123977477419436079198121643 185966216129154118797182465)
  ·
    refine ⟨139474662096865589097886849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185966216129154118797182465 139474662096865589097886849)
    ·
      refine ⟨104605996572649191823415137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139474662096865589097886849 104605996572649191823415137)
      ·
        refine ⟨78454497429486893867561353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104605996572649191823415137 78454497429486893867561353)
        ·
          refine ⟨58840873072115170400671015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78454497429486893867561353 58840873072115170400671015)
          ·
            refine ⟨88261309608172755601006523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58840873072115170400671015 88261309608172755601006523)
            ·
              refine ⟨132391964412259133401509785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88261309608172755601006523 132391964412259133401509785)
              ·
                refine ⟨99293973309194350051132339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132391964412259133401509785 99293973309194350051132339)
                ·
                  refine ⟨148940959963791525076698509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99293973309194350051132339 148940959963791525076698509)
                  ·
                    refine ⟨55852859986421821903761941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148940959963791525076698509 55852859986421821903761941)
                    ·
                      refine ⟨2618102811863522901738841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55852859986421821903761941 2618102811863522901738841)
                      ·
                        rfl

theorem cell23_5098737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_5098737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098737 prefixEnd_5098737 := by exact prefixLift 5098737
  have htrace : WordTrace (prefixWord ++ tailWord_5098737) baseStart_5098737 baseEnd_5098737 := by
    simpa [prefixWord, tailWord_5098737, baseEnd_5098737] using wordTrace_append hprefix tailTrace_5098737
  have hstable : (prefixWord ++ tailWord_5098737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098737).length < 2 ^ (prefixWord ++ tailWord_5098737).sum := by decide
  have hdescent : baseEnd_5098737 < baseStart_5098737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098764 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 6]
def baseStart_5098764 : Nat := 118140960795 + 5098764 * 2 ^ 59
def prefixEnd_5098764 : Nat := 4983230072969 + 3 ^ 40 * 5098764 * 2
def baseEnd_5098764 : Nat := 290901852871243810677913

theorem tailTrace_5098764 : CollatzResearch.WordTrace tailWord_5098764 prefixEnd_5098764 290901852871243810677913 := by
  unfold tailWord_5098764
  simp only [CollatzResearch.WordTrace]
  refine ⟨92983600450028151204207673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123978133933370868272276897 92983600450028151204207673)
  ·
    refine ⟨69737700337521113403155755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92983600450028151204207673 69737700337521113403155755)
    ·
      refine ⟨104606550506281670104733633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69737700337521113403155755 104606550506281670104733633)
      ·
        refine ⟨78454912879711252578550225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104606550506281670104733633 78454912879711252578550225)
        ·
          refine ⟨58841184659783439433912669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78454912879711252578550225 58841184659783439433912669)
          ·
            refine ⟨22065444247418789787717251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58841184659783439433912669 22065444247418789787717251)
            ·
              refine ⟨33098166371128184681575877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22065444247418789787717251 33098166371128184681575877)
              ·
                refine ⟨6205906194586534627795477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33098166371128184681575877 6205906194586534627795477)
                ·
                  refine ⟨290901852871243810677913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6205906194586534627795477 290901852871243810677913)
                  ·
                    rfl

theorem cell23_5098764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_5098764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098764 prefixEnd_5098764 := by exact prefixLift 5098764
  have htrace : WordTrace (prefixWord ++ tailWord_5098764) baseStart_5098764 baseEnd_5098764 := by
    simpa [prefixWord, tailWord_5098764, baseEnd_5098764] using wordTrace_append hprefix tailTrace_5098764
  have hstable : (prefixWord ++ tailWord_5098764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098764).length < 2 ^ (prefixWord ++ tailWord_5098764).sum := by decide
  have hdescent : baseEnd_5098764 < baseStart_5098764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098781 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 6]
def baseStart_5098781 : Nat := 118140960795 + 5098781 * 2 ^ 59
def prefixEnd_5098781 : Nat := 4983230072969 + 3 ^ 40 * 5098781 * 2
def baseEnd_5098781 : Nat := 290902822779146747732071

theorem tailTrace_5098781 : CollatzResearch.WordTrace tailWord_5098781 prefixEnd_5098781 290902822779146747732071 := by
  unfold tailWord_5098781
  simp only [CollatzResearch.WordTrace]
  refine ⟨185967820940994714311784197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123978547293996476207856131 185967820940994714311784197)
  ·
    refine ⟨34868966426436508933459537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185967820940994714311784197 34868966426436508933459537)
    ·
      refine ⟨26151724819827381700094653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34868966426436508933459537 26151724819827381700094653)
      ·
        refine ⟨9806896807435268137535495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26151724819827381700094653 9806896807435268137535495)
        ·
          refine ⟨14710345211152902206303243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806896807435268137535495 14710345211152902206303243)
          ·
            refine ⟨22065517816729353309454865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14710345211152902206303243 22065517816729353309454865)
            ·
              refine ⟨16549138362547014982091149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22065517816729353309454865 16549138362547014982091149)
              ·
                refine ⟨6205926885955130618284181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549138362547014982091149 6205926885955130618284181)
                ·
                  refine ⟨290902822779146747732071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6205926885955130618284181 290902822779146747732071)
                  ·
                    rfl

theorem cell23_5098781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_5098781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098781 prefixEnd_5098781 := by exact prefixLift 5098781
  have htrace : WordTrace (prefixWord ++ tailWord_5098781) baseStart_5098781 baseEnd_5098781 := by
    simpa [prefixWord, tailWord_5098781, baseEnd_5098781] using wordTrace_append hprefix tailTrace_5098781
  have hstable : (prefixWord ++ tailWord_5098781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098781).length < 2 ^ (prefixWord ++ tailWord_5098781).sum := by decide
  have hdescent : baseEnd_5098781 < baseStart_5098781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098841 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 2, 4]
def baseStart_5098841 : Nat := 118140960795 + 5098841 * 2 ^ 59
def prefixEnd_5098841 : Nat := 4983230072969 + 3 ^ 40 * 5098841 * 2
def baseEnd_5098841 : Nat := 872718737950530164946121

theorem tailTrace_5098841 : CollatzResearch.WordTrace tailWord_5098841 prefixEnd_5098841 872718737950530164946121 := by
  unfold tailWord_5098841
  simp only [CollatzResearch.WordTrace]
  refine ⟨185970009320777344558968377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123980006213851563039312251 185970009320777344558968377)
  ·
    refine ⟨139477506990583008419226283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185970009320777344558968377 139477506990583008419226283)
    ·
      refine ⟨209216260485874512628839425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139477506990583008419226283 209216260485874512628839425)
      ·
        refine ⟨156912195364405884471629569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209216260485874512628839425 156912195364405884471629569)
        ·
          refine ⟨117684146523304413353722177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156912195364405884471629569 117684146523304413353722177)
          ·
            refine ⟨88263109892478310015291633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117684146523304413353722177 88263109892478310015291633)
            ·
              refine ⟨66197332419358732511468725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88263109892478310015291633 66197332419358732511468725)
              ·
                refine ⟨6205999914314881172950193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66197332419358732511468725 6205999914314881172950193)
                ·
                  refine ⟨4654499935736160879712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6205999914314881172950193 4654499935736160879712645)
                  ·
                    refine ⟨872718737950530164946121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4654499935736160879712645 872718737950530164946121)
                    ·
                      rfl

theorem cell23_5098841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 4].length) (baseStart_5098841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098841 prefixEnd_5098841 := by exact prefixLift 5098841
  have htrace : WordTrace (prefixWord ++ tailWord_5098841) baseStart_5098841 baseEnd_5098841 := by
    simpa [prefixWord, tailWord_5098841, baseEnd_5098841] using wordTrace_append hprefix tailTrace_5098841
  have hstable : (prefixWord ++ tailWord_5098841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098841).length < 2 ^ (prefixWord ++ tailWord_5098841).sum := by decide
  have hdescent : baseEnd_5098841 < baseStart_5098841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098848 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_5098848 : Nat := 118140960795 + 5098848 * 2 ^ 59
def prefixEnd_5098848 : Nat := 4983230072969 + 3 ^ 40 * 5098848 * 2
def baseEnd_5098848 : Nat := 2618159808216171967450831

theorem tailTrace_5098848 : CollatzResearch.WordTrace tailWord_5098848 prefixEnd_5098848 2618159808216171967450831 := by
  unfold tailWord_5098848
  simp only [CollatzResearch.WordTrace]
  refine ⟨92985132315875992377236599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123980176421167989836315465 92985132315875992377236599)
  ·
    refine ⟨139477698473813988565854899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92985132315875992377236599 139477698473813988565854899)
    ·
      refine ⟨209216547710720982848782349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139477698473813988565854899 209216547710720982848782349)
      ·
        refine ⟨78456205391520368568293381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209216547710720982848782349 78456205391520368568293381)
        ·
          refine ⟨14710538510910069106555009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78456205391520368568293381 14710538510910069106555009)
          ·
            refine ⟨11032903883182551829916257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14710538510910069106555009 11032903883182551829916257)
            ·
              refine ⟨8274677912386913872437193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11032903883182551829916257 8274677912386913872437193)
              ·
                refine ⟨6206008434290185404327895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8274677912386913872437193 6206008434290185404327895)
                ·
                  refine ⟨9309012651435278106491843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206008434290185404327895 9309012651435278106491843)
                  ·
                    refine ⟨13963518977152917159737765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9309012651435278106491843 13963518977152917159737765)
                    ·
                      refine ⟨2618159808216171967450831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13963518977152917159737765 2618159808216171967450831)
                      ·
                        rfl

theorem cell23_5098848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_5098848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098848 prefixEnd_5098848 := by exact prefixLift 5098848
  have htrace : WordTrace (prefixWord ++ tailWord_5098848) baseStart_5098848 baseEnd_5098848 := by
    simpa [prefixWord, tailWord_5098848, baseEnd_5098848] using wordTrace_append hprefix tailTrace_5098848
  have hstable : (prefixWord ++ tailWord_5098848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098848).length < 2 ^ (prefixWord ++ tailWord_5098848).sum := by decide
  have hdescent : baseEnd_5098848 < baseStart_5098848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098941 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_5098941 : Nat := 118140960795 + 5098941 * 2 ^ 59
def prefixEnd_5098941 : Nat := 4983230072969 + 3 ^ 40 * 5098941 * 2
def baseEnd_5098941 : Nat := 2618207561917040103587903

theorem tailTrace_5098941 : CollatzResearch.WordTrace tailWord_5098941 prefixEnd_5098941 2618207561917040103587903 := by
  unfold tailWord_5098941
  simp only [CollatzResearch.WordTrace]
  refine ⟨185973656620415061637608677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123982437746943374425072451 185973656620415061637608677)
  ·
    refine ⟨34870060616327824057051627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185973656620415061637608677 34870060616327824057051627)
    ·
      refine ⟨52305090924491736085577441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34870060616327824057051627 52305090924491736085577441)
      ·
        refine ⟨39228818193368802064183081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52305090924491736085577441 39228818193368802064183081)
        ·
          refine ⟨29421613645026601548137311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39228818193368802064183081 29421613645026601548137311)
          ·
            refine ⟨44132420467539902322205967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29421613645026601548137311 44132420467539902322205967)
            ·
              refine ⟨66198630701309853483308951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44132420467539902322205967 66198630701309853483308951)
              ·
                refine ⟨99297946051964780224963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66198630701309853483308951 99297946051964780224963427)
                ·
                  refine ⟨148946919077947170337445141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99297946051964780224963427 148946919077947170337445141)
                  ·
                    refine ⟨6981886831778773609567741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148946919077947170337445141 6981886831778773609567741)
                    ·
                      refine ⟨2618207561917040103587903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6981886831778773609567741 2618207561917040103587903)
                      ·
                        rfl

theorem cell23_5098941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_5098941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098941 prefixEnd_5098941 := by exact prefixLift 5098941
  have htrace : WordTrace (prefixWord ++ tailWord_5098941) baseStart_5098941 baseEnd_5098941 := by
    simpa [prefixWord, tailWord_5098941, baseEnd_5098941] using wordTrace_append hprefix tailTrace_5098941
  have hstable : (prefixWord ++ tailWord_5098941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098941).length < 2 ^ (prefixWord ++ tailWord_5098941).sum := by decide
  have hdescent : baseEnd_5098941 < baseStart_5098941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098948 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5098948 : Nat := 118140960795 + 5098948 * 2 ^ 59
def prefixEnd_5098948 : Nat := 4983230072969 + 3 ^ 40 * 5098948 * 2
def baseEnd_5098948 : Nat := 872737052093873858733457

theorem tailTrace_5098948 : CollatzResearch.WordTrace tailWord_5098948 prefixEnd_5098948 872737052093873858733457 := by
  unfold tailWord_5098948
  simp only [CollatzResearch.WordTrace]
  refine ⟨92986955965694850916556749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123982607954259801222075665 92986955965694850916556749)
  ·
    refine ⟨34870108487135569093708781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92986955965694850916556749 34870108487135569093708781)
    ·
      refine ⟨13076290682675838410140793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34870108487135569093708781 13076290682675838410140793)
      ·
        refine ⟨9807218012006878807605595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13076290682675838410140793 9807218012006878807605595)
        ·
          refine ⟨14710827018010318211408393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9807218012006878807605595 14710827018010318211408393)
          ·
            refine ⟨11033120263507738658556295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14710827018010318211408393 11033120263507738658556295)
            ·
              refine ⟨16549680395261607987834443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033120263507738658556295 16549680395261607987834443)
              ·
                refine ⟨24824520592892411981751665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16549680395261607987834443 24824520592892411981751665)
                ·
                  refine ⟨18618390444669308986313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24824520592892411981751665 18618390444669308986313749)
                  ·
                    refine ⟨872737052093873858733457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18618390444669308986313749 872737052093873858733457)
                    ·
                      rfl

theorem cell23_5098948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5098948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098948 prefixEnd_5098948 := by exact prefixLift 5098948
  have htrace : WordTrace (prefixWord ++ tailWord_5098948) baseStart_5098948 baseEnd_5098948 := by
    simpa [prefixWord, tailWord_5098948, baseEnd_5098948] using wordTrace_append hprefix tailTrace_5098948
  have hstable : (prefixWord ++ tailWord_5098948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098948).length < 2 ^ (prefixWord ++ tailWord_5098948).sum := by decide
  have hdescent : baseEnd_5098948 < baseStart_5098948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098951 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_5098951 : Nat := 118140960795 + 5098951 * 2 ^ 59
def prefixEnd_5098951 : Nat := 4983230072969 + 3 ^ 40 * 5098951 * 2
def baseEnd_5098951 : Nat := 2618212696723585064462857

theorem tailTrace_5098951 : CollatzResearch.WordTrace tailWord_5098951 prefixEnd_5098951 2618212696723585064462857 := by
  unfold tailWord_5098951
  simp only [CollatzResearch.WordTrace]
  refine ⟨185974021350378833345472707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123982680900252555563648471 185974021350378833345472707)
  ·
    refine ⟨278961032025568250018209061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185974021350378833345472707 278961032025568250018209061)
    ·
      refine ⟨52305193504794046878414199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 278961032025568250018209061 52305193504794046878414199)
      ·
        refine ⟨78457790257191070317621299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52305193504794046878414199 78457790257191070317621299)
        ·
          refine ⟨117686685385786605476431949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78457790257191070317621299 117686685385786605476431949)
          ·
            refine ⟨44132507019669977053661981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117686685385786605476431949 44132507019669977053661981)
            ·
              refine ⟨16549690132376241395123243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44132507019669977053661981 16549690132376241395123243)
              ·
                refine ⟨24824535198564362092684865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16549690132376241395123243 24824535198564362092684865)
                ·
                  refine ⟨18618401398923271569513649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24824535198564362092684865 18618401398923271569513649)
                  ·
                    refine ⟨13963801049192453677135237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18618401398923271569513649 13963801049192453677135237)
                    ·
                      refine ⟨2618212696723585064462857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13963801049192453677135237 2618212696723585064462857)
                      ·
                        rfl

theorem cell23_5098951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_5098951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098951 prefixEnd_5098951 := by exact prefixLift 5098951
  have htrace : WordTrace (prefixWord ++ tailWord_5098951) baseStart_5098951 baseEnd_5098951 := by
    simpa [prefixWord, tailWord_5098951, baseEnd_5098951] using wordTrace_append hprefix tailTrace_5098951
  have hstable : (prefixWord ++ tailWord_5098951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098951).length < 2 ^ (prefixWord ++ tailWord_5098951).sum := by decide
  have hdescent : baseEnd_5098951 < baseStart_5098951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098955 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 2, 2, 2]
def baseStart_5098955 : Nat := 118140960795 + 5098955 * 2 ^ 59
def prefixEnd_5098955 : Nat := 4983230072969 + 3 ^ 40 * 5098955 * 2
def baseEnd_5098955 : Nat := 2618214750646203048812839

theorem tailTrace_5098955 : CollatzResearch.WordTrace tailWord_5098955 prefixEnd_5098955 2618214750646203048812839 := by
  unfold tailWord_5098955
  simp only [CollatzResearch.WordTrace]
  refine ⟨185974167242364342028618319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123982778161576228019078879 185974167242364342028618319)
  ·
    refine ⟨278961250863546513042927479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185974167242364342028618319 278961250863546513042927479)
    ·
      refine ⟨418441876295319769564391219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278961250863546513042927479 418441876295319769564391219)
      ·
        refine ⟨627662814442979654346586829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418441876295319769564391219 627662814442979654346586829)
        ·
          refine ⟨235373555416117370379970061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627662814442979654346586829 235373555416117370379970061)
          ·
            refine ⟨88265083281044013892488773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235373555416117370379970061 88265083281044013892488773)
            ·
              refine ⟨16549703115195752604841645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88265083281044013892488773 16549703115195752604841645)
              ·
                refine ⟨6206138668198407226815617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549703115195752604841645 6206138668198407226815617)
                ·
                  refine ⟨4654604001148805420111713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206138668198407226815617 4654604001148805420111713)
                  ·
                    refine ⟨3490953000861604065083785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654604001148805420111713 3490953000861604065083785)
                    ·
                      refine ⟨2618214750646203048812839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490953000861604065083785 2618214750646203048812839)
                      ·
                        rfl

theorem cell23_5098955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 2, 2].length) (baseStart_5098955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098955 prefixEnd_5098955 := by exact prefixLift 5098955
  have htrace : WordTrace (prefixWord ++ tailWord_5098955) baseStart_5098955 baseEnd_5098955 := by
    simpa [prefixWord, tailWord_5098955, baseEnd_5098955] using wordTrace_append hprefix tailTrace_5098955
  have hstable : (prefixWord ++ tailWord_5098955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098955).length < 2 ^ (prefixWord ++ tailWord_5098955).sum := by decide
  have hdescent : baseEnd_5098955 < baseStart_5098955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5098991 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 2, 5]
def baseStart_5098991 : Nat := 118140960795 + 5098991 * 2 ^ 59
def prefixEnd_5098991 : Nat := 4983230072969 + 3 ^ 40 * 5098991 * 2
def baseEnd_5098991 : Nat := 872744411983254969320891

theorem tailTrace_5098991 : CollatzResearch.WordTrace tailWord_5098991 prefixEnd_5098991 872744411983254969320891 := by
  unfold tailWord_5098991
  simp only [CollatzResearch.WordTrace]
  refine ⟨185975480270233920176928827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123983653513489280117952551 185975480270233920176928827)
  ·
    refine ⟨278963220405350880265393241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185975480270233920176928827 278963220405350880265393241)
    ·
      refine ⟨209222415304013160199044931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278963220405350880265393241 209222415304013160199044931)
      ·
        refine ⟨313833622956019740298567397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209222415304013160199044931 313833622956019740298567397)
        ·
          refine ⟨58843804304253701305981387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313833622956019740298567397 58843804304253701305981387)
          ·
            refine ⟨88265706456380551958972081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58843804304253701305981387 88265706456380551958972081)
            ·
              refine ⟨66199279842285413969229061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88265706456380551958972081 66199279842285413969229061)
              ·
                refine ⟨12412364970428515119230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66199279842285413969229061 12412364970428515119230449)
                ·
                  refine ⟨9309273727821386339422837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12412364970428515119230449 9309273727821386339422837)
                  ·
                    refine ⟨872744411983254969320891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9309273727821386339422837 872744411983254969320891)
                    ·
                      rfl

theorem cell23_5098991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_5098991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5098991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5098991 prefixEnd_5098991 := by exact prefixLift 5098991
  have htrace : WordTrace (prefixWord ++ tailWord_5098991) baseStart_5098991 baseEnd_5098991 := by
    simpa [prefixWord, tailWord_5098991, baseEnd_5098991] using wordTrace_append hprefix tailTrace_5098991
  have hstable : (prefixWord ++ tailWord_5098991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5098991).length < 2 ^ (prefixWord ++ tailWord_5098991).sum := by decide
  have hdescent : baseEnd_5098991 < baseStart_5098991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5098991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099006 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5099006 : Nat := 118140960795 + 5099006 * 2 ^ 59
def prefixEnd_5099006 : Nat := 4983230072969 + 3 ^ 40 * 5099006 * 2
def baseEnd_5099006 : Nat := 2618240938159582349275105

theorem tailTrace_5099006 : CollatzResearch.WordTrace tailWord_5099006 prefixEnd_5099006 2618240938159582349275105 := by
  unfold tailWord_5099006
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247003420647447217340609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123984018243453051825816581 23247003420647447217340609)
  ·
    refine ⟨17435252565485585413005457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23247003420647447217340609 17435252565485585413005457)
    ·
      refine ⟨13076439424114189059754093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17435252565485585413005457 13076439424114189059754093)
      ·
        refine ⟨4903664784042820897407785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13076439424114189059754093 4903664784042820897407785)
        ·
          refine ⟨3677748588032115673055839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4903664784042820897407785 3677748588032115673055839)
          ·
            refine ⟨5516622882048173509583759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677748588032115673055839 5516622882048173509583759)
            ·
              refine ⟨8274934323072260264375639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516622882048173509583759 8274934323072260264375639)
              ·
                refine ⟨12412401484608390396563459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8274934323072260264375639 12412401484608390396563459)
                ·
                  refine ⟨18618602226912585594845189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12412401484608390396563459 18618602226912585594845189)
                  ·
                    refine ⟨3490987917546109799033473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18618602226912585594845189 3490987917546109799033473)
                    ·
                      refine ⟨2618240938159582349275105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3490987917546109799033473 2618240938159582349275105)
                      ·
                        rfl

theorem cell23_5099006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5099006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099006 prefixEnd_5099006 := by exact prefixLift 5099006
  have htrace : WordTrace (prefixWord ++ tailWord_5099006) baseStart_5099006 baseEnd_5099006 := by
    simpa [prefixWord, tailWord_5099006, baseEnd_5099006] using wordTrace_append hprefix tailTrace_5099006
  have hstable : (prefixWord ++ tailWord_5099006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099006).length < 2 ^ (prefixWord ++ tailWord_5099006).sum := by decide
  have hdescent : baseEnd_5099006 < baseStart_5099006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099011 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4]
def baseStart_5099011 : Nat := 118140960795 + 5099011 * 2 ^ 59
def prefixEnd_5099011 : Nat := 4983230072969 + 3 ^ 40 * 5099011 * 2
def baseEnd_5099011 : Nat := 2618243505562854829712581

theorem tailTrace_5099011 : CollatzResearch.WordTrace tailWord_5099011 prefixEnd_5099011 2618243505562854829712581 := by
  unfold tailWord_5099011
  simp only [CollatzResearch.WordTrace]
  refine ⟨185976209730161463592656887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123984139820107642395104591 185976209730161463592656887)
  ·
    refine ⟨278964314595242195388985331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185976209730161463592656887 278964314595242195388985331)
    ·
      refine ⟨418446471892863293083477997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278964314595242195388985331 418446471892863293083477997)
      ·
        refine ⟨156917426959823734906304249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418446471892863293083477997 156917426959823734906304249)
        ·
          refine ⟨117688070219867801179728187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156917426959823734906304249 117688070219867801179728187)
          ·
            refine ⟨176532105329801701769592281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117688070219867801179728187 176532105329801701769592281)
            ·
              refine ⟨132399078997351276327194211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176532105329801701769592281 132399078997351276327194211)
              ·
                refine ⟨198598618496026914490791317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132399078997351276327194211 198598618496026914490791317)
                ·
                  refine ⟨9309310242001261616755843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198598618496026914490791317 9309310242001261616755843)
                  ·
                    refine ⟨13963965363001892425133765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9309310242001261616755843 13963965363001892425133765)
                    ·
                      refine ⟨2618243505562854829712581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13963965363001892425133765 2618243505562854829712581)
                      ·
                        rfl

theorem cell23_5099011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_5099011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099011 prefixEnd_5099011 := by exact prefixLift 5099011
  have htrace : WordTrace (prefixWord ++ tailWord_5099011) baseStart_5099011 baseEnd_5099011 := by
    simpa [prefixWord, tailWord_5099011, baseEnd_5099011] using wordTrace_append hprefix tailTrace_5099011
  have hstable : (prefixWord ++ tailWord_5099011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099011).length < 2 ^ (prefixWord ++ tailWord_5099011).sum := by decide
  have hdescent : baseEnd_5099011 < baseStart_5099011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099098 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_5099098 : Nat := 118140960795 + 5099098 * 2 ^ 59
def prefixEnd_5099098 : Nat := 4983230072969 + 3 ^ 40 * 5099098 * 2
def baseEnd_5099098 : Nat := 872762726126598663108227

theorem tailTrace_5099098 : CollatzResearch.WordTrace tailWord_5099098 prefixEnd_5099098 872762726126598663108227 := by
  unfold tailWord_5099098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46494845720211569362768487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123986255253897518300715965 46494845720211569362768487)
  ·
    refine ⟨69742268580317354044152731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46494845720211569362768487 69742268580317354044152731)
    ·
      refine ⟨104613402870476031066229097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69742268580317354044152731 104613402870476031066229097)
      ·
        refine ⟨78460052152857023299671823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104613402870476031066229097 78460052152857023299671823)
        ·
          refine ⟨117690078229285534949507735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78460052152857023299671823 117690078229285534949507735)
          ·
            refine ⟨176535117343928302424261603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117690078229285534949507735 176535117343928302424261603)
            ·
              refine ⟨264802676015892453636392405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176535117343928302424261603 264802676015892453636392405)
              ·
                refine ⟨6206312719122479382102947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 264802676015892453636392405 6206312719122479382102947)
                ·
                  refine ⟨9309469078683719073154421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206312719122479382102947 9309469078683719073154421)
                  ·
                    refine ⟨872762726126598663108227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9309469078683719073154421 872762726126598663108227)
                    ·
                      rfl

theorem cell23_5099098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_5099098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099098 prefixEnd_5099098 := by exact prefixLift 5099098
  have htrace : WordTrace (prefixWord ++ tailWord_5099098) baseStart_5099098 baseEnd_5099098 := by
    simpa [prefixWord, tailWord_5099098, baseEnd_5099098] using wordTrace_append hprefix tailTrace_5099098
  have hstable : (prefixWord ++ tailWord_5099098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099098).length < 2 ^ (prefixWord ++ tailWord_5099098).sum := by decide
  have hdescent : baseEnd_5099098 < baseStart_5099098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099105 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_5099105 : Nat := 118140960795 + 5099105 * 2 ^ 59
def prefixEnd_5099105 : Nat := 4983230072969 + 3 ^ 40 * 5099105 * 2
def baseEnd_5099105 : Nat := 2618291772744377461937149

theorem tailTrace_5099105 : CollatzResearch.WordTrace tailWord_5099105 prefixEnd_5099105 2618291772744377461937149 := by
  unfold tailWord_5099105
  simp only [CollatzResearch.WordTrace]
  refine ⟨185979638191820917646578769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123986425461213945097719179 185979638191820917646578769)
  ·
    refine ⟨139484728643865688234934077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185979638191820917646578769 139484728643865688234934077)
    ·
      refine ⟨52306773241449633088100279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139484728643865688234934077 52306773241449633088100279)
      ·
        refine ⟨78460159862174449632150419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52306773241449633088100279 78460159862174449632150419)
        ·
          refine ⟨117690239793261674448225629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78460159862174449632150419 117690239793261674448225629)
          ·
            refine ⟨44133839922473127918084611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117690239793261674448225629 44133839922473127918084611)
            ·
              refine ⟨66200759883709691877126917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44133839922473127918084611 66200759883709691877126917)
              ·
                refine ⟨12412642478195567226961297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66200759883709691877126917 12412642478195567226961297)
                ·
                  refine ⟨9309481858646675420220973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12412642478195567226961297 9309481858646675420220973)
                  ·
                    refine ⟨3491055696992503282582865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9309481858646675420220973 3491055696992503282582865)
                    ·
                      refine ⟨2618291772744377461937149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491055696992503282582865 2618291772744377461937149)
                      ·
                        rfl

theorem cell23_5099105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_5099105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099105 prefixEnd_5099105 := by exact prefixLift 5099105
  have htrace : WordTrace (prefixWord ++ tailWord_5099105) baseStart_5099105 baseEnd_5099105 := by
    simpa [prefixWord, tailWord_5099105, baseEnd_5099105] using wordTrace_append hprefix tailTrace_5099105
  have hstable : (prefixWord ++ tailWord_5099105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099105).length < 2 ^ (prefixWord ++ tailWord_5099105).sum := by decide
  have hdescent : baseEnd_5099105 < baseStart_5099105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099148 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5099148 : Nat := 118140960795 + 5099148 * 2 ^ 59
def prefixEnd_5099148 : Nat := 4983230072969 + 3 ^ 40 * 5099148 * 2
def baseEnd_5099148 : Nat := 2618313852412520793699451

theorem tailTrace_5099148 : CollatzResearch.WordTrace tailWord_5099148 prefixEnd_5099148 2618313852412520793699451 := by
  unfold tailWord_5099148
  simp only [CollatzResearch.WordTrace]
  refine ⟨92990603265332567995197049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123987471020443423993596065 92990603265332567995197049)
  ·
    refine ⟨69742952448999425996397787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92990603265332567995197049 69742952448999425996397787)
    ·
      refine ⟨104614428673499138994596681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69742952448999425996397787 104614428673499138994596681)
      ·
        refine ⟨78460821505124354245947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104614428673499138994596681 78460821505124354245947511)
        ·
          refine ⟨117691232257686531368921267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78460821505124354245947511 117691232257686531368921267)
          ·
            refine ⟨176536848386529797053381901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117691232257686531368921267 176536848386529797053381901)
            ·
              refine ⟨66201318144948673895018213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176536848386529797053381901 66201318144948673895018213)
              ·
                refine ⟨12412747152177876355315915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66201318144948673895018213 12412747152177876355315915)
                ·
                  refine ⟨18619120728266814532973873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12412747152177876355315915 18619120728266814532973873)
                  ·
                    refine ⟨13964340546200110899730405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18619120728266814532973873 13964340546200110899730405)
                    ·
                      refine ⟨2618313852412520793699451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13964340546200110899730405 2618313852412520793699451)
                      ·
                        rfl

theorem cell23_5099148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5099148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099148 prefixEnd_5099148 := by exact prefixLift 5099148
  have htrace : WordTrace (prefixWord ++ tailWord_5099148) baseStart_5099148 baseEnd_5099148 := by
    simpa [prefixWord, tailWord_5099148, baseEnd_5099148] using wordTrace_append hprefix tailTrace_5099148
  have hstable : (prefixWord ++ tailWord_5099148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099148).length < 2 ^ (prefixWord ++ tailWord_5099148).sum := by decide
  have hdescent : baseEnd_5099148 < baseStart_5099148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099169 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5099169 : Nat := 118140960795 + 5099169 * 2 ^ 59
def prefixEnd_5099169 : Nat := 4983230072969 + 3 ^ 40 * 5099169 * 2
def baseEnd_5099169 : Nat := 2618324635506265211536855

theorem tailTrace_5099169 : CollatzResearch.WordTrace tailWord_5099169 prefixEnd_5099169 2618324635506265211536855 := by
  unfold tailWord_5099169
  simp only [CollatzResearch.WordTrace]
  refine ⟨185981972463589056576908561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123987981642392704384605707 185981972463589056576908561)
  ·
    refine ⟨139486479347691792432681421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185981972463589056576908561 139486479347691792432681421)
    ·
      refine ⟨52307429755384422162255533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139486479347691792432681421 52307429755384422162255533)
      ·
        refine ⟨19615286158269158310845825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52307429755384422162255533 19615286158269158310845825)
        ·
          refine ⟨14711464618701868733134369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19615286158269158310845825 14711464618701868733134369)
          ·
            refine ⟨11033598464026401549850777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14711464618701868733134369 11033598464026401549850777)
            ·
              refine ⟨8275198848019801162388083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11033598464026401549850777 8275198848019801162388083)
              ·
                refine ⟨12412798272029701743582125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8275198848019801162388083 12412798272029701743582125)
                ·
                  refine ⟨4654799352011138153843297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12412798272029701743582125 4654799352011138153843297)
                  ·
                    refine ⟨3491099514008353615382473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654799352011138153843297 3491099514008353615382473)
                    ·
                      refine ⟨2618324635506265211536855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491099514008353615382473 2618324635506265211536855)
                      ·
                        rfl

theorem cell23_5099169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5099169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099169 prefixEnd_5099169 := by exact prefixLift 5099169
  have htrace : WordTrace (prefixWord ++ tailWord_5099169) baseStart_5099169 baseEnd_5099169 := by
    simpa [prefixWord, tailWord_5099169, baseEnd_5099169] using wordTrace_append hprefix tailTrace_5099169
  have hstable : (prefixWord ++ tailWord_5099169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099169).length < 2 ^ (prefixWord ++ tailWord_5099169).sum := by decide
  have hdescent : baseEnd_5099169 < baseStart_5099169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099182 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5099182 : Nat := 118140960795 + 5099182 * 2 ^ 59
def prefixEnd_5099182 : Nat := 4983230072969 + 3 ^ 40 * 5099182 * 2
def baseEnd_5099182 : Nat := 2618331310754773660674295

theorem tailTrace_5099182 : CollatzResearch.WordTrace tailWord_5099182 prefixEnd_5099182 2618331310754773660674295 := by
  unfold tailWord_5099182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247805826567744974641475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123988297741694639864754533 23247805826567744974641475)
  ·
    refine ⟨34871708739851617461962213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23247805826567744974641475 34871708739851617461962213)
    ·
      refine ⟨6538445388722178274117915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34871708739851617461962213 6538445388722178274117915)
      ·
        refine ⟨9807668083083267411176873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538445388722178274117915 9807668083083267411176873)
        ·
          refine ⟨7355751062312450558382655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9807668083083267411176873 7355751062312450558382655)
          ·
            refine ⟨11033626593468675837573983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355751062312450558382655 11033626593468675837573983)
            ·
              refine ⟨16550439890203013756360975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11033626593468675837573983 16550439890203013756360975)
              ·
                refine ⟨24825659835304520634541463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16550439890203013756360975 24825659835304520634541463)
                ·
                  refine ⟨37238489752956780951812195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24825659835304520634541463 37238489752956780951812195)
                  ·
                    refine ⟨55857734629435171427718293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37238489752956780951812195 55857734629435171427718293)
                    ·
                      refine ⟨2618331310754773660674295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55857734629435171427718293 2618331310754773660674295)
                      ·
                        rfl

theorem cell23_5099182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5099182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099182 prefixEnd_5099182 := by exact prefixLift 5099182
  have htrace : WordTrace (prefixWord ++ tailWord_5099182) baseStart_5099182 baseEnd_5099182 := by
    simpa [prefixWord, tailWord_5099182, baseEnd_5099182] using wordTrace_append hprefix tailTrace_5099182
  have hstable : (prefixWord ++ tailWord_5099182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099182).length < 2 ^ (prefixWord ++ tailWord_5099182).sum := by decide
  have hdescent : baseEnd_5099182 < baseStart_5099182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099189 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5099189 : Nat := 118140960795 + 5099189 * 2 ^ 59
def prefixEnd_5099189 : Nat := 4983230072969 + 3 ^ 40 * 5099189 * 2
def baseEnd_5099189 : Nat := 2618334905119355133286763

theorem tailTrace_5099189 : CollatzResearch.WordTrace tailWord_5099189 prefixEnd_5099189 2618334905119355133286763 := by
  unfold tailWord_5099189
  simp only [CollatzResearch.WordTrace]
  refine ⟨185982701923516599992636621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123988467949011066661757747 185982701923516599992636621)
  ·
    refine ⟨69743513221318724997238733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185982701923516599992636621 69743513221318724997238733)
    ·
      refine ⟨26153817457994521873964525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69743513221318724997238733 26153817457994521873964525)
      ·
        refine ⟨9807681546747945702736697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26153817457994521873964525 9807681546747945702736697)
        ·
          refine ⟨7355761160060959277052523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9807681546747945702736697 7355761160060959277052523)
          ·
            refine ⟨11033641740091438915578785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7355761160060959277052523 11033641740091438915578785)
            ·
              refine ⟨8275231305068579186684089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11033641740091438915578785 8275231305068579186684089)
              ·
                refine ⟨6206423478801434390013067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275231305068579186684089 6206423478801434390013067)
                ·
                  refine ⟨9309635218202151585019601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206423478801434390013067 9309635218202151585019601)
                  ·
                    refine ⟨6982226413651613688764701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9309635218202151585019601 6982226413651613688764701)
                    ·
                      refine ⟨2618334905119355133286763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6982226413651613688764701 2618334905119355133286763)
                      ·
                        rfl

theorem cell23_5099189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5099189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099189 prefixEnd_5099189 := by exact prefixLift 5099189
  have htrace : WordTrace (prefixWord ++ tailWord_5099189) baseStart_5099189 baseEnd_5099189 := by
    simpa [prefixWord, tailWord_5099189, baseEnd_5099189] using wordTrace_append hprefix tailTrace_5099189
  have hstable : (prefixWord ++ tailWord_5099189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099189).length < 2 ^ (prefixWord ++ tailWord_5099189).sum := by decide
  have hdescent : baseEnd_5099189 < baseStart_5099189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099195 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 3, 3, 2]
def baseStart_5099195 : Nat := 118140960795 + 5099195 * 2 ^ 59
def prefixEnd_5099195 : Nat := 4983230072969 + 3 ^ 40 * 5099195 * 2
def baseEnd_5099195 : Nat := 2618337986003282109811735

theorem tailTrace_5099195 : CollatzResearch.WordTrace tailWord_5099195 prefixEnd_5099195 2618337986003282109811735 := by
  unfold tailWord_5099195
  simp only [CollatzResearch.WordTrace]
  refine ⟨185982920761494863017355039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123988613840996575344903359 185982920761494863017355039)
  ·
    refine ⟨278974381142242294526032559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185982920761494863017355039 278974381142242294526032559)
    ·
      refine ⟨418461571713363441789048839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278974381142242294526032559 418461571713363441789048839)
      ·
        refine ⟨627692357570045162683573259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418461571713363441789048839 627692357570045162683573259)
        ·
          refine ⟨941538536355067744025359889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627692357570045162683573259 941538536355067744025359889)
          ·
            refine ⟨706153902266300808019019917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941538536355067744025359889 706153902266300808019019917)
            ·
              refine ⟨264807713349862803007132469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706153902266300808019019917 264807713349862803007132469)
              ·
                refine ⟨24825723126549637781918669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264807713349862803007132469 24825723126549637781918669)
                ·
                  refine ⟨9309646172456114168219501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24825723126549637781918669 9309646172456114168219501)
                  ·
                    refine ⟨3491117314671042813082313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9309646172456114168219501 3491117314671042813082313)
                    ·
                      refine ⟨2618337986003282109811735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491117314671042813082313 2618337986003282109811735)
                      ·
                        rfl

theorem cell23_5099195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 3, 2].length) (baseStart_5099195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099195 prefixEnd_5099195 := by exact prefixLift 5099195
  have htrace : WordTrace (prefixWord ++ tailWord_5099195) baseStart_5099195 baseEnd_5099195 := by
    simpa [prefixWord, tailWord_5099195, baseEnd_5099195] using wordTrace_append hprefix tailTrace_5099195
  have hstable : (prefixWord ++ tailWord_5099195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099195).length < 2 ^ (prefixWord ++ tailWord_5099195).sum := by decide
  have hdescent : baseEnd_5099195 < baseStart_5099195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099206 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5099206 : Nat := 118140960795 + 5099206 * 2 ^ 59
def prefixEnd_5099206 : Nat := 4983230072969 + 3 ^ 40 * 5099206 * 2
def baseEnd_5099206 : Nat := 2618343634290481566774185

theorem tailTrace_5099206 : CollatzResearch.WordTrace tailWord_5099206 prefixEnd_5099206 2618343634290481566774185 := by
  unfold tailWord_5099206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811978811389219121750171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 123988881309636674597336981 5811978811389219121750171)
  ·
    refine ⟨8717968217083828682625257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5811978811389219121750171 8717968217083828682625257)
    ·
      refine ⟨6538476162812871511968943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8717968217083828682625257 6538476162812871511968943)
      ·
        refine ⟨9807714244219307267953415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538476162812871511968943 9807714244219307267953415)
        ·
          refine ⟨14711571366328960901930123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9807714244219307267953415 14711571366328960901930123)
          ·
            refine ⟨22067357049493441352895185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14711571366328960901930123 22067357049493441352895185)
            ·
              refine ⟨16550517787120081014671389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22067357049493441352895185 16550517787120081014671389)
              ·
                refine ⟨6206444170170030380501771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16550517787120081014671389 6206444170170030380501771)
                ·
                  refine ⟨9309666255255045570752657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206444170170030380501771 9309666255255045570752657)
                  ·
                    refine ⟨6982249691441284178064493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9309666255255045570752657 6982249691441284178064493)
                    ·
                      refine ⟨2618343634290481566774185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6982249691441284178064493 2618343634290481566774185)
                      ·
                        rfl

theorem cell23_5099206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5099206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099206 prefixEnd_5099206 := by exact prefixLift 5099206
  have htrace : WordTrace (prefixWord ++ tailWord_5099206) baseStart_5099206 baseEnd_5099206 := by
    simpa [prefixWord, tailWord_5099206, baseEnd_5099206] using wordTrace_append hprefix tailTrace_5099206
  have hstable : (prefixWord ++ tailWord_5099206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099206).length < 2 ^ (prefixWord ++ tailWord_5099206).sum := by decide
  have hdescent : baseEnd_5099206 < baseStart_5099206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099245 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5099245 : Nat := 118140960795 + 5099245 * 2 ^ 59
def prefixEnd_5099245 : Nat := 4983230072969 + 3 ^ 40 * 5099245 * 2
def baseEnd_5099245 : Nat := 2618363660036006914186505

theorem tailTrace_5099245 : CollatzResearch.WordTrace tailWord_5099245 prefixEnd_5099245 2618363660036006914186505 := by
  unfold tailWord_5099245
  simp only [CollatzResearch.WordTrace]
  refine ⟨185984744411313721556675189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123989829607542481037783459 185984744411313721556675189)
  ·
    refine ⟨17436069788560661395938299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 185984744411313721556675189 17436069788560661395938299)
    ·
      refine ⟨26154104682840992093907449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17436069788560661395938299 26154104682840992093907449)
      ·
        refine ⟨19615578512130744070430587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26154104682840992093907449 19615578512130744070430587)
        ·
          refine ⟨29423367768196116105645881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19615578512130744070430587 29423367768196116105645881)
          ·
            refine ⟨22067525826147087079234411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29423367768196116105645881 22067525826147087079234411)
            ·
              refine ⟨33101288739220630618851617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22067525826147087079234411 33101288739220630618851617)
              ·
                refine ⟨24825966554415472964138713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33101288739220630618851617 24825966554415472964138713)
                ·
                  refine ⟨18619474915811604723104035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24825966554415472964138713 18619474915811604723104035)
                  ·
                    refine ⟨27929212373717407084656053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18619474915811604723104035 27929212373717407084656053)
                    ·
                      refine ⟨2618363660036006914186505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27929212373717407084656053 2618363660036006914186505)
                      ·
                        rfl

theorem cell23_5099245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5099245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099245 prefixEnd_5099245 := by exact prefixLift 5099245
  have htrace : WordTrace (prefixWord ++ tailWord_5099245) baseStart_5099245 baseEnd_5099245 := by
    simpa [prefixWord, tailWord_5099245, baseEnd_5099245] using wordTrace_append hprefix tailTrace_5099245
  have hstable : (prefixWord ++ tailWord_5099245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099245).length < 2 ^ (prefixWord ++ tailWord_5099245).sum := by decide
  have hdescent : baseEnd_5099245 < baseStart_5099245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099365 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_5099365 : Nat := 118140960795 + 5099365 * 2 ^ 59
def prefixEnd_5099365 : Nat := 4983230072969 + 3 ^ 40 * 5099365 * 2
def baseEnd_5099365 : Nat := 2618425277714546444685953

theorem tailTrace_5099365 : CollatzResearch.WordTrace tailWord_5099365 prefixEnd_5099365 2618425277714546444685953 := by
  unfold tailWord_5099365
  simp only [CollatzResearch.WordTrace]
  refine ⟨185989121170878982051043549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123992747447252654700695699 185989121170878982051043549)
  ·
    refine ⟨69745920439079618269141331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185989121170878982051043549 69745920439079618269141331)
    ·
      refine ⟨104618880658619427403711997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69745920439079618269141331 104618880658619427403711997)
      ·
        refine ⟨39232080246982285276391999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104618880658619427403711997 39232080246982285276391999)
        ·
          refine ⟨58848120370473427914587999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39232080246982285276391999 58848120370473427914587999)
          ·
            refine ⟨88272180555710141871881999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58848120370473427914587999 88272180555710141871881999)
            ·
              refine ⟨132408270833565212807822999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88272180555710141871881999 132408270833565212807822999)
              ·
                refine ⟨198612406250347819211734499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132408270833565212807822999 198612406250347819211734499)
                ·
                  refine ⟨297918609375521728817601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198612406250347819211734499 297918609375521728817601749)
                  ·
                    refine ⟨6982467407238790519162541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 297918609375521728817601749 6982467407238790519162541)
                    ·
                      refine ⟨2618425277714546444685953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6982467407238790519162541 2618425277714546444685953)
                      ·
                        rfl

theorem cell23_5099365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_5099365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099365 prefixEnd_5099365 := by exact prefixLift 5099365
  have htrace : WordTrace (prefixWord ++ tailWord_5099365) baseStart_5099365 baseEnd_5099365 := by
    simpa [prefixWord, tailWord_5099365, baseEnd_5099365] using wordTrace_append hprefix tailTrace_5099365
  have hstable : (prefixWord ++ tailWord_5099365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099365).length < 2 ^ (prefixWord ++ tailWord_5099365).sum := by decide
  have hdescent : baseEnd_5099365 < baseStart_5099365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099393 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 3, 4]
def baseStart_5099393 : Nat := 118140960795 + 5099393 * 2 ^ 59
def prefixEnd_5099393 : Nat := 4983230072969 + 3 ^ 40 * 5099393 * 2
def baseEnd_5099393 : Nat := 872813218390957445045275

theorem tailTrace_5099393 : CollatzResearch.WordTrace tailWord_5099393 prefixEnd_5099393 872813218390957445045275 := by
  unfold tailWord_5099393
  simp only [CollatzResearch.WordTrace]
  refine ⟨185990142414777542833062833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123993428276518361888708555 185990142414777542833062833)
  ·
    refine ⟨139492606811083157124797125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185990142414777542833062833 139492606811083157124797125)
    ·
      refine ⟨26154863777078091960899461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139492606811083157124797125 26154863777078091960899461)
      ·
        refine ⟨4904036958202142242668649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26154863777078091960899461 4904036958202142242668649)
        ·
          refine ⟨3678027718651606682001487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904036958202142242668649 3678027718651606682001487)
          ·
            refine ⟨5517041577977410023002231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678027718651606682001487 5517041577977410023002231)
            ·
              refine ⟨8275562366966115034503347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517041577977410023002231 8275562366966115034503347)
              ·
                refine ⟨12413343550449172551755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8275562366966115034503347 12413343550449172551755021)
                ·
                  refine ⟨4655003831418439706908133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12413343550449172551755021 4655003831418439706908133)
                  ·
                    refine ⟨872813218390957445045275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655003831418439706908133 872813218390957445045275)
                    ·
                      rfl

theorem cell23_5099393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_5099393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099393 prefixEnd_5099393 := by exact prefixLift 5099393
  have htrace : WordTrace (prefixWord ++ tailWord_5099393) baseStart_5099393 baseEnd_5099393 := by
    simpa [prefixWord, tailWord_5099393, baseEnd_5099393] using wordTrace_append hprefix tailTrace_5099393
  have hstable : (prefixWord ++ tailWord_5099393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099393).length < 2 ^ (prefixWord ++ tailWord_5099393).sum := by decide
  have hdescent : baseEnd_5099393 < baseStart_5099393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099439 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 1, 1, 4]
def baseStart_5099439 : Nat := 118140960795 + 5099439 * 2 ^ 59
def prefixEnd_5099439 : Nat := 4983230072969 + 3 ^ 40 * 5099439 * 2
def baseEnd_5099439 : Nat := 2618463275282979155160613

theorem tailTrace_5099439 : CollatzResearch.WordTrace tailWord_5099439 prefixEnd_5099439 2618463275282979155160613 := by
  unfold tailWord_5099439
  simp only [CollatzResearch.WordTrace]
  refine ⟨185991820172610892689237371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123994546781740595126158247 185991820172610892689237371)
  ·
    refine ⟨278987730258916339033856057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185991820172610892689237371 278987730258916339033856057)
    ·
      refine ⟨209240797694187254275392043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278987730258916339033856057 209240797694187254275392043)
      ·
        refine ⟨313861196541280881413088065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209240797694187254275392043 313861196541280881413088065)
        ·
          refine ⟨235395897405960661059816049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313861196541280881413088065 235395897405960661059816049)
          ·
            refine ⟨176546923054470495794862037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235395897405960661059816049 176546923054470495794862037)
            ·
              refine ⟨4137818509089152245192079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 176546923054470495794862037 4137818509089152245192079)
              ·
                refine ⟨6206727763633728367788119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137818509089152245192079 6206727763633728367788119)
                ·
                  refine ⟨9310091645450592551682179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206727763633728367788119 9310091645450592551682179)
                  ·
                    refine ⟨13965137468175888827523269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9310091645450592551682179 13965137468175888827523269)
                    ·
                      refine ⟨2618463275282979155160613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13965137468175888827523269 2618463275282979155160613)
                      ·
                        rfl

theorem cell23_5099439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 1, 4].length) (baseStart_5099439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099439 prefixEnd_5099439 := by exact prefixLift 5099439
  have htrace : WordTrace (prefixWord ++ tailWord_5099439) baseStart_5099439 baseEnd_5099439 := by
    simpa [prefixWord, tailWord_5099439, baseEnd_5099439] using wordTrace_append hprefix tailTrace_5099439
  have hstable : (prefixWord ++ tailWord_5099439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099439).length < 2 ^ (prefixWord ++ tailWord_5099439).sum := by decide
  have hdescent : baseEnd_5099439 < baseStart_5099439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099445 : List Nat := [1, 3, 3, 2, 1, 13]
def baseStart_5099445 : Nat := 118140960795 + 5099445 * 2 ^ 59
def prefixEnd_5099445 : Nat := 4983230072969 + 3 ^ 40 * 5099445 * 2
def baseEnd_5099445 : Nat := 10775581712621012887595

theorem tailTrace_5099445 : CollatzResearch.WordTrace tailWord_5099445 prefixEnd_5099445 10775581712621012887595 := by
  unfold tailWord_5099445
  simp only [CollatzResearch.WordTrace]
  refine ⟨185992039010589155713955789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123994692673726103809303859 185992039010589155713955789)
  ·
    refine ⟨69747014628970933392733421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185992039010589155713955789 69747014628970933392733421)
    ·
      refine ⟨26155130485864100022275033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69747014628970933392733421 26155130485864100022275033)
      ·
        refine ⟨19616347864398075016706275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26155130485864100022275033 19616347864398075016706275)
        ·
          refine ⟨29424521796597112525059413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19616347864398075016706275 29424521796597112525059413)
          ·
            refine ⟨10775581712621012887595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29424521796597112525059413 10775581712621012887595)
            ·
              rfl

theorem cell23_5099445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 13].length) (baseStart_5099445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099445 prefixEnd_5099445 := by exact prefixLift 5099445
  have htrace : WordTrace (prefixWord ++ tailWord_5099445) baseStart_5099445 baseEnd_5099445 := by
    simpa [prefixWord, tailWord_5099445, baseEnd_5099445] using wordTrace_append hprefix tailTrace_5099445
  have hstable : (prefixWord ++ tailWord_5099445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099445).length < 2 ^ (prefixWord ++ tailWord_5099445).sum := by decide
  have hdescent : baseEnd_5099445 < baseStart_5099445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099449 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 2, 4]
def baseStart_5099449 : Nat := 118140960795 + 5099449 * 2 ^ 59
def prefixEnd_5099449 : Nat := 4983230072969 + 3 ^ 40 * 5099449 * 2
def baseEnd_5099449 : Nat := 872822803363174705345189

theorem tailTrace_5099449 : CollatzResearch.WordTrace tailWord_5099449 prefixEnd_5099449 872822803363174705345189 := by
  unfold tailWord_5099449
  simp only [CollatzResearch.WordTrace]
  refine ⟨185992184902574664397101401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123994789935049776264734267 185992184902574664397101401)
  ·
    refine ⟨139494138676930998297826051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185992184902574664397101401 139494138676930998297826051)
    ·
      refine ⟨209241208015396497446739077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139494138676930998297826051 209241208015396497446739077)
      ·
        refine ⟨39232726502886843271263577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209241208015396497446739077 39232726502886843271263577)
        ·
          refine ⟨29424544877165132453447683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39232726502886843271263577 29424544877165132453447683)
          ·
            refine ⟨44136817315747698680171525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29424544877165132453447683 44136817315747698680171525)
            ·
              refine ⟨8275653246702693502532161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44136817315747698680171525 8275653246702693502532161)
              ·
                refine ⟨6206739935027020126899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275653246702693502532161 6206739935027020126899121)
                ·
                  refine ⟨4655054951270265095174341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206739935027020126899121 4655054951270265095174341)
                  ·
                    refine ⟨872822803363174705345189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655054951270265095174341 872822803363174705345189)
                    ·
                      rfl

theorem cell23_5099449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 4].length) (baseStart_5099449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099449 prefixEnd_5099449 := by exact prefixLift 5099449
  have htrace : WordTrace (prefixWord ++ tailWord_5099449) baseStart_5099449 baseEnd_5099449 := by
    simpa [prefixWord, tailWord_5099449, baseEnd_5099449] using wordTrace_append hprefix tailTrace_5099449
  have hstable : (prefixWord ++ tailWord_5099449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099449).length < 2 ^ (prefixWord ++ tailWord_5099449).sum := by decide
  have hdescent : baseEnd_5099449 < baseStart_5099449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099472 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_5099472 : Nat := 118140960795 + 5099472 * 2 ^ 59
def prefixEnd_5099472 : Nat := 4983230072969 + 3 ^ 40 * 5099472 * 2
def baseEnd_5099472 : Nat := 2618480220144577526047961

theorem tailTrace_5099472 : CollatzResearch.WordTrace tailWord_5099472 prefixEnd_5099472 2618480220144577526047961 := by
  unfold tailWord_5099472
  simp only [CollatzResearch.WordTrace]
  refine ⟨92996511890745669662594335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123995349187660892883459113 92996511890745669662594335)
  ·
    refine ⟨139494767836118504493891503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92996511890745669662594335 139494767836118504493891503)
    ·
      refine ⟨209242151754177756740837255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139494767836118504493891503 209242151754177756740837255)
      ·
        refine ⟨313863227631266635111255883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209242151754177756740837255 313863227631266635111255883)
        ·
          refine ⟨470794841446899952666883825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313863227631266635111255883 470794841446899952666883825)
          ·
            refine ⟨353096131085174964500162869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470794841446899952666883825 353096131085174964500162869)
            ·
              refine ⟨33102762289235152921890269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 353096131085174964500162869 33102762289235152921890269)
              ·
                refine ⟨12413535858463182345708851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33102762289235152921890269 12413535858463182345708851)
                ·
                  refine ⟨18620303787694773518563277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12413535858463182345708851 18620303787694773518563277)
                  ·
                    refine ⟨6982613920385540069461229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18620303787694773518563277 6982613920385540069461229)
                    ·
                      refine ⟨2618480220144577526047961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6982613920385540069461229 2618480220144577526047961)
                      ·
                        rfl

theorem cell23_5099472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_5099472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099472 prefixEnd_5099472 := by exact prefixLift 5099472
  have htrace : WordTrace (prefixWord ++ tailWord_5099472) baseStart_5099472 baseEnd_5099472 := by
    simpa [prefixWord, tailWord_5099472, baseEnd_5099472] using wordTrace_append hprefix tailTrace_5099472
  have hstable : (prefixWord ++ tailWord_5099472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099472).length < 2 ^ (prefixWord ++ tailWord_5099472).sum := by decide
  have hdescent : baseEnd_5099472 < baseStart_5099472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099490 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5099490 : Nat := 118140960795 + 5099490 * 2 ^ 59
def prefixEnd_5099490 : Nat := 4983230072969 + 3 ^ 40 * 5099490 * 2
def baseEnd_5099490 : Nat := 2618489462796358455622879

theorem tailTrace_5099490 : CollatzResearch.WordTrace tailWord_5099490 prefixEnd_5099490 2618489462796358455622879 := by
  unfold tailWord_5099490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498420073856532099835981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123995786863617418932895949 46498420073856532099835981)
  ·
    refine ⟨17436907527696199537438493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46498420073856532099835981 17436907527696199537438493)
    ·
      refine ⟨6538840322886074826539435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17436907527696199537438493 6538840322886074826539435)
      ·
        refine ⟨9808260484329112239809153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538840322886074826539435 9808260484329112239809153)
        ·
          refine ⟨7356195363246834179856865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9808260484329112239809153 7356195363246834179856865)
          ·
            refine ⟨5517146522435125634892649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7356195363246834179856865 5517146522435125634892649)
            ·
              refine ⟨4137859891826344226169487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5517146522435125634892649 4137859891826344226169487)
              ·
                refine ⟨6206789837739516339254231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137859891826344226169487 6206789837739516339254231)
                ·
                  refine ⟨9310184756609274508881347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206789837739516339254231 9310184756609274508881347)
                  ·
                    refine ⟨13965277134913911763322021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9310184756609274508881347 13965277134913911763322021)
                    ·
                      refine ⟨2618489462796358455622879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13965277134913911763322021 2618489462796358455622879)
                      ·
                        rfl

theorem cell23_5099490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5099490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099490 prefixEnd_5099490 := by exact prefixLift 5099490
  have htrace : WordTrace (prefixWord ++ tailWord_5099490) baseStart_5099490 baseEnd_5099490 := by
    simpa [prefixWord, tailWord_5099490, baseEnd_5099490] using wordTrace_append hprefix tailTrace_5099490
  have hstable : (prefixWord ++ tailWord_5099490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099490).length < 2 ^ (prefixWord ++ tailWord_5099490).sum := by decide
  have hdescent : baseEnd_5099490 < baseStart_5099490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099532 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5099532 : Nat := 118140960795 + 5099532 * 2 ^ 59
def prefixEnd_5099532 : Nat := 4983230072969 + 3 ^ 40 * 5099532 * 2
def baseEnd_5099532 : Nat := 2618511028983847291297685

theorem tailTrace_5099532 : CollatzResearch.WordTrace tailWord_5099532 prefixEnd_5099532 2618511028983847291297685 := by
  unfold tailWord_5099532
  simp only [CollatzResearch.WordTrace]
  refine ⟨92997606080636984786186425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123996808107515979714915233 92997606080636984786186425)
  ·
    refine ⟨69748204560477738589639819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92997606080636984786186425 69748204560477738589639819)
    ·
      refine ⟨104622306840716607884459729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69748204560477738589639819 104622306840716607884459729)
      ·
        refine ⟨78466730130537455913344797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104622306840716607884459729 78466730130537455913344797)
        ·
          refine ⟨29425023798951545967504299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78466730130537455913344797 29425023798951545967504299)
          ·
            refine ⟨44137535698427318951256449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29425023798951545967504299 44137535698427318951256449)
            ·
              refine ⟨33103151773820489213442337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44137535698427318951256449 33103151773820489213442337)
              ·
                refine ⟨24827363830365366910081753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33103151773820489213442337 24827363830365366910081753)
                ·
                  refine ⟨18620522872774025182561315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24827363830365366910081753 18620522872774025182561315)
                  ·
                    refine ⟨27930784309161037773841973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18620522872774025182561315 27930784309161037773841973)
                    ·
                      refine ⟨2618511028983847291297685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27930784309161037773841973 2618511028983847291297685)
                      ·
                        rfl

theorem cell23_5099532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5099532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099532 prefixEnd_5099532 := by exact prefixLift 5099532
  have htrace : WordTrace (prefixWord ++ tailWord_5099532) baseStart_5099532 baseEnd_5099532 := by
    simpa [prefixWord, tailWord_5099532, baseEnd_5099532] using wordTrace_append hprefix tailTrace_5099532
  have hstable : (prefixWord ++ tailWord_5099532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099532).length < 2 ^ (prefixWord ++ tailWord_5099532).sum := by decide
  have hdescent : baseEnd_5099532 < baseStart_5099532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099546 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_5099546 : Nat := 118140960795 + 5099546 * 2 ^ 59
def prefixEnd_5099546 : Nat := 4983230072969 + 3 ^ 40 * 5099546 * 2
def baseEnd_5099546 : Nat := 2618518217713010236522621

theorem tailTrace_5099546 : CollatzResearch.WordTrace tailWord_5099546 prefixEnd_5099546 2618518217713010236522621 := by
  unfold tailWord_5099546
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498930695805812490845623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 123997148522148833308921661 46498930695805812490845623)
  ·
    refine ⟨69748396043708718736268435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46498930695805812490845623 69748396043708718736268435)
    ·
      refine ⟨104622594065563078104402653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69748396043708718736268435 104622594065563078104402653)
      ·
        refine ⟨39233472774586154289150995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104622594065563078104402653 39233472774586154289150995)
        ·
          refine ⟨58850209161879231433726493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39233472774586154289150995 58850209161879231433726493)
          ·
            refine ⟨22068828435704711787647435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58850209161879231433726493 22068828435704711787647435)
            ·
              refine ⟨33103242653557067681471153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22068828435704711787647435 33103242653557067681471153)
              ·
                refine ⟨24827431990167800761103365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33103242653557067681471153 24827431990167800761103365)
                ·
                  refine ⟨4655143498156462642706881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24827431990167800761103365 4655143498156462642706881)
                  ·
                    refine ⟨3491357623617346982030161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4655143498156462642706881 3491357623617346982030161)
                    ·
                      refine ⟨2618518217713010236522621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491357623617346982030161 2618518217713010236522621)
                      ·
                        rfl

theorem cell23_5099546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_5099546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099546 prefixEnd_5099546 := by exact prefixLift 5099546
  have htrace : WordTrace (prefixWord ++ tailWord_5099546) baseStart_5099546 baseEnd_5099546 := by
    simpa [prefixWord, tailWord_5099546, baseEnd_5099546] using wordTrace_append hprefix tailTrace_5099546
  have hstable : (prefixWord ++ tailWord_5099546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099546).length < 2 ^ (prefixWord ++ tailWord_5099546).sum := by decide
  have hdescent : baseEnd_5099546 < baseStart_5099546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099549 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5099549 : Nat := 118140960795 + 5099549 * 2 ^ 59
def prefixEnd_5099549 : Nat := 4983230072969 + 3 ^ 40 * 5099549 * 2
def baseEnd_5099549 : Nat := 2618519758154973724785107

theorem tailTrace_5099549 : CollatzResearch.WordTrace tailWord_5099549 prefixEnd_5099549 2618519758154973724785107 := by
  unfold tailWord_5099549
  simp only [CollatzResearch.WordTrace]
  refine ⟨185995832202212381475741701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123997221468141587650494467 185995832202212381475741701)
  ·
    refine ⟨34874218537914821526701569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 185995832202212381475741701 34874218537914821526701569)
    ·
      refine ⟨26155663903436116145026177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34874218537914821526701569 26155663903436116145026177)
      ·
        refine ⟨19616747927577087108769633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26155663903436116145026177 19616747927577087108769633)
        ·
          refine ⟨14712560945682815331577225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19616747927577087108769633 14712560945682815331577225)
          ·
            refine ⟨11034420709262111498682919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14712560945682815331577225 11034420709262111498682919)
            ·
              refine ⟨16551631063893167248024379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11034420709262111498682919 16551631063893167248024379)
              ·
                refine ⟨24827446595839750872036569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16551631063893167248024379 24827446595839750872036569)
                ·
                  refine ⟨18620584946879813154027427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24827446595839750872036569 18620584946879813154027427)
                  ·
                    refine ⟨27930877420319719731041141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18620584946879813154027427 27930877420319719731041141)
                    ·
                      refine ⟨2618519758154973724785107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27930877420319719731041141 2618519758154973724785107)
                      ·
                        rfl

theorem cell23_5099549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5099549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099549 prefixEnd_5099549 := by exact prefixLift 5099549
  have htrace : WordTrace (prefixWord ++ tailWord_5099549) baseStart_5099549 baseEnd_5099549 := by
    simpa [prefixWord, tailWord_5099549, baseEnd_5099549] using wordTrace_append hprefix tailTrace_5099549
  have hstable : (prefixWord ++ tailWord_5099549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099549).length < 2 ^ (prefixWord ++ tailWord_5099549).sum := by decide
  have hdescent : baseEnd_5099549 < baseStart_5099549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099569 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 7]
def baseStart_5099569 : Nat := 118140960795 + 5099569 * 2 ^ 59
def prefixEnd_5099569 : Nat := 4983230072969 + 3 ^ 40 * 5099569 * 2
def baseEnd_5099569 : Nat := 290947780863118182948335

theorem tailTrace_5099569 : CollatzResearch.WordTrace tailWord_5099569 prefixEnd_5099569 290947780863118182948335 := by
  unfold tailWord_5099569
  simp only [CollatzResearch.WordTrace]
  refine ⟨185996561662139924891469761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123997707774759949927646507 185996561662139924891469761)
  ·
    refine ⟨139497421246604943668602321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185996561662139924891469761 139497421246604943668602321)
    ·
      refine ⟨104623065934953707751451741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139497421246604943668602321 104623065934953707751451741)
      ·
        refine ⟨39233649725607640406794403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104623065934953707751451741 39233649725607640406794403)
        ·
          refine ⟨58850474588411460610191605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39233649725607640406794403 58850474588411460610191605)
          ·
            refine ⟨5517231992663574432205463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58850474588411460610191605 5517231992663574432205463)
            ·
              refine ⟨8275847988995361648308195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517231992663574432205463 8275847988995361648308195)
              ·
                refine ⟨12413771983493042472462293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8275847988995361648308195 12413771983493042472462293)
                ·
                  refine ⟨290947780863118182948335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12413771983493042472462293 290947780863118182948335)
                  ·
                    rfl

theorem cell23_5099569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 7].length) (baseStart_5099569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099569 prefixEnd_5099569 := by exact prefixLift 5099569
  have htrace : WordTrace (prefixWord ++ tailWord_5099569) baseStart_5099569 baseEnd_5099569 := by
    simpa [prefixWord, tailWord_5099569, baseEnd_5099569] using wordTrace_append hprefix tailTrace_5099569
  have hstable : (prefixWord ++ tailWord_5099569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099569).length < 2 ^ (prefixWord ++ tailWord_5099569).sum := by decide
  have hdescent : baseEnd_5099569 < baseStart_5099569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099614 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5099614 : Nat := 118140960795 + 5099614 * 2 ^ 59
def prefixEnd_5099614 : Nat := 4983230072969 + 3 ^ 40 * 5099614 * 2
def baseEnd_5099614 : Nat := 2618553134397515970472309

theorem tailTrace_5099614 : CollatzResearch.WordTrace tailWord_5099614 prefixEnd_5099614 2618553134397515970472309 := by
  unfold tailWord_5099614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23249775368372112197107237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 123998801964651265051238597 23249775368372112197107237)
  ·
    refine ⟨4359332881569771036957607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23249775368372112197107237 4359332881569771036957607)
    ·
      refine ⟨6538999322354656555436411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359332881569771036957607 6538999322354656555436411)
      ·
        refine ⟨9808498983531984833154617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6538999322354656555436411 9808498983531984833154617)
        ·
          refine ⟨7356374237648988624865963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9808498983531984833154617 7356374237648988624865963)
          ·
            refine ⟨11034561356473482937298945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7356374237648988624865963 11034561356473482937298945)
            ·
              refine ⟨8275921017355112202974209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11034561356473482937298945 8275921017355112202974209)
              ·
                refine ⟨6206940763016334152230657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275921017355112202974209 6206940763016334152230657)
                ·
                  refine ⟨4655205572262250614172993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206940763016334152230657 4655205572262250614172993)
                  ·
                    refine ⟨3491404179196687960629745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4655205572262250614172993 3491404179196687960629745)
                    ·
                      refine ⟨2618553134397515970472309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491404179196687960629745 2618553134397515970472309)
                      ·
                        rfl

theorem cell23_5099614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5099614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099614 prefixEnd_5099614 := by exact prefixLift 5099614
  have htrace : WordTrace (prefixWord ++ tailWord_5099614) baseStart_5099614 baseEnd_5099614 := by
    simpa [prefixWord, tailWord_5099614, baseEnd_5099614] using wordTrace_append hprefix tailTrace_5099614
  have hstable : (prefixWord ++ tailWord_5099614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099614).length < 2 ^ (prefixWord ++ tailWord_5099614).sum := by decide
  have hdescent : baseEnd_5099614 < baseStart_5099614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099619 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4]
def baseStart_5099619 : Nat := 118140960795 + 5099619 * 2 ^ 59
def prefixEnd_5099619 : Nat := 4983230072969 + 3 ^ 40 * 5099619 * 2
def baseEnd_5099619 : Nat := 2618555701800788450909785

theorem tailTrace_5099619 : CollatzResearch.WordTrace tailWord_5099619 prefixEnd_5099619 2618555701800788450909785 := by
  unfold tailWord_5099619
  simp only [CollatzResearch.WordTrace]
  refine ⟨185998385311958783430789911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 123998923541305855620526607 185998385311958783430789911)
  ·
    refine ⟨278997577967938175146184867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185998385311958783430789911 278997577967938175146184867)
    ·
      refine ⟨418496366951907262719277301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278997577967938175146184867 418496366951907262719277301)
      ·
        refine ⟨39234034401741305879932247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 418496366951907262719277301 39234034401741305879932247)
        ·
          refine ⟨58851051602611958819898371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39234034401741305879932247 58851051602611958819898371)
          ·
            refine ⟨88276577403917938229847557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58851051602611958819898371 88276577403917938229847557)
            ·
              refine ⟨16551858263234613418096417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88276577403917938229847557 16551858263234613418096417)
              ·
                refine ⟨12413893697425960063572313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16551858263234613418096417 12413893697425960063572313)
                ·
                  refine ⟨9310420273069470047679235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12413893697425960063572313 9310420273069470047679235)
                  ·
                    refine ⟨13965630409604205071518853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9310420273069470047679235 13965630409604205071518853)
                    ·
                      refine ⟨2618555701800788450909785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13965630409604205071518853 2618555701800788450909785)
                      ·
                        rfl

theorem cell23_5099619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_5099619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099619 prefixEnd_5099619 := by exact prefixLift 5099619
  have htrace : WordTrace (prefixWord ++ tailWord_5099619) baseStart_5099619 baseEnd_5099619 := by
    simpa [prefixWord, tailWord_5099619, baseEnd_5099619] using wordTrace_append hprefix tailTrace_5099619
  have hstable : (prefixWord ++ tailWord_5099619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099619).length < 2 ^ (prefixWord ++ tailWord_5099619).sum := by decide
  have hdescent : baseEnd_5099619 < baseStart_5099619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099656 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5099656 : Nat := 118140960795 + 5099656 * 2 ^ 59
def prefixEnd_5099656 : Nat := 4983230072969 + 3 ^ 40 * 5099656 * 2
def baseEnd_5099656 : Nat := 2618574700585004806147115

theorem tailTrace_5099656 : CollatzResearch.WordTrace tailWord_5099656 prefixEnd_5099656 2618574700585004806147115 := by
  unfold tailWord_5099656
  simp only [CollatzResearch.WordTrace]
  refine ⟨92999867406412369374943411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 123999823208549825833257881 92999867406412369374943411)
  ·
    refine ⟨139499801109618554062415117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92999867406412369374943411 139499801109618554062415117)
    ·
      refine ⟨52312425416106957773405669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139499801109618554062415117 52312425416106957773405669)
      ·
        refine ⟨9808579765520054582513563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52312425416106957773405669 9808579765520054582513563)
        ·
          refine ⟨14712869648280081873770345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808579765520054582513563 14712869648280081873770345)
          ·
            refine ⟨11034652236210061405327759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14712869648280081873770345 11034652236210061405327759)
            ·
              refine ⟨16551978354315092107991639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11034652236210061405327759 16551978354315092107991639)
              ·
                refine ⟨24827967531472638161987459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16551978354315092107991639 24827967531472638161987459)
                ·
                  refine ⟨37241951297208957242981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24827967531472638161987459 37241951297208957242981189)
                  ·
                    refine ⟨6982865868226679483058973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37241951297208957242981189 6982865868226679483058973)
                    ·
                      refine ⟨2618574700585004806147115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6982865868226679483058973 2618574700585004806147115)
                      ·
                        rfl

theorem cell23_5099656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5099656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099656 prefixEnd_5099656 := by exact prefixLift 5099656
  have htrace : WordTrace (prefixWord ++ tailWord_5099656) baseStart_5099656 baseEnd_5099656 := by
    simpa [prefixWord, tailWord_5099656, baseEnd_5099656] using wordTrace_append hprefix tailTrace_5099656
  have hstable : (prefixWord ++ tailWord_5099656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099656).length < 2 ^ (prefixWord ++ tailWord_5099656).sum := by decide
  have hdescent : baseEnd_5099656 < baseStart_5099656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099679 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5099679 : Nat := 118140960795 + 5099679 * 2 ^ 59
def prefixEnd_5099679 : Nat := 4983230072969 + 3 ^ 40 * 5099679 * 2
def baseEnd_5099679 : Nat := 2618586510640058216159509

theorem tailTrace_5099679 : CollatzResearch.WordTrace tailWord_5099679 prefixEnd_5099679 2618586510640058216159509 := by
  unfold tailWord_5099679
  simp only [CollatzResearch.WordTrace]
  refine ⟨186000573691741413677974091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124000382461160942451982727 186000573691741413677974091)
  ·
    refine ⟨279000860537612120516961137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186000573691741413677974091 279000860537612120516961137)
    ·
      refine ⟨209250645403209090387720853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279000860537612120516961137 209250645403209090387720853)
      ·
        refine ⟨9808624003275426111924415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 209250645403209090387720853 9808624003275426111924415)
        ·
          refine ⟨14712936004913139167886623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808624003275426111924415 14712936004913139167886623)
          ·
            refine ⟨22069404007369708751829935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14712936004913139167886623 22069404007369708751829935)
            ·
              refine ⟨33104106011054563127744903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22069404007369708751829935 33104106011054563127744903)
              ·
                refine ⟨49656159016581844691617355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33104106011054563127744903 49656159016581844691617355)
                ·
                  refine ⟨74484238524872767037426033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49656159016581844691617355 74484238524872767037426033)
                  ·
                    refine ⟨55863178893654575278069525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74484238524872767037426033 55863178893654575278069525)
                    ·
                      refine ⟨2618586510640058216159509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55863178893654575278069525 2618586510640058216159509)
                      ·
                        rfl

theorem cell23_5099679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5099679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099679 prefixEnd_5099679 := by exact prefixLift 5099679
  have htrace : WordTrace (prefixWord ++ tailWord_5099679) baseStart_5099679 baseEnd_5099679 := by
    simpa [prefixWord, tailWord_5099679, baseEnd_5099679] using wordTrace_append hprefix tailTrace_5099679
  have hstable : (prefixWord ++ tailWord_5099679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099679).length < 2 ^ (prefixWord ++ tailWord_5099679).sum := by decide
  have hdescent : baseEnd_5099679 < baseStart_5099679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099693 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 6]
def baseStart_5099693 : Nat := 118140960795 + 5099693 * 2 ^ 59
def prefixEnd_5099693 : Nat := 4983230072969 + 3 ^ 40 * 5099693 * 2
def baseEnd_5099693 : Nat := 290954855485469017931605

theorem tailTrace_5099693 : CollatzResearch.WordTrace tailWord_5099693 prefixEnd_5099693 290954855485469017931605 := by
  unfold tailWord_5099693
  simp only [CollatzResearch.WordTrace]
  refine ⟨186001084313690694068983733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124000722875793796045989155 186001084313690694068983733)
  ·
    refine ⟨17437601654408502568967225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186001084313690694068983733 17437601654408502568967225)
    ·
      refine ⟨13078201240806376926725419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17437601654408502568967225 13078201240806376926725419)
      ·
        refine ⟨19617301861209565390088129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13078201240806376926725419 19617301861209565390088129)
        ·
          refine ⟨14712976395907174042566097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19617301861209565390088129 14712976395907174042566097)
          ·
            refine ⟨11034732296930380531924573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14712976395907174042566097 11034732296930380531924573)
            ·
              refine ⟨4138024611348892699471715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11034732296930380531924573 4138024611348892699471715)
              ·
                refine ⟨6207036917023339049207573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138024611348892699471715 6207036917023339049207573)
                ·
                  refine ⟨290954855485469017931605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6207036917023339049207573 290954855485469017931605)
                  ·
                    rfl

theorem cell23_5099693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_5099693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099693 prefixEnd_5099693 := by exact prefixLift 5099693
  have htrace : WordTrace (prefixWord ++ tailWord_5099693) baseStart_5099693 baseEnd_5099693 := by
    simpa [prefixWord, tailWord_5099693, baseEnd_5099693] using wordTrace_append hprefix tailTrace_5099693
  have hstable : (prefixWord ++ tailWord_5099693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099693).length < 2 ^ (prefixWord ++ tailWord_5099693).sum := by decide
  have hdescent : baseEnd_5099693 < baseStart_5099693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099714 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5099714 : Nat := 118140960795 + 5099714 * 2 ^ 59
def prefixEnd_5099714 : Nat := 4983230072969 + 3 ^ 40 * 5099714 * 2
def baseEnd_5099714 : Nat := 872868160820988526407283

theorem tailTrace_5099714 : CollatzResearch.WordTrace tailWord_5099714 prefixEnd_5099714 872868160820988526407283 := by
  unfold tailWord_5099714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46500462561653653663874549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124001233497743076436998797 46500462561653653663874549)
  ·
    refine ⟨4359418365155030030988239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46500462561653653663874549 4359418365155030030988239)
    ·
      refine ⟨6539127547732545046482359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359418365155030030988239 6539127547732545046482359)
      ·
        refine ⟨9808691321598817569723539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539127547732545046482359 9808691321598817569723539)
        ·
          refine ⟨14713036982398226354585309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9808691321598817569723539 14713036982398226354585309)
          ·
            refine ⟨5517388868399334882969491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14713036982398226354585309 5517388868399334882969491)
            ·
              refine ⟨8276083302599002324454237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517388868399334882969491 8276083302599002324454237)
              ·
                refine ⟨3103531238474625871670339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8276083302599002324454237 3103531238474625871670339)
                ·
                  refine ⟨4655296857711938807505509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103531238474625871670339 4655296857711938807505509)
                  ·
                    refine ⟨872868160820988526407283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655296857711938807505509 872868160820988526407283)
                    ·
                      rfl

theorem cell23_5099714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5099714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099714 prefixEnd_5099714 := by exact prefixLift 5099714
  have htrace : WordTrace (prefixWord ++ tailWord_5099714) baseStart_5099714 baseEnd_5099714 := by
    simpa [prefixWord, tailWord_5099714, baseEnd_5099714] using wordTrace_append hprefix tailTrace_5099714
  have hstable : (prefixWord ++ tailWord_5099714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099714).length < 2 ^ (prefixWord ++ tailWord_5099714).sum := by decide
  have hdescent : baseEnd_5099714 < baseStart_5099714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099729 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_5099729 : Nat := 118140960795 + 5099729 * 2 ^ 59
def prefixEnd_5099729 : Nat := 4983230072969 + 3 ^ 40 * 5099729 * 2
def baseEnd_5099729 : Nat := 2618612184672783020534279

theorem tailTrace_5099729 : CollatzResearch.WordTrace tailWord_5099729 prefixEnd_5099729 2618612184672783020534279 := by
  unfold tailWord_5099729
  simp only [CollatzResearch.WordTrace]
  refine ⟨186002397341560272217294241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124001598227706848144862827 186002397341560272217294241)
  ·
    refine ⟨139501798006170204162970681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186002397341560272217294241 139501798006170204162970681)
    ·
      refine ⟨104626348504627653122228011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139501798006170204162970681 104626348504627653122228011)
      ·
        refine ⟨156939522756941479683342017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104626348504627653122228011 156939522756941479683342017)
        ·
          refine ⟨117704642067706109762506513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156939522756941479683342017 117704642067706109762506513)
          ·
            refine ⟨88278481550779582321879885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117704642067706109762506513 88278481550779582321879885)
            ·
              refine ⟨33104430581542343370704957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88278481550779582321879885 33104430581542343370704957)
              ·
                refine ⟨12414161468078378764014359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33104430581542343370704957 12414161468078378764014359)
                ·
                  refine ⟨18621242202117568146021539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12414161468078378764014359 18621242202117568146021539)
                  ·
                    refine ⟨27931863303176352219032309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18621242202117568146021539 27931863303176352219032309)
                    ·
                      refine ⟨2618612184672783020534279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27931863303176352219032309 2618612184672783020534279)
                      ·
                        rfl

theorem cell23_5099729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_5099729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099729 prefixEnd_5099729 := by exact prefixLift 5099729
  have htrace : WordTrace (prefixWord ++ tailWord_5099729) baseStart_5099729 baseEnd_5099729 := by
    simpa [prefixWord, tailWord_5099729, baseEnd_5099729] using wordTrace_append hprefix tailTrace_5099729
  have hstable : (prefixWord ++ tailWord_5099729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099729).length < 2 ^ (prefixWord ++ tailWord_5099729).sum := by decide
  have hdescent : baseEnd_5099729 < baseStart_5099729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099736 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_5099736 : Nat := 118140960795 + 5099736 * 2 ^ 59
def prefixEnd_5099736 : Nat := 4983230072969 + 3 ^ 40 * 5099736 * 2
def baseEnd_5099736 : Nat := 872871926345788164382249

theorem tailTrace_5099736 : CollatzResearch.WordTrace tailWord_5099736 prefixEnd_5099736 872871926345788164382249 := by
  unfold tailWord_5099736
  simp only [CollatzResearch.WordTrace]
  refine ⟨93001326326267456206399531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124001768435023274941866041 93001326326267456206399531)
  ·
    refine ⟨139501989489401184309599297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93001326326267456206399531 139501989489401184309599297)
    ·
      refine ⟨104626492117050888232199473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139501989489401184309599297 104626492117050888232199473)
      ·
        refine ⟨78469869087788166174149605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104626492117050888232199473 78469869087788166174149605)
        ·
          refine ⟨14713100453960281157653051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78469869087788166174149605 14713100453960281157653051)
          ·
            refine ⟨22069650680940421736479577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14713100453960281157653051 22069650680940421736479577)
            ·
              refine ⟨16552238010705316302359683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22069650680940421736479577 16552238010705316302359683)
              ·
                refine ⟨24828357016057974453539525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16552238010705316302359683 24828357016057974453539525)
                ·
                  refine ⟨4655316940510870210038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24828357016057974453539525 4655316940510870210038661)
                  ·
                    refine ⟨872871926345788164382249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655316940510870210038661 872871926345788164382249)
                    ·
                      rfl

theorem cell23_5099736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_5099736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099736 prefixEnd_5099736 := by exact prefixLift 5099736
  have htrace : WordTrace (prefixWord ++ tailWord_5099736) baseStart_5099736 baseEnd_5099736 := by
    simpa [prefixWord, tailWord_5099736, baseEnd_5099736] using wordTrace_append hprefix tailTrace_5099736
  have hstable : (prefixWord ++ tailWord_5099736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099736).length < 2 ^ (prefixWord ++ tailWord_5099736).sum := by decide
  have hdescent : baseEnd_5099736 < baseStart_5099736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099749 : List Nat := [1, 3, 1, 4, 2, 1, 1, 10]
def baseStart_5099749 : Nat := 118140960795 + 5099749 * 2 ^ 59
def prefixEnd_5099749 : Nat := 4983230072969 + 3 ^ 40 * 5099749 * 2
def baseEnd_5099749 : Nat := 96986016825402701566081

theorem tailTrace_5099749 : CollatzResearch.WordTrace tailWord_5099749 prefixEnd_5099749 96986016825402701566081 := by
  unfold tailWord_5099749
  simp only [CollatzResearch.WordTrace]
  refine ⟨186003126801487815633022301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124002084534325210422014867 186003126801487815633022301)
  ·
    refine ⟨69751172550557930862383363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186003126801487815633022301 69751172550557930862383363)
    ·
      refine ⟨104626758825836896293575045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69751172550557930862383363 104626758825836896293575045)
      ·
        refine ⟨19617517279844418055045321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104626758825836896293575045 19617517279844418055045321)
        ·
          refine ⟨14713137959883313541283991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19617517279844418055045321 14713137959883313541283991)
          ·
            refine ⟨22069706939824970311925987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14713137959883313541283991 22069706939824970311925987)
            ·
              refine ⟨33104560409737455467888981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22069706939824970311925987 33104560409737455467888981)
              ·
                refine ⟨96986016825402701566081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33104560409737455467888981 96986016825402701566081)
                ·
                  rfl

theorem cell23_5099749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 10].length) (baseStart_5099749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099749 prefixEnd_5099749 := by exact prefixLift 5099749
  have htrace : WordTrace (prefixWord ++ tailWord_5099749) baseStart_5099749 baseEnd_5099749 := by
    simpa [prefixWord, tailWord_5099749, baseEnd_5099749] using wordTrace_append hprefix tailTrace_5099749
  have hstable : (prefixWord ++ tailWord_5099749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099749).length < 2 ^ (prefixWord ++ tailWord_5099749).sum := by decide
  have hdescent : baseEnd_5099749 < baseStart_5099749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099776 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3]
def baseStart_5099776 : Nat := 118140960795 + 5099776 * 2 ^ 59
def prefixEnd_5099776 : Nat := 4983230072969 + 3 ^ 40 * 5099776 * 2
def baseEnd_5099776 : Nat := 2618636318263544336646563

theorem tailTrace_5099776 : CollatzResearch.WordTrace tailWord_5099776 prefixEnd_5099776 2618636318263544336646563 := by
  unfold tailWord_5099776
  simp only [CollatzResearch.WordTrace]
  refine ⟨93002055786194999622127591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124002741048259999496170121 93002055786194999622127591)
  ·
    refine ⟨139503083679292499433191387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93002055786194999622127591 139503083679292499433191387)
    ·
      refine ⟨209254625518938749149787081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139503083679292499433191387 209254625518938749149787081)
      ·
        refine ⟨156940969139204061862340311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209254625518938749149787081 156940969139204061862340311)
        ·
          refine ⟨235411453708806092793510467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156940969139204061862340311 235411453708806092793510467)
          ·
            refine ⟨353117180563209139190265701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235411453708806092793510467 353117180563209139190265701)
            ·
              refine ⟨66209471355601713598174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353117180563209139190265701 66209471355601713598174819)
              ·
                refine ⟨99314207033402570397262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66209471355601713598174819 99314207033402570397262229)
                ·
                  refine ⟨4655353454690745487371667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99314207033402570397262229 4655353454690745487371667)
                  ·
                    refine ⟨6983030182036118231057501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655353454690745487371667 6983030182036118231057501)
                    ·
                      refine ⟨2618636318263544336646563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983030182036118231057501 2618636318263544336646563)
                      ·
                        rfl

theorem cell23_5099776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_5099776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099776 prefixEnd_5099776 := by exact prefixLift 5099776
  have htrace : WordTrace (prefixWord ++ tailWord_5099776) baseStart_5099776 baseEnd_5099776 := by
    simpa [prefixWord, tailWord_5099776, baseEnd_5099776] using wordTrace_append hprefix tailTrace_5099776
  have hstable : (prefixWord ++ tailWord_5099776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099776).length < 2 ^ (prefixWord ++ tailWord_5099776).sum := by decide
  have hdescent : baseEnd_5099776 < baseStart_5099776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099780 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_5099780 : Nat := 118140960795 + 5099780 * 2 ^ 59
def prefixEnd_5099780 : Nat := 4983230072969 + 3 ^ 40 * 5099780 * 2
def baseEnd_5099780 : Nat := 2618638372186162320996545

theorem tailTrace_5099780 : CollatzResearch.WordTrace tailWord_5099780 prefixEnd_5099780 2618638372186162320996545 := by
  unfold tailWord_5099780
  simp only [CollatzResearch.WordTrace]
  refine ⟨93002128732187753963700397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124002838309583671951600529 93002128732187753963700397)
  ·
    refine ⟨34875798274570407736387649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93002128732187753963700397 34875798274570407736387649)
    ·
      refine ⟨26156848705927805802290737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34875798274570407736387649 26156848705927805802290737)
      ·
        refine ⟨19617636529445854351718053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26156848705927805802290737 19617636529445854351718053)
        ·
          refine ⟨3678306849271097690947135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19617636529445854351718053 3678306849271097690947135)
          ·
            refine ⟨5517460273906646536420703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678306849271097690947135 5517460273906646536420703)
            ·
              refine ⟨8276190410859969804631055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517460273906646536420703 8276190410859969804631055)
              ·
                refine ⟨12414285616289954706946583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8276190410859969804631055 12414285616289954706946583)
                ·
                  refine ⟨18621428424434932060419875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12414285616289954706946583 18621428424434932060419875)
                  ·
                    refine ⟨27932142636652398090629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18621428424434932060419875 27932142636652398090629813)
                    ·
                      refine ⟨2618638372186162320996545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27932142636652398090629813 2618638372186162320996545)
                      ·
                        rfl

theorem cell23_5099780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_5099780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099780 prefixEnd_5099780 := by exact prefixLift 5099780
  have htrace : WordTrace (prefixWord ++ tailWord_5099780) baseStart_5099780 baseEnd_5099780 := by
    simpa [prefixWord, tailWord_5099780, baseEnd_5099780] using wordTrace_append hprefix tailTrace_5099780
  have hstable : (prefixWord ++ tailWord_5099780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099780).length < 2 ^ (prefixWord ++ tailWord_5099780).sum := by decide
  have hdescent : baseEnd_5099780 < baseStart_5099780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099793 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_5099793 : Nat := 118140960795 + 5099793 * 2 ^ 59
def prefixEnd_5099793 : Nat := 4983230072969 + 3 ^ 40 * 5099793 * 2
def baseEnd_5099793 : Nat := 2618645047434670770133985

theorem tailTrace_5099793 : CollatzResearch.WordTrace tailWord_5099793 prefixEnd_5099793 2618645047434670770133985 := by
  unfold tailWord_5099793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186004731613328411147624033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124003154408885607431749355 186004731613328411147624033)
  ·
    refine ⟨139503548709996308360718025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186004731613328411147624033 139503548709996308360718025)
    ·
      refine ⟨104627661532497231270538519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139503548709996308360718025 104627661532497231270538519)
      ·
        refine ⟨156941492298745846905807779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104627661532497231270538519 156941492298745846905807779)
        ·
          refine ⟨235412238448118770358711669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156941492298745846905807779 235412238448118770358711669)
          ·
            refine ⟨22069897354511134721129219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235412238448118770358711669 22069897354511134721129219)
            ·
              refine ⟨33104846031766702081693829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22069897354511134721129219 33104846031766702081693829)
              ·
                refine ⟨6207158630956256640317593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33104846031766702081693829 6207158630956256640317593)
                ·
                  refine ⟨4655368973217192480238195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207158630956256640317593 4655368973217192480238195)
                  ·
                    refine ⟨6983053459825788720357293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655368973217192480238195 6983053459825788720357293)
                    ·
                      refine ⟨2618645047434670770133985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983053459825788720357293 2618645047434670770133985)
                      ·
                        rfl

theorem cell23_5099793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_5099793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099793 prefixEnd_5099793 := by exact prefixLift 5099793
  have htrace : WordTrace (prefixWord ++ tailWord_5099793) baseStart_5099793 baseEnd_5099793 := by
    simpa [prefixWord, tailWord_5099793, baseEnd_5099793] using wordTrace_append hprefix tailTrace_5099793
  have hstable : (prefixWord ++ tailWord_5099793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099793).length < 2 ^ (prefixWord ++ tailWord_5099793).sum := by decide
  have hdescent : baseEnd_5099793 < baseStart_5099793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099809 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_5099809 : Nat := 118140960795 + 5099809 * 2 ^ 59
def prefixEnd_5099809 : Nat := 4983230072969 + 3 ^ 40 * 5099809 * 2
def baseEnd_5099809 : Nat := 872884421041714235844637

theorem tailTrace_5099809 : CollatzResearch.WordTrace tailWord_5099809 prefixEnd_5099809 872884421041714235844637 := by
  unfold tailWord_5099809
  simp only [CollatzResearch.WordTrace]
  refine ⟨186005315181270445880206481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124003543454180297253470987 186005315181270445880206481)
  ·
    refine ⟨139503986385952834410154861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186005315181270445880206481 139503986385952834410154861)
    ·
      refine ⟨52313994894732312903808073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139503986385952834410154861 52313994894732312903808073)
      ·
        refine ⟨39235496171049234677856055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52313994894732312903808073 39235496171049234677856055)
        ·
          refine ⟨58853244256573852016784083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39235496171049234677856055 58853244256573852016784083)
          ·
            refine ⟨88279866384860778025176125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58853244256573852016784083 88279866384860778025176125)
            ·
              refine ⟨33104949894322791759441047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88279866384860778025176125 33104949894322791759441047)
              ·
                refine ⟨49657424841484187639161571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33104949894322791759441047 49657424841484187639161571)
                ·
                  refine ⟨74486137262226281458742357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49657424841484187639161571 74486137262226281458742357)
                  ·
                    refine ⟨872884421041714235844637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74486137262226281458742357 872884421041714235844637)
                    ·
                      rfl

theorem cell23_5099809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_5099809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099809 prefixEnd_5099809 := by exact prefixLift 5099809
  have htrace : WordTrace (prefixWord ++ tailWord_5099809) baseStart_5099809 baseEnd_5099809 := by
    simpa [prefixWord, tailWord_5099809, baseEnd_5099809] using wordTrace_append hprefix tailTrace_5099809
  have hstable : (prefixWord ++ tailWord_5099809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099809).length < 2 ^ (prefixWord ++ tailWord_5099809).sum := by decide
  have hdescent : baseEnd_5099809 < baseStart_5099809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099810 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_5099810 : Nat := 118140960795 + 5099810 * 2 ^ 59
def prefixEnd_5099810 : Nat := 4983230072969 + 3 ^ 40 * 5099810 * 2
def baseEnd_5099810 : Nat := 2618653776605797203621407

theorem tailTrace_5099810 : CollatzResearch.WordTrace tailWord_5099810 prefixEnd_5099810 2618653776605797203621407 := by
  unfold tailWord_5099810
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501337913566705762748221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124003567769511215367328589 46501337913566705762748221)
  ·
    refine ⟨17438001717587514661030583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46501337913566705762748221 17438001717587514661030583)
    ·
      refine ⟨26157002576381271991545875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17438001717587514661030583 26157002576381271991545875)
      ·
        refine ⟨39235503864571907987318813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26157002576381271991545875 39235503864571907987318813)
        ·
          refine ⟨14713313949214465495244555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39235503864571907987318813 14713313949214465495244555)
          ·
            refine ⟨22069970923821698242866833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14713313949214465495244555 22069970923821698242866833)
            ·
              refine ⟨16552478192866273682150125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22069970923821698242866833 16552478192866273682150125)
              ·
                refine ⟨6207179322324852630806297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16552478192866273682150125 6207179322324852630806297)
                ·
                  refine ⟨4655384491743639473104723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207179322324852630806297 4655384491743639473104723)
                  ·
                    refine ⟨6983076737615459209657085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655384491743639473104723 6983076737615459209657085)
                    ·
                      refine ⟨2618653776605797203621407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983076737615459209657085 2618653776605797203621407)
                      ·
                        rfl

theorem cell23_5099810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_5099810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099810 prefixEnd_5099810 := by exact prefixLift 5099810
  have htrace : WordTrace (prefixWord ++ tailWord_5099810) baseStart_5099810 baseEnd_5099810 := by
    simpa [prefixWord, tailWord_5099810, baseEnd_5099810] using wordTrace_append hprefix tailTrace_5099810
  have hstable : (prefixWord ++ tailWord_5099810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099810).length < 2 ^ (prefixWord ++ tailWord_5099810).sum := by decide
  have hdescent : baseEnd_5099810 < baseStart_5099810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099839 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 9]
def baseStart_5099839 : Nat := 118140960795 + 5099839 * 2 ^ 59
def prefixEnd_5099839 : Nat := 4983230072969 + 3 ^ 40 * 5099839 * 2
def baseEnd_5099839 : Nat := 290963185282753065573197

theorem tailTrace_5099839 : CollatzResearch.WordTrace tailWord_5099839 prefixEnd_5099839 290963185282753065573197 := by
  unfold tailWord_5099839
  simp only [CollatzResearch.WordTrace]
  refine ⟨186006409371161761003798571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124004272914107840669199047 186006409371161761003798571)
  ·
    refine ⟨279009614056742641505697857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186006409371161761003798571 279009614056742641505697857)
    ·
      refine ⟨209257210542556981129273393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279009614056742641505697857 209257210542556981129273393)
      ·
        refine ⟨156942907906917735846955045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209257210542556981129273393 156942907906917735846955045)
        ·
          refine ⟨29426795232547075471304071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156942907906917735846955045 29426795232547075471304071)
          ·
            refine ⟨44140192848820613206956107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29426795232547075471304071 44140192848820613206956107)
            ·
              refine ⟨66210289273230919810434161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44140192848820613206956107 66210289273230919810434161)
              ·
                refine ⟨49657716954923189857825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66210289273230919810434161 49657716954923189857825621)
                ·
                  refine ⟨290963185282753065573197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49657716954923189857825621 290963185282753065573197)
                  ·
                    rfl

theorem cell23_5099839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 9].length) (baseStart_5099839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099839 prefixEnd_5099839 := by exact prefixLift 5099839
  have htrace : WordTrace (prefixWord ++ tailWord_5099839) baseStart_5099839 baseEnd_5099839 := by
    simpa [prefixWord, tailWord_5099839, baseEnd_5099839] using wordTrace_append hprefix tailTrace_5099839
  have hstable : (prefixWord ++ tailWord_5099839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099839).length < 2 ^ (prefixWord ++ tailWord_5099839).sum := by decide
  have hdescent : baseEnd_5099839 < baseStart_5099839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099844 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5099844 : Nat := 118140960795 + 5099844 * 2 ^ 59
def prefixEnd_5099844 : Nat := 4983230072969 + 3 ^ 40 * 5099844 * 2
def baseEnd_5099844 : Nat := 2618671234948050070596251

theorem tailTrace_5099844 : CollatzResearch.WordTrace tailWord_5099844 prefixEnd_5099844 2618671234948050070596251 := by
  unfold tailWord_5099844
  simp only [CollatzResearch.WordTrace]
  refine ⟨93003295868071823428865293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124004394490762431238487057 93003295868071823428865293)
  ·
    refine ⟨34876235950526933785824485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93003295868071823428865293 34876235950526933785824485)
    ·
      refine ⟨6539294240723800084842091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34876235950526933785824485 6539294240723800084842091)
      ·
        refine ⟨9808941361085700127263137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6539294240723800084842091 9808941361085700127263137)
        ·
          refine ⟨7356706020814275095447353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9808941361085700127263137 7356706020814275095447353)
          ·
            refine ⟨5517529515610706321585515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7356706020814275095447353 5517529515610706321585515)
            ·
              refine ⟨8276294273416059482378273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517529515610706321585515 8276294273416059482378273)
              ·
                refine ⟨6207220705062044611783705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8276294273416059482378273 6207220705062044611783705)
                ·
                  refine ⟨4655415528796533458837779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207220705062044611783705 4655415528796533458837779)
                  ·
                    refine ⟨6983123293194800188256669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655415528796533458837779 6983123293194800188256669)
                    ·
                      refine ⟨2618671234948050070596251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983123293194800188256669 2618671234948050070596251)
                      ·
                        rfl

theorem cell23_5099844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5099844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099844 prefixEnd_5099844 := by exact prefixLift 5099844
  have htrace : WordTrace (prefixWord ++ tailWord_5099844) baseStart_5099844 baseEnd_5099844 := by
    simpa [prefixWord, tailWord_5099844, baseEnd_5099844] using wordTrace_append hprefix tailTrace_5099844
  have hstable : (prefixWord ++ tailWord_5099844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099844).length < 2 ^ (prefixWord ++ tailWord_5099844).sum := by decide
  have hdescent : baseEnd_5099844 < baseStart_5099844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099856 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 7]
def baseStart_5099856 : Nat := 118140960795 + 5099856 * 2 ^ 59
def prefixEnd_5099856 : Nat := 4983230072969 + 3 ^ 40 * 5099856 * 2
def baseEnd_5099856 : Nat := 290964155190656002627355

theorem tailTrace_5099856 : CollatzResearch.WordTrace tailWord_5099856 prefixEnd_5099856 290964155190656002627355 := by
  unfold tailWord_5099856
  simp only [CollatzResearch.WordTrace]
  refine ⟨93003514706050086453583711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124004686274733448604778281 93003514706050086453583711)
  ·
    refine ⟨139505272059075129680375567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93003514706050086453583711 139505272059075129680375567)
    ·
      refine ⟨209257908088612694520563351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139505272059075129680375567 209257908088612694520563351)
      ·
        refine ⟨313886862132919041780845027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209257908088612694520563351 313886862132919041780845027)
        ·
          refine ⟨470830293199378562671267541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313886862132919041780845027 470830293199378562671267541)
          ·
            refine ⟨11035084996860435062607833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 470830293199378562671267541 11035084996860435062607833)
            ·
              refine ⟨8276313747645326296955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11035084996860435062607833 8276313747645326296955875)
              ·
                refine ⟨12414470621467989445433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8276313747645326296955875 12414470621467989445433813)
                ·
                  refine ⟨290964155190656002627355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12414470621467989445433813 290964155190656002627355)
                  ·
                    rfl

theorem cell23_5099856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_5099856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099856 prefixEnd_5099856 := by exact prefixLift 5099856
  have htrace : WordTrace (prefixWord ++ tailWord_5099856) baseStart_5099856 baseEnd_5099856 := by
    simpa [prefixWord, tailWord_5099856, baseEnd_5099856] using wordTrace_append hprefix tailTrace_5099856
  have hstable : (prefixWord ++ tailWord_5099856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099856).length < 2 ^ (prefixWord ++ tailWord_5099856).sum := by decide
  have hdescent : baseEnd_5099856 < baseStart_5099856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099890 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_5099890 : Nat := 118140960795 + 5099890 * 2 ^ 59
def prefixEnd_5099890 : Nat := 4983230072969 + 3 ^ 40 * 5099890 * 2
def baseEnd_5099890 : Nat := 290966095006461876735671

theorem tailTrace_5099890 : CollatzResearch.WordTrace tailWord_5099890 prefixEnd_5099890 290966095006461876735671 := by
  unfold tailWord_5099890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46502067373494249178476281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124005512995984664475936749 46502067373494249178476281)
  ·
    refine ⟨34876550530120686883857211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46502067373494249178476281 34876550530120686883857211)
    ·
      refine ⟨52314825795181030325785817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34876550530120686883857211 52314825795181030325785817)
      ·
        refine ⟨39236119346385772744339363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52314825795181030325785817 39236119346385772744339363)
        ·
          refine ⟨58854179019578659116509045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39236119346385772744339363 58854179019578659116509045)
          ·
            refine ⟨5517579283085499292172723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58854179019578659116509045 5517579283085499292172723)
            ·
              refine ⟨8276368924628248938259085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517579283085499292172723 8276368924628248938259085)
              ·
                refine ⟨3103638346735593351847157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8276368924628248938259085 3103638346735593351847157)
                ·
                  refine ⟨290966095006461876735671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3103638346735593351847157 290966095006461876735671)
                  ·
                    rfl

theorem cell23_5099890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_5099890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099890 prefixEnd_5099890 := by exact prefixLift 5099890
  have htrace : WordTrace (prefixWord ++ tailWord_5099890) baseStart_5099890 baseEnd_5099890 := by
    simpa [prefixWord, tailWord_5099890, baseEnd_5099890] using wordTrace_append hprefix tailTrace_5099890
  have hstable : (prefixWord ++ tailWord_5099890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099890).length < 2 ^ (prefixWord ++ tailWord_5099890).sum := by decide
  have hdescent : baseEnd_5099890 < baseStart_5099890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099973 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_5099973 : Nat := 118140960795 + 5099973 * 2 ^ 59
def prefixEnd_5099973 : Nat := 4983230072969 + 3 ^ 40 * 5099973 * 2
def baseEnd_5099973 : Nat := 2618737473952480065883157

theorem tailTrace_5099973 : CollatzResearch.WordTrace tailWord_5099973 prefixEnd_5099973 2618737473952480065883157 := by
  unfold tailWord_5099973
  simp only [CollatzResearch.WordTrace]
  refine ⟨186011296752676301889176573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124007531168450867926117715 186011296752676301889176573)
  ·
    refine ⟨69754236282253613208441215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186011296752676301889176573 69754236282253613208441215)
    ·
      refine ⟨104631354423380419812661823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69754236282253613208441215 104631354423380419812661823)
      ·
        refine ⟨156947031635070629718992735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104631354423380419812661823 156947031635070629718992735)
        ·
          refine ⟨235420547452605944578489103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156947031635070629718992735 235420547452605944578489103)
          ·
            refine ⟨353130821178908916867733655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235420547452605944578489103 353130821178908916867733655)
            ·
              refine ⟨529696231768363375301600483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353130821178908916867733655 529696231768363375301600483)
              ·
                refine ⟨794544347652545062952400725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529696231768363375301600483 794544347652545062952400725)
                ·
                  refine ⟨4655533287026631228236723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 794544347652545062952400725 4655533287026631228236723)
                  ·
                    refine ⟨6983299930539946842355085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655533287026631228236723 6983299930539946842355085)
                    ·
                      refine ⟨2618737473952480065883157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983299930539946842355085 2618737473952480065883157)
                      ·
                        rfl

theorem cell23_5099973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_5099973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099973 prefixEnd_5099973 := by exact prefixLift 5099973
  have htrace : WordTrace (prefixWord ++ tailWord_5099973) baseStart_5099973 baseEnd_5099973 := by
    simpa [prefixWord, tailWord_5099973, baseEnd_5099973] using wordTrace_append hprefix tailTrace_5099973
  have hstable : (prefixWord ++ tailWord_5099973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099973).length < 2 ^ (prefixWord ++ tailWord_5099973).sum := by decide
  have hdescent : baseEnd_5099973 < baseStart_5099973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099983 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 5, 2]
def baseStart_5099983 : Nat := 118140960795 + 5099983 * 2 ^ 59
def prefixEnd_5099983 : Nat := 4983230072969 + 3 ^ 40 * 5099983 * 2
def baseEnd_5099983 : Nat := 2618742608759025026758111

theorem tailTrace_5099983 : CollatzResearch.WordTrace tailWord_5099983 prefixEnd_5099983 2618742608759025026758111 := by
  unfold tailWord_5099983
  simp only [CollatzResearch.WordTrace]
  refine ⟨186011661482640073597040603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124007774321760049064693735 186011661482640073597040603)
  ·
    refine ⟨279017492223960110395560905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186011661482640073597040603 279017492223960110395560905)
    ·
      refine ⟨209263119167970082796670679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279017492223960110395560905 209263119167970082796670679)
      ·
        refine ⟨313894678751955124195006019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209263119167970082796670679 313894678751955124195006019)
        ·
          refine ⟨470842018127932686292509029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313894678751955124195006019 470842018127932686292509029)
          ·
            refine ⟨88282878398987378679845443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 470842018127932686292509029 88282878398987378679845443)
            ·
              refine ⟨132424317598481068019768165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88282878398987378679845443 132424317598481068019768165)
              ·
                refine ⟨24829559549715200253706531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132424317598481068019768165 24829559549715200253706531)
                ·
                  refine ⟨37244339324572800380559797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24829559549715200253706531 37244339324572800380559797)
                  ·
                    refine ⟨3491656811678700035677481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37244339324572800380559797 3491656811678700035677481)
                    ·
                      refine ⟨2618742608759025026758111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491656811678700035677481 2618742608759025026758111)
                      ·
                        rfl

theorem cell23_5099983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5, 2].length) (baseStart_5099983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099983 prefixEnd_5099983 := by exact prefixLift 5099983
  have htrace : WordTrace (prefixWord ++ tailWord_5099983) baseStart_5099983 baseEnd_5099983 := by
    simpa [prefixWord, tailWord_5099983, baseEnd_5099983] using wordTrace_append hprefix tailTrace_5099983
  have hstable : (prefixWord ++ tailWord_5099983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099983).length < 2 ^ (prefixWord ++ tailWord_5099983).sum := by decide
  have hdescent : baseEnd_5099983 < baseStart_5099983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5099993 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_5099993 : Nat := 118140960795 + 5099993 * 2 ^ 59
def prefixEnd_5099993 : Nat := 4983230072969 + 3 ^ 40 * 5099993 * 2
def baseEnd_5099993 : Nat := 872915914521856662544355

theorem tailTrace_5099993 : CollatzResearch.WordTrace tailWord_5099993 prefixEnd_5099993 872915914521856662544355 := by
  unfold tailWord_5099993
  simp only [CollatzResearch.WordTrace]
  refine ⟨186012026212603845304904633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124008017475069230203269755 186012026212603845304904633)
  ·
    refine ⟨139509019659452883978678475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186012026212603845304904633 139509019659452883978678475)
    ·
      refine ⟨209263529489179325968017713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139509019659452883978678475 209263529489179325968017713)
      ·
        refine ⟨156947647116884494476013285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209263529489179325968017713 156947647116884494476013285)
        ·
          refine ⟨29427683834415842714252491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156947647116884494476013285 29427683834415842714252491)
          ·
            refine ⟨44141525751623764071378737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29427683834415842714252491 44141525751623764071378737)
            ·
              refine ⟨33106144313717823053534053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44141525751623764071378737 33106144313717823053534053)
              ·
                refine ⟨6207402058822091822537635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33106144313717823053534053 6207402058822091822537635)
                ·
                  refine ⟨9311103088233137733806453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207402058822091822537635 9311103088233137733806453)
                  ·
                    refine ⟨872915914521856662544355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9311103088233137733806453 872915914521856662544355)
                    ·
                      rfl

theorem cell23_5099993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_5099993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5099993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5099993 prefixEnd_5099993 := by exact prefixLift 5099993
  have htrace : WordTrace (prefixWord ++ tailWord_5099993) baseStart_5099993 baseEnd_5099993 := by
    simpa [prefixWord, tailWord_5099993, baseEnd_5099993] using wordTrace_append hprefix tailTrace_5099993
  have hstable : (prefixWord ++ tailWord_5099993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5099993).length < 2 ^ (prefixWord ++ tailWord_5099993).sum := by decide
  have hdescent : baseEnd_5099993 < baseStart_5099993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5099993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100010 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_5100010 : Nat := 118140960795 + 5100010 * 2 ^ 59
def prefixEnd_5100010 : Nat := 4983230072969 + 3 ^ 40 * 5100010 * 2
def baseEnd_5100010 : Nat := 872918824245565473706829

theorem tailTrace_5100010 : CollatzResearch.WordTrace tailWord_5100010 prefixEnd_5100010 872918824245565473706829 := by
  unfold tailWord_5100010
  simp only [CollatzResearch.WordTrace]
  refine ⟨46503161563385564302068371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124008430835694838138848989 46503161563385564302068371)
  ·
    refine ⟨69754742345078346453102557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46503161563385564302068371 69754742345078346453102557)
    ·
      refine ⟨26158028379404379919913459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69754742345078346453102557 26158028379404379919913459)
      ·
        refine ⟨39237042569106569879870189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26158028379404379919913459 39237042569106569879870189)
        ·
          refine ⟨14713890963414963704951321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39237042569106569879870189 14713890963414963704951321)
          ·
            refine ⟨11035418222561222778713491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14713890963414963704951321 11035418222561222778713491)
            ·
              refine ⟨16553127333841834168070237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035418222561222778713491 16553127333841834168070237)
              ·
                refine ⟨6207422750190687813026339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16553127333841834168070237 6207422750190687813026339)
                ·
                  refine ⟨9311134125286031719539509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207422750190687813026339 9311134125286031719539509)
                  ·
                    refine ⟨872918824245565473706829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9311134125286031719539509 872918824245565473706829)
                    ·
                      rfl

theorem cell23_5100010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_5100010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100010 prefixEnd_5100010 := by exact prefixLift 5100010
  have htrace : WordTrace (prefixWord ++ tailWord_5100010) baseStart_5100010 baseEnd_5100010 := by
    simpa [prefixWord, tailWord_5100010, baseEnd_5100010] using wordTrace_append hprefix tailTrace_5100010
  have hstable : (prefixWord ++ tailWord_5100010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100010).length < 2 ^ (prefixWord ++ tailWord_5100010).sum := by decide
  have hdescent : baseEnd_5100010 < baseStart_5100010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100033 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5100033 : Nat := 118140960795 + 5100033 * 2 ^ 59
def prefixEnd_5100033 : Nat := 4983230072969 + 3 ^ 40 * 5100033 * 2
def baseEnd_5100033 : Nat := 2618768282791749831132881

theorem tailTrace_5100033 : CollatzResearch.WordTrace tailWord_5100033 prefixEnd_5100033 2618768282791749831132881 := by
  unfold tailWord_5100033
  simp only [CollatzResearch.WordTrace]
  refine ⟨186013485132458932136360753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124008990088305954757573835 186013485132458932136360753)
  ·
    refine ⟨139510113849344199102270565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186013485132458932136360753 139510113849344199102270565)
    ·
      refine ⟨26158146346752037331675731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139510113849344199102270565 26158146346752037331675731)
      ·
        refine ⟨39237219520128055997513597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26158146346752037331675731 39237219520128055997513597)
        ·
          refine ⟨14713957320048020999067599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39237219520128055997513597 14713957320048020999067599)
          ·
            refine ⟨22070935980072031498601399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14713957320048020999067599 22070935980072031498601399)
            ·
              refine ⟨33106403970108047247902099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22070935980072031498601399 33106403970108047247902099)
              ·
                refine ⟨49659605955162070871853149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33106403970108047247902099 49659605955162070871853149)
                ·
                  refine ⟨18622352233185776576944931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49659605955162070871853149 18622352233185776576944931)
                  ·
                    refine ⟨27933528349778664865417397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18622352233185776576944931 27933528349778664865417397)
                    ·
                      refine ⟨2618768282791749831132881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27933528349778664865417397 2618768282791749831132881)
                      ·
                        rfl

theorem cell23_5100033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5100033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100033 prefixEnd_5100033 := by exact prefixLift 5100033
  have htrace : WordTrace (prefixWord ++ tailWord_5100033) baseStart_5100033 baseEnd_5100033 := by
    simpa [prefixWord, tailWord_5100033, baseEnd_5100033] using wordTrace_append hprefix tailTrace_5100033
  have hstable : (prefixWord ++ tailWord_5100033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100033).length < 2 ^ (prefixWord ++ tailWord_5100033).sum := by decide
  have hdescent : baseEnd_5100033 < baseStart_5100033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100043 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6]
def baseStart_5100043 : Nat := 118140960795 + 5100043 * 2 ^ 59
def prefixEnd_5100043 : Nat := 4983230072969 + 3 ^ 40 * 5100043 * 2
def baseEnd_5100043 : Nat := 2618773417598294792007835

theorem tailTrace_5100043 : CollatzResearch.WordTrace tailWord_5100043 prefixEnd_5100043 2618773417598294792007835 := by
  unfold tailWord_5100043
  simp only [CollatzResearch.WordTrace]
  refine ⟨186013849862422703844224783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124009233241615135896149855 186013849862422703844224783)
  ·
    refine ⟨279020774793634055766337175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186013849862422703844224783 279020774793634055766337175)
    ·
      refine ⟨418531162190451083649505763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279020774793634055766337175 418531162190451083649505763)
      ·
        refine ⟨627796743285676625474258645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418531162190451083649505763 627796743285676625474258645)
        ·
          refine ⟨14713986170758045909552937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 627796743285676625474258645 14713986170758045909552937)
          ·
            refine ⟨11035489628068534432164703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14713986170758045909552937 11035489628068534432164703)
            ·
              refine ⟨16553234442102801648247055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035489628068534432164703 16553234442102801648247055)
              ·
                refine ⟨24829851663154202472370583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16553234442102801648247055 24829851663154202472370583)
                ·
                  refine ⟨37244777494731303708555875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24829851663154202472370583 37244777494731303708555875)
                  ·
                    refine ⟨55867166242096955562833813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37244777494731303708555875 55867166242096955562833813)
                    ·
                      refine ⟨2618773417598294792007835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55867166242096955562833813 2618773417598294792007835)
                      ·
                        rfl

theorem cell23_5100043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 6].length) (baseStart_5100043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100043 prefixEnd_5100043 := by exact prefixLift 5100043
  have htrace : WordTrace (prefixWord ++ tailWord_5100043) baseStart_5100043 baseEnd_5100043 := by
    simpa [prefixWord, tailWord_5100043, baseEnd_5100043] using wordTrace_append hprefix tailTrace_5100043
  have hstable : (prefixWord ++ tailWord_5100043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100043).length < 2 ^ (prefixWord ++ tailWord_5100043).sum := by decide
  have hdescent : baseEnd_5100043 < baseStart_5100043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100063 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_5100063 : Nat := 118140960795 + 5100063 * 2 ^ 59
def prefixEnd_5100063 : Nat := 4983230072969 + 3 ^ 40 * 5100063 * 2
def baseEnd_5100063 : Nat := 2618783687211384713757743

theorem tailTrace_5100063 : CollatzResearch.WordTrace tailWord_5100063 prefixEnd_5100063 2618783687211384713757743 := by
  unfold tailWord_5100063
  simp only [CollatzResearch.WordTrace]
  refine ⟨186014579322350247259952843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124009719548233498173301895 186014579322350247259952843)
  ·
    refine ⟨279021868983525370889929265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186014579322350247259952843 279021868983525370889929265)
    ·
      refine ⟨209266401737644028167446949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279021868983525370889929265 209266401737644028167446949)
      ·
        refine ⟨39237450325808255281396303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209266401737644028167446949 39237450325808255281396303)
        ·
          refine ⟨58856175488712382922094455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39237450325808255281396303 58856175488712382922094455)
          ·
            refine ⟨88284263233068574383141683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58856175488712382922094455 88284263233068574383141683)
            ·
              refine ⟨132426394849602861574712525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88284263233068574383141683 132426394849602861574712525)
              ·
                refine ⟨49659898068601073090517197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132426394849602861574712525 49659898068601073090517197)
                ·
                  refine ⟨18622461775725402408943949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49659898068601073090517197 18622461775725402408943949)
                  ·
                    refine ⟨6983423165897025903353981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18622461775725402408943949 6983423165897025903353981)
                    ·
                      refine ⟨2618783687211384713757743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983423165897025903353981 2618783687211384713757743)
                      ·
                        rfl

theorem cell23_5100063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_5100063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100063 prefixEnd_5100063 := by exact prefixLift 5100063
  have htrace : WordTrace (prefixWord ++ tailWord_5100063) baseStart_5100063 baseEnd_5100063 := by
    simpa [prefixWord, tailWord_5100063, baseEnd_5100063] using wordTrace_append hprefix tailTrace_5100063
  have hstable : (prefixWord ++ tailWord_5100063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100063).length < 2 ^ (prefixWord ++ tailWord_5100063).sum := by decide
  have hdescent : baseEnd_5100063 < baseStart_5100063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100080 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3]
def baseStart_5100080 : Nat := 118140960795 + 5100080 * 2 ^ 59
def prefixEnd_5100080 : Nat := 4983230072969 + 3 ^ 40 * 5100080 * 2
def baseEnd_5100080 : Nat := 2618792416382511147245165

theorem tailTrace_5100080 : CollatzResearch.WordTrace tailWord_5100080 prefixEnd_5100080 2618792416382511147245165 := by
  unfold tailWord_5100080
  simp only [CollatzResearch.WordTrace]
  refine ⟨93007599681644329581660847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124010132908859106108881129 93007599681644329581660847)
  ·
    refine ⟨139511399522466494372491271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93007599681644329581660847 139511399522466494372491271)
    ·
      refine ⟨209267099283699741558736907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139511399522466494372491271 209267099283699741558736907)
      ·
        refine ⟨313900648925549612338105361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209267099283699741558736907 313900648925549612338105361)
        ·
          refine ⟨235425486694162209253579021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313900648925549612338105361 235425486694162209253579021)
          ·
            refine ⟨88284557510310828470092133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235425486694162209253579021 88284557510310828470092133)
            ·
              refine ⟨16553354533183280338142275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88284557510310828470092133 16553354533183280338142275)
              ·
                refine ⟨24830031799774920507213413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16553354533183280338142275 24830031799774920507213413)
                ·
                  refine ⟨4655630962457797595102515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24830031799774920507213413 4655630962457797595102515)
                  ·
                    refine ⟨6983446443686696392653773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655630962457797595102515 6983446443686696392653773)
                    ·
                      refine ⟨2618792416382511147245165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983446443686696392653773 2618792416382511147245165)
                      ·
                        rfl

theorem cell23_5100080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 1, 3].length) (baseStart_5100080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100080 prefixEnd_5100080 := by exact prefixLift 5100080
  have htrace : WordTrace (prefixWord ++ tailWord_5100080) baseStart_5100080 baseEnd_5100080 := by
    simpa [prefixWord, tailWord_5100080, baseEnd_5100080] using wordTrace_append hprefix tailTrace_5100080
  have hstable : (prefixWord ++ tailWord_5100080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100080).length < 2 ^ (prefixWord ++ tailWord_5100080).sum := by decide
  have hdescent : baseEnd_5100080 < baseStart_5100080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100107 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 1, 3, 2]
def baseStart_5100107 : Nat := 118140960795 + 5100107 * 2 ^ 59
def prefixEnd_5100107 : Nat := 4983230072969 + 3 ^ 40 * 5100107 * 2
def baseEnd_5100107 : Nat := 2618806280360182541607541

theorem tailTrace_5100107 : CollatzResearch.WordTrace tailWord_5100107 prefixEnd_5100107 2618806280360182541607541 := by
  unfold tailWord_5100107
  simp only [CollatzResearch.WordTrace]
  refine ⟨186016184134190842774554575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124010789422793895183036383 186016184134190842774554575)
  ·
    refine ⟨279024276201286264161831863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186016184134190842774554575 279024276201286264161831863)
    ·
      refine ⟨418536414301929396242747795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279024276201286264161831863 418536414301929396242747795)
      ·
        refine ⟨627804621452894094364121693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418536414301929396242747795 627804621452894094364121693)
        ·
          refine ⟨235426733044835285386545635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627804621452894094364121693 235426733044835285386545635)
          ·
            refine ⟨353140099567252928079818453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235426733044835285386545635 353140099567252928079818453)
            ·
              refine ⟨8276721083607490501870745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 353140099567252928079818453 8276721083607490501870745)
              ·
                refine ⟨6207540812705617876403059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8276721083607490501870745 6207540812705617876403059)
                ·
                  refine ⟨9311311219058426814604589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207540812705617876403059 9311311219058426814604589)
                  ·
                    refine ⟨3491741707146910055476721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9311311219058426814604589 3491741707146910055476721)
                    ·
                      refine ⟨2618806280360182541607541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491741707146910055476721 2618806280360182541607541)
                      ·
                        rfl

theorem cell23_5100107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3, 2].length) (baseStart_5100107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100107 prefixEnd_5100107 := by exact prefixLift 5100107
  have htrace : WordTrace (prefixWord ++ tailWord_5100107) baseStart_5100107 baseEnd_5100107 := by
    simpa [prefixWord, tailWord_5100107, baseEnd_5100107] using wordTrace_append hprefix tailTrace_5100107
  have hstable : (prefixWord ++ tailWord_5100107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100107).length < 2 ^ (prefixWord ++ tailWord_5100107).sum := by decide
  have hdescent : baseEnd_5100107 < baseStart_5100107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100120 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2]
def baseStart_5100120 : Nat := 118140960795 + 5100120 * 2 ^ 59
def prefixEnd_5100120 : Nat := 4983230072969 + 3 ^ 40 * 5100120 * 2
def baseEnd_5100120 : Nat := 2618812955608690990744981

theorem tailTrace_5100120 : CollatzResearch.WordTrace tailWord_5100120 prefixEnd_5100120 2618812955608690990744981 := by
  unfold tailWord_5100120
  simp only [CollatzResearch.WordTrace]
  refine ⟨93008329141571872997388907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124011105522095830663185209 93008329141571872997388907)
  ·
    refine ⟨139512493712357809496083361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93008329141571872997388907 139512493712357809496083361)
    ·
      refine ⟨104634370284268357122062521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139512493712357809496083361 104634370284268357122062521)
      ·
        refine ⟨78475777713201267841546891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104634370284268357122062521 78475777713201267841546891)
        ·
          refine ⟨117713666569801901762320337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78475777713201267841546891 117713666569801901762320337)
          ·
            refine ⟨88285249927351426321740253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117713666569801901762320337 88285249927351426321740253)
            ·
              refine ⟨33106968722756784870652595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88285249927351426321740253 33106968722756784870652595)
              ·
                refine ⟨49660453084135177305978893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33106968722756784870652595 49660453084135177305978893)
                ·
                  refine ⟨18622669906550691489742085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49660453084135177305978893 18622669906550691489742085)
                  ·
                    refine ⟨3491750607478254654326641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18622669906550691489742085 3491750607478254654326641)
                    ·
                      refine ⟨2618812955608690990744981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3491750607478254654326641 2618812955608690990744981)
                      ·
                        rfl

theorem cell23_5100120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_5100120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100120 prefixEnd_5100120 := by exact prefixLift 5100120
  have htrace : WordTrace (prefixWord ++ tailWord_5100120) baseStart_5100120 baseEnd_5100120 := by
    simpa [prefixWord, tailWord_5100120, baseEnd_5100120] using wordTrace_append hprefix tailTrace_5100120
  have hstable : (prefixWord ++ tailWord_5100120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100120).length < 2 ^ (prefixWord ++ tailWord_5100120).sum := by decide
  have hdescent : baseEnd_5100120 < baseStart_5100120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100244 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5100244 : Nat := 118140960795 + 5100244 * 2 ^ 59
def prefixEnd_5100244 : Nat := 4983230072969 + 3 ^ 40 * 5100244 * 2
def baseEnd_5100244 : Nat := 2618876627209848505594411

theorem tailTrace_5100244 : CollatzResearch.WordTrace tailWord_5100244 prefixEnd_5100244 2618876627209848505594411 := by
  unfold tailWord_5100244
  simp only [CollatzResearch.WordTrace]
  refine ⟨93010590467347257586145893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124014120623129676781527857 93010590467347257586145893)
  ·
    refine ⟨17439485712627610797402355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93010590467347257586145893 17439485712627610797402355)
    ·
      refine ⟨26159228568941416196103533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17439485712627610797402355 26159228568941416196103533)
      ·
        refine ⟨9809710713353031073538825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26159228568941416196103533 9809710713353031073538825)
        ·
          refine ⟨7357283035014773305154119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9809710713353031073538825 7357283035014773305154119)
          ·
            refine ⟨11035924552522159957731179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7357283035014773305154119 11035924552522159957731179)
            ·
              refine ⟨16553886828783239936596769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035924552522159957731179 16553886828783239936596769)
              ·
                refine ⟨12415415121587429952447577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16553886828783239936596769 12415415121587429952447577)
                ·
                  refine ⟨9311561341190572464335683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12415415121587429952447577 9311561341190572464335683)
                  ·
                    refine ⟨13967342011785858696503525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9311561341190572464335683 13967342011785858696503525)
                    ·
                      refine ⟨2618876627209848505594411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13967342011785858696503525 2618876627209848505594411)
                      ·
                        rfl

theorem cell23_5100244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5100244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100244 prefixEnd_5100244 := by exact prefixLift 5100244
  have htrace : WordTrace (prefixWord ++ tailWord_5100244) baseStart_5100244 baseEnd_5100244 := by
    simpa [prefixWord, tailWord_5100244, baseEnd_5100244] using wordTrace_append hprefix tailTrace_5100244
  have hstable : (prefixWord ++ tailWord_5100244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100244).length < 2 ^ (prefixWord ++ tailWord_5100244).sum := by decide
  have hdescent : baseEnd_5100244 < baseStart_5100244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100247 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_5100247 : Nat := 118140960795 + 5100247 * 2 ^ 59
def prefixEnd_5100247 : Nat := 4983230072969 + 3 ^ 40 * 5100247 * 2
def baseEnd_5100247 : Nat := 2618878167651811993856897

theorem tailTrace_5100247 : CollatzResearch.WordTrace tailWord_5100247 prefixEnd_5100247 2618878167651811993856897 := by
  unfold tailWord_5100247
  simp only [CollatzResearch.WordTrace]
  refine ⟨186021290353683646684650995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124014193569122431123100663 186021290353683646684650995)
  ·
    refine ⟨279031935530525470026976493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186021290353683646684650995 279031935530525470026976493)
    ·
      refine ⟨104636975823947051260116185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279031935530525470026976493 104636975823947051260116185)
      ·
        refine ⟨78477731867960288445087139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104636975823947051260116185 78477731867960288445087139)
        ·
          refine ⟨117716597801940432667630709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78477731867960288445087139 117716597801940432667630709)
          ·
            refine ⟨11035931043931915562590379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117716597801940432667630709 11035931043931915562590379)
            ·
              refine ⟨16553896565897873343885569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035931043931915562590379 16553896565897873343885569)
              ·
                refine ⟨12415422424423405007914177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16553896565897873343885569 12415422424423405007914177)
                ·
                  refine ⟨9311566818317553755935633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12415422424423405007914177 9311566818317553755935633)
                  ·
                    refine ⟨6983675113738165316951725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9311566818317553755935633 6983675113738165316951725)
                    ·
                      refine ⟨2618878167651811993856897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983675113738165316951725 2618878167651811993856897)
                      ·
                        rfl

theorem cell23_5100247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_5100247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100247 prefixEnd_5100247 := by exact prefixLift 5100247
  have htrace : WordTrace (prefixWord ++ tailWord_5100247) baseStart_5100247 baseEnd_5100247 := by
    simpa [prefixWord, tailWord_5100247, baseEnd_5100247] using wordTrace_append hprefix tailTrace_5100247
  have hstable : (prefixWord ++ tailWord_5100247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100247).length < 2 ^ (prefixWord ++ tailWord_5100247).sum := by decide
  have hdescent : baseEnd_5100247 < baseStart_5100247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100250 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_5100250 : Nat := 118140960795 + 5100250 * 2 ^ 59
def prefixEnd_5100250 : Nat := 4983230072969 + 3 ^ 40 * 5100250 * 2
def baseEnd_5100250 : Nat := 290986634232641720235487

theorem tailTrace_5100250 : CollatzResearch.WordTrace tailWord_5100250 prefixEnd_5100250 290986634232641720235487 := by
  unfold tailWord_5100250
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505349943168194549252551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124014266515115185464673469 46505349943168194549252551)
  ·
    refine ⟨69758024914752291823878827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46505349943168194549252551 69758024914752291823878827)
    ·
      refine ⟨104637037372128437735818241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69758024914752291823878827 104637037372128437735818241)
      ·
        refine ⟨78477778029096328301863681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104637037372128437735818241 78477778029096328301863681)
        ·
          refine ⟨58858333521822246226397761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78477778029096328301863681 58858333521822246226397761)
          ·
            refine ⟨44143750141366684669798321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58858333521822246226397761 44143750141366684669798321)
            ·
              refine ⟨33107812606025013502348741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44143750141366684669798321 33107812606025013502348741)
              ·
                refine ⟨6207714863629690031690389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33107812606025013502348741 6207714863629690031690389)
                ·
                  refine ⟨290986634232641720235487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6207714863629690031690389 290986634232641720235487)
                  ·
                    rfl

theorem cell23_5100250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_5100250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100250 prefixEnd_5100250 := by exact prefixLift 5100250
  have htrace : WordTrace (prefixWord ++ tailWord_5100250) baseStart_5100250 baseEnd_5100250 := by
    simpa [prefixWord, tailWord_5100250, baseEnd_5100250] using wordTrace_append hprefix tailTrace_5100250
  have hstable : (prefixWord ++ tailWord_5100250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100250).length < 2 ^ (prefixWord ++ tailWord_5100250).sum := by decide
  have hdescent : baseEnd_5100250 < baseStart_5100250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100280 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_5100280 : Nat := 118140960795 + 5100280 * 2 ^ 59
def prefixEnd_5100280 : Nat := 4983230072969 + 3 ^ 40 * 5100280 * 2
def baseEnd_5100280 : Nat := 872965037504470121581415

theorem tailTrace_5100280 : CollatzResearch.WordTrace tailWord_5100280 prefixEnd_5100280 872965037504470121581415 := by
  unfold tailWord_5100280
  simp only [CollatzResearch.WordTrace]
  refine ⟨93011246981282046660301147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124014995975042728880401529 93011246981282046660301147)
  ·
    refine ⟨139516870471923069990451721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93011246981282046660301147 139516870471923069990451721)
    ·
      refine ⟨104637652853942302492838791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139516870471923069990451721 104637652853942302492838791)
      ·
        refine ⟨156956479280913453739258187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104637652853942302492838791 156956479280913453739258187)
        ·
          refine ⟨235434718921370180608887281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156956479280913453739258187 235434718921370180608887281)
          ·
            refine ⟨176576039191027635456665461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235434718921370180608887281 176576039191027635456665461)
            ·
              refine ⟨16554003674158840824062387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176576039191027635456665461 16554003674158840824062387)
              ·
                refine ⟨24831005511238261236093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16554003674158840824062387 24831005511238261236093581)
                ·
                  refine ⟨9311627066714347963535093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24831005511238261236093581 9311627066714347963535093)
                  ·
                    refine ⟨872965037504470121581415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9311627066714347963535093 872965037504470121581415)
                    ·
                      rfl

theorem cell23_5100280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_5100280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100280 prefixEnd_5100280 := by exact prefixLift 5100280
  have htrace : WordTrace (prefixWord ++ tailWord_5100280) baseStart_5100280 baseEnd_5100280 := by
    simpa [prefixWord, tailWord_5100280, baseEnd_5100280] using wordTrace_append hprefix tailTrace_5100280
  have hstable : (prefixWord ++ tailWord_5100280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100280).length < 2 ^ (prefixWord ++ tailWord_5100280).sum := by decide
  have hdescent : baseEnd_5100280 < baseStart_5100280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100334 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5100334 : Nat := 118140960795 + 5100334 * 2 ^ 59
def prefixEnd_5100334 : Nat := 4983230072969 + 3 ^ 40 * 5100334 * 2
def baseEnd_5100334 : Nat := 2618922840468753153468997

theorem tailTrace_5100334 : CollatzResearch.WordTrace tailWord_5100334 prefixEnd_5100334 2618922840468753153468997 := by
  unfold tailWord_5100334
  simp only [CollatzResearch.WordTrace]
  refine ⟨23253057938046057567883507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124016309002912307028712037 23253057938046057567883507)
  ·
    refine ⟨34879586907069086351825261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23253057938046057567883507 34879586907069086351825261)
    ·
      refine ⟨13079845090150907381934473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34879586907069086351825261 13079845090150907381934473)
      ·
        refine ⟨9809883817613180536450855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13079845090150907381934473 9809883817613180536450855)
        ·
          refine ⟨14714825726419770804676283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809883817613180536450855 14714825726419770804676283)
          ·
            refine ⟨22072238589629656207014425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14714825726419770804676283 22072238589629656207014425)
            ·
              refine ⟨16554178942222242155260819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22072238589629656207014425 16554178942222242155260819)
              ·
                refine ⟨24831268413333363232891229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16554178942222242155260819 24831268413333363232891229)
                ·
                  refine ⟨9311725655000011212334211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24831268413333363232891229 9311725655000011212334211)
                  ·
                    refine ⟨13967588482500016818501317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9311725655000011212334211 13967588482500016818501317)
                    ·
                      refine ⟨2618922840468753153468997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13967588482500016818501317 2618922840468753153468997)
                      ·
                        rfl

theorem cell23_5100334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5100334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100334 prefixEnd_5100334 := by exact prefixLift 5100334
  have htrace : WordTrace (prefixWord ++ tailWord_5100334) baseStart_5100334 baseEnd_5100334 := by
    simpa [prefixWord, tailWord_5100334, baseEnd_5100334] using wordTrace_append hprefix tailTrace_5100334
  have hstable : (prefixWord ++ tailWord_5100334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100334).length < 2 ^ (prefixWord ++ tailWord_5100334).sum := by decide
  have hdescent : baseEnd_5100334 < baseStart_5100334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100337 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5100337 : Nat := 118140960795 + 5100337 * 2 ^ 59
def prefixEnd_5100337 : Nat := 4983230072969 + 3 ^ 40 * 5100337 * 2
def baseEnd_5100337 : Nat := 2618924380910716641731483

theorem tailTrace_5100337 : CollatzResearch.WordTrace tailWord_5100337 prefixEnd_5100337 2618924380910716641731483 := by
  unfold tailWord_5100337
  simp only [CollatzResearch.WordTrace]
  refine ⟨186024572923357592055427265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124016381948905061370284843 186024572923357592055427265)
  ·
    refine ⟨139518429692518194041570449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186024572923357592055427265 139518429692518194041570449)
    ·
      refine ⟨104638822269388645531177837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139518429692518194041570449 104638822269388645531177837)
      ·
        refine ⟨39239558351020742074191689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104638822269388645531177837 39239558351020742074191689)
        ·
          refine ⟨29429668763265556555643767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39239558351020742074191689 29429668763265556555643767)
          ·
            refine ⟨44144503144898334833465651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29429668763265556555643767 44144503144898334833465651)
            ·
              refine ⟨66216754717347502250198477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44144503144898334833465651 66216754717347502250198477)
              ·
                refine ⟨24831283019005313343824429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66216754717347502250198477 24831283019005313343824429)
                ·
                  refine ⟨9311731132126992503934161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24831283019005313343824429 9311731132126992503934161)
                  ·
                    refine ⟨6983798349095244377950621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9311731132126992503934161 6983798349095244377950621)
                    ·
                      refine ⟨2618924380910716641731483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6983798349095244377950621 2618924380910716641731483)
                      ·
                        rfl

theorem cell23_5100337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5100337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100337 prefixEnd_5100337 := by exact prefixLift 5100337
  have htrace : WordTrace (prefixWord ++ tailWord_5100337) baseStart_5100337 baseEnd_5100337 := by
    simpa [prefixWord, tailWord_5100337, baseEnd_5100337] using wordTrace_append hprefix tailTrace_5100337
  have hstable : (prefixWord ++ tailWord_5100337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100337).length < 2 ^ (prefixWord ++ tailWord_5100337).sum := by decide
  have hdescent : baseEnd_5100337 < baseStart_5100337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100351 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 1, 1, 4]
def baseStart_5100351 : Nat := 118140960795 + 5100351 * 2 ^ 59
def prefixEnd_5100351 : Nat := 4983230072969 + 3 ^ 40 * 5100351 * 2
def baseEnd_5100351 : Nat := 2618931569639879586956419

theorem tailTrace_5100351 : CollatzResearch.WordTrace tailWord_5100351 prefixEnd_5100351 2618931569639879586956419 := by
  unfold tailWord_5100351
  simp only [CollatzResearch.WordTrace]
  refine ⟨186025083545306872446436907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124016722363537914964291271 186025083545306872446436907)
  ·
    refine ⟨279037625317960308669655361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186025083545306872446436907 279037625317960308669655361)
    ·
      refine ⟨209278218988470231502241521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279037625317960308669655361 209278218988470231502241521)
      ·
        refine ⟨156958664241352673626681141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209278218988470231502241521 156958664241352673626681141)
        ·
          refine ⟨14714874772626813152501357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156958664241352673626681141 14714874772626813152501357)
          ·
            refine ⟨5518078039735054932188009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14714874772626813152501357 5518078039735054932188009)
            ·
              refine ⟨4138558529801291199141007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518078039735054932188009 4138558529801291199141007)
              ·
                refine ⟨6207837794701936798711511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138558529801291199141007 6207837794701936798711511)
                ·
                  refine ⟨9311756692052905198067267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6207837794701936798711511 9311756692052905198067267)
                  ·
                    refine ⟨13967635038079357797100901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9311756692052905198067267 13967635038079357797100901)
                    ·
                      refine ⟨2618931569639879586956419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13967635038079357797100901 2618931569639879586956419)
                      ·
                        rfl

theorem cell23_5100351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_5100351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100351 prefixEnd_5100351 := by exact prefixLift 5100351
  have htrace : WordTrace (prefixWord ++ tailWord_5100351) baseStart_5100351 baseEnd_5100351 := by
    simpa [prefixWord, tailWord_5100351, baseEnd_5100351] using wordTrace_append hprefix tailTrace_5100351
  have hstable : (prefixWord ++ tailWord_5100351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100351).length < 2 ^ (prefixWord ++ tailWord_5100351).sum := by decide
  have hdescent : baseEnd_5100351 < baseStart_5100351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100400 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_5100400 : Nat := 118140960795 + 5100400 * 2 ^ 59
def prefixEnd_5100400 : Nat := 4983230072969 + 3 ^ 40 * 5100400 * 2
def baseEnd_5100400 : Nat := 872985576730649965081231

theorem tailTrace_5100400 : CollatzResearch.WordTrace tailWord_5100400 prefixEnd_5100400 872985576730649965081231 := by
  unfold tailWord_5100400
  simp only [CollatzResearch.WordTrace]
  refine ⟨93013435361064676907485327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124017913814752902543313769 93013435361064676907485327)
  ·
    refine ⟨139520153041597015361227991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93013435361064676907485327 139520153041597015361227991)
    ·
      refine ⟨209280229562395523041841987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139520153041597015361227991 209280229562395523041841987)
      ·
        refine ⟨313920344343593284562762981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209280229562395523041841987 313920344343593284562762981)
        ·
          refine ⟨58860064564423740855518059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313920344343593284562762981 58860064564423740855518059)
          ·
            refine ⟨88290096846635611283277089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58860064564423740855518059 88290096846635611283277089)
            ·
              refine ⟨66217572634976708462457817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88290096846635611283277089 66217572634976708462457817)
              ·
                refine ⟨49663179476232531346843363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66217572634976708462457817 49663179476232531346843363)
                ·
                  refine ⟨74494769214348797020265045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49663179476232531346843363 74494769214348797020265045)
                  ·
                    refine ⟨872985576730649965081231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74494769214348797020265045 872985576730649965081231)
                    ·
                      rfl

theorem cell23_5100400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_5100400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100400 prefixEnd_5100400 := by exact prefixLift 5100400
  have htrace : WordTrace (prefixWord ++ tailWord_5100400) baseStart_5100400 baseEnd_5100400 := by
    simpa [prefixWord, tailWord_5100400, baseEnd_5100400] using wordTrace_append hprefix tailTrace_5100400
  have hstable : (prefixWord ++ tailWord_5100400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100400).length < 2 ^ (prefixWord ++ tailWord_5100400).sum := by decide
  have hdescent : baseEnd_5100400 < baseStart_5100400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100487 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_5100487 : Nat := 118140960795 + 5100487 * 2 ^ 59
def prefixEnd_5100487 : Nat := 4983230072969 + 3 ^ 40 * 5100487 * 2
def baseEnd_5100487 : Nat := 2619001403008891054855793

theorem tailTrace_5100487 : CollatzResearch.WordTrace tailWord_5100487 prefixEnd_5100487 2619001403008891054855793 := by
  unfold tailWord_5100487
  simp only [CollatzResearch.WordTrace]
  refine ⟨186030043872814167673387715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124020029248542778448925143 186030043872814167673387715)
  ·
    refine ⟨279045065809221251510081573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186030043872814167673387715 279045065809221251510081573)
    ·
      refine ⟨52320949839228984658140295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279045065809221251510081573 52320949839228984658140295)
      ·
        refine ⟨78481424758843476987210443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52320949839228984658140295 78481424758843476987210443)
        ·
          refine ⟨117722137138265215480815665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78481424758843476987210443 117722137138265215480815665)
          ·
            refine ⟨88291602853698911610611749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117722137138265215480815665 88291602853698911610611749)
            ·
              refine ⟨16554675535068545926989703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88291602853698911610611749 16554675535068545926989703)
              ·
                refine ⟨24832013302602818890484555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16554675535068545926989703 24832013302602818890484555)
                ·
                  refine ⟨37248019953904228335726833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24832013302602818890484555 37248019953904228335726833)
                  ·
                    refine ⟨27936014965428171251795125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37248019953904228335726833 27936014965428171251795125)
                    ·
                      refine ⟨2619001403008891054855793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27936014965428171251795125 2619001403008891054855793)
                      ·
                        rfl

theorem cell23_5100487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_5100487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100487 prefixEnd_5100487 := by exact prefixLift 5100487
  have htrace : WordTrace (prefixWord ++ tailWord_5100487) baseStart_5100487 baseEnd_5100487 := by
    simpa [prefixWord, tailWord_5100487, baseEnd_5100487] using wordTrace_append hprefix tailTrace_5100487
  have hstable : (prefixWord ++ tailWord_5100487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100487).length < 2 ^ (prefixWord ++ tailWord_5100487).sum := by decide
  have hdescent : baseEnd_5100487 < baseStart_5100487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100497 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_5100497 : Nat := 118140960795 + 5100497 * 2 ^ 59
def prefixEnd_5100497 : Nat := 4983230072969 + 3 ^ 40 * 5100497 * 2
def baseEnd_5100497 : Nat := 2619006537815436015730747

theorem tailTrace_5100497 : CollatzResearch.WordTrace tailWord_5100497 prefixEnd_5100497 2619006537815436015730747 := by
  unfold tailWord_5100497
  simp only [CollatzResearch.WordTrace]
  refine ⟨186030408602777939381251745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124020272401851959587501163 186030408602777939381251745)
  ·
    refine ⟨139522806452083454535938809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186030408602777939381251745 139522806452083454535938809)
    ·
      refine ⟨104642104839062590901954107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139522806452083454535938809 104642104839062590901954107)
      ·
        refine ⟨156963157258593886352931161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104642104839062590901954107 156963157258593886352931161)
        ·
          refine ⟨117722367943945414764698371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156963157258593886352931161 117722367943945414764698371)
          ·
            refine ⟨176583551915918122147047557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117722367943945414764698371 176583551915918122147047557)
            ·
              refine ⟨33109415984234647902571417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176583551915918122147047557 33109415984234647902571417)
              ·
                refine ⟨24832061988175985926928563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33109415984234647902571417 24832061988175985926928563)
                ·
                  refine ⟨37248092982263978890392845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24832061988175985926928563 37248092982263978890392845)
                  ·
                    refine ⟨13968034868348992083897317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37248092982263978890392845 13968034868348992083897317)
                    ·
                      refine ⟨2619006537815436015730747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13968034868348992083897317 2619006537815436015730747)
                      ·
                        rfl

theorem cell23_5100497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_5100497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100497 prefixEnd_5100497 := by exact prefixLift 5100497
  have htrace : WordTrace (prefixWord ++ tailWord_5100497) baseStart_5100497 baseEnd_5100497 := by
    simpa [prefixWord, tailWord_5100497, baseEnd_5100497] using wordTrace_append hprefix tailTrace_5100497
  have hstable : (prefixWord ++ tailWord_5100497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100497).length < 2 ^ (prefixWord ++ tailWord_5100497).sum := by decide
  have hdescent : baseEnd_5100497 < baseStart_5100497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100511 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 2, 5]
def baseStart_5100511 : Nat := 118140960795 + 5100511 * 2 ^ 59
def prefixEnd_5100511 : Nat := 4983230072969 + 3 ^ 40 * 5100511 * 2
def baseEnd_5100511 : Nat := 873004575514866320318561

theorem tailTrace_5100511 : CollatzResearch.WordTrace tailWord_5100511 prefixEnd_5100511 873004575514866320318561 := by
  unfold tailWord_5100511
  simp only [CollatzResearch.WordTrace]
  refine ⟨186030919224727219772261387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124020612816484813181507591 186030919224727219772261387)
  ·
    refine ⟨279046378837090829658392081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186030919224727219772261387 279046378837090829658392081)
    ·
      refine ⟨209284784127818122243794061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279046378837090829658392081 209284784127818122243794061)
      ·
        refine ⟨78481794047931795841422773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209284784127818122243794061 78481794047931795841422773)
        ·
          refine ⟨7357668191993605860133385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78481794047931795841422773 7357668191993605860133385)
          ·
            refine ⟨5518251143995204395100039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7357668191993605860133385 5518251143995204395100039)
            ·
              refine ⟨8277376715992806592650059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518251143995204395100039 8277376715992806592650059)
              ·
                refine ⟨12416065073989209888975089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8277376715992806592650059 12416065073989209888975089)
                ·
                  refine ⟨9312048805491907416731317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12416065073989209888975089 9312048805491907416731317)
                  ·
                    refine ⟨873004575514866320318561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9312048805491907416731317 873004575514866320318561)
                    ·
                      rfl

theorem cell23_5100511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_5100511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100511 prefixEnd_5100511 := by exact prefixLift 5100511
  have htrace : WordTrace (prefixWord ++ tailWord_5100511) baseStart_5100511 baseEnd_5100511 := by
    simpa [prefixWord, tailWord_5100511, baseEnd_5100511] using wordTrace_append hprefix tailTrace_5100511
  have hstable : (prefixWord ++ tailWord_5100511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100511).length < 2 ^ (prefixWord ++ tailWord_5100511).sum := by decide
  have hdescent : baseEnd_5100511 < baseStart_5100511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100527 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_5100527 : Nat := 118140960795 + 5100527 * 2 ^ 59
def prefixEnd_5100527 : Nat := 4983230072969 + 3 ^ 40 * 5100527 * 2
def baseEnd_5100527 : Nat := 2619021942235070898355609

theorem tailTrace_5100527 : CollatzResearch.WordTrace tailWord_5100527 prefixEnd_5100527 2619021942235070898355609 := by
  unfold tailWord_5100527
  simp only [CollatzResearch.WordTrace]
  refine ⟨186031502792669254504843835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124021001861779503003229223 186031502792669254504843835)
  ·
    refine ⟨279047254189003881757265753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186031502792669254504843835 279047254189003881757265753)
    ·
      refine ⟨209285440641752911317949315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279047254189003881757265753 209285440641752911317949315)
      ·
        refine ⟨313928160962629366976923973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209285440641752911317949315 313928160962629366976923973)
        ·
          refine ⟨58861530180493006308173245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313928160962629366976923973 58861530180493006308173245)
          ·
            refine ⟨22073073817684877365564967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58861530180493006308173245 22073073817684877365564967)
            ·
              refine ⟨33109610726527316048347451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22073073817684877365564967 33109610726527316048347451)
              ·
                refine ⟨49664416089790974072521177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33109610726527316048347451 49664416089790974072521177)
                ·
                  refine ⟨37248312067343230554390883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49664416089790974072521177 37248312067343230554390883)
                  ·
                    refine ⟨55872468101014845831586325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37248312067343230554390883 55872468101014845831586325)
                    ·
                      refine ⟨2619021942235070898355609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55872468101014845831586325 2619021942235070898355609)
                      ·
                        rfl

theorem cell23_5100527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_5100527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100527 prefixEnd_5100527 := by exact prefixLift 5100527
  have htrace : WordTrace (prefixWord ++ tailWord_5100527) baseStart_5100527 baseEnd_5100527 := by
    simpa [prefixWord, tailWord_5100527, baseEnd_5100527] using wordTrace_append hprefix tailTrace_5100527
  have hstable : (prefixWord ++ tailWord_5100527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100527).length < 2 ^ (prefixWord ++ tailWord_5100527).sum := by decide
  have hdescent : baseEnd_5100527 < baseStart_5100527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100537 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 8]
def baseStart_5100537 : Nat := 118140960795 + 5100537 * 2 ^ 59
def prefixEnd_5100537 : Nat := 4983230072969 + 3 ^ 40 * 5100537 * 2
def baseEnd_5100537 : Nat := 291003008560179539914507

theorem tailTrace_5100537 : CollatzResearch.WordTrace tailWord_5100537 prefixEnd_5100537 291003008560179539914507 := by
  unfold tailWord_5100537
  simp only [CollatzResearch.WordTrace]
  refine ⟨186031867522633026212707865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124021245015088684141805243 186031867522633026212707865)
  ·
    refine ⟨139523900641974769659530899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186031867522633026212707865 139523900641974769659530899)
    ·
      refine ⟨209285850962962154489296349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139523900641974769659530899 209285850962962154489296349)
      ·
        refine ⟨78482194111110807933486131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209285850962962154489296349 78482194111110807933486131)
        ·
          refine ⟨117723291166666211900229197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78482194111110807933486131 117723291166666211900229197)
          ·
            refine ⟨44146234187499829462585949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117723291166666211900229197 44146234187499829462585949)
            ·
              refine ⟨16554837820312436048469731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44146234187499829462585949 16554837820312436048469731)
              ·
                refine ⟨24832256730468654072704597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16554837820312436048469731 24832256730468654072704597)
                ·
                  refine ⟨291003008560179539914507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24832256730468654072704597 291003008560179539914507)
                  ·
                    rfl

theorem cell23_5100537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_5100537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100537 prefixEnd_5100537 := by exact prefixLift 5100537
  have htrace : WordTrace (prefixWord ++ tailWord_5100537) baseStart_5100537 baseEnd_5100537 := by
    simpa [prefixWord, tailWord_5100537, baseEnd_5100537] using wordTrace_append hprefix tailTrace_5100537
  have hstable : (prefixWord ++ tailWord_5100537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100537).length < 2 ^ (prefixWord ++ tailWord_5100537).sum := by decide
  have hdescent : baseEnd_5100537 < baseStart_5100537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100641 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_5100641 : Nat := 118140960795 + 5100641 * 2 ^ 59
def prefixEnd_5100641 : Nat := 4983230072969 + 3 ^ 40 * 5100641 * 2
def baseEnd_5100641 : Nat := 2619080479029683452330085

theorem tailTrace_5100641 : CollatzResearch.WordTrace tailWord_5100641 prefixEnd_5100641 2619080479029683452330085 := by
  unfold tailWord_5100641
  simp only [CollatzResearch.WordTrace]
  refine ⟨186035660714256251974493777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124023773809504167982995851 186035660714256251974493777)
  ·
    refine ⟨139526745535692188980870333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186035660714256251974493777 139526745535692188980870333)
    ·
      refine ⟨52322529575884570867826375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139526745535692188980870333 52322529575884570867826375)
      ·
        refine ⟨78483794363826856301739563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52322529575884570867826375 78483794363826856301739563)
        ·
          refine ⟨117725691545740284452609345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78483794363826856301739563 117725691545740284452609345)
          ·
            refine ⟨88294268659305213339457009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117725691545740284452609345 88294268659305213339457009)
            ·
              refine ⟨66220701494478910004592757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88294268659305213339457009 66220701494478910004592757)
              ·
                refine ⟨6208190765107397812930571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66220701494478910004592757 6208190765107397812930571)
                ·
                  refine ⟨9312286147661096719395857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6208190765107397812930571 9312286147661096719395857)
                  ·
                    refine ⟨6984214610745822539546893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9312286147661096719395857 6984214610745822539546893)
                    ·
                      refine ⟨2619080479029683452330085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6984214610745822539546893 2619080479029683452330085)
                      ·
                        rfl

theorem cell23_5100641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_5100641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100641 prefixEnd_5100641 := by exact prefixLift 5100641
  have htrace : WordTrace (prefixWord ++ tailWord_5100641) baseStart_5100641 baseEnd_5100641 := by
    simpa [prefixWord, tailWord_5100641, baseEnd_5100641] using wordTrace_append hprefix tailTrace_5100641
  have hstable : (prefixWord ++ tailWord_5100641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100641).length < 2 ^ (prefixWord ++ tailWord_5100641).sum := by decide
  have hdescent : baseEnd_5100641 < baseStart_5100641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100655 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 1, 2, 2]
def baseStart_5100655 : Nat := 118140960795 + 5100655 * 2 ^ 59
def prefixEnd_5100655 : Nat := 4983230072969 + 3 ^ 40 * 5100655 * 2
def baseEnd_5100655 : Nat := 2619087667758846397555021

theorem tailTrace_5100655 : CollatzResearch.WordTrace tailWord_5100655 prefixEnd_5100655 2619087667758846397555021 := by
  unfold tailWord_5100655
  simp only [CollatzResearch.WordTrace]
  refine ⟨186036171336205532365503419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124024114224137021577002279 186036171336205532365503419)
  ·
    refine ⟨279054257004308298548255129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186036171336205532365503419 279054257004308298548255129)
    ·
      refine ⟨209290692753231223911191347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279054257004308298548255129 209290692753231223911191347)
      ·
        refine ⟨313936039129846835866787021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209290692753231223911191347 313936039129846835866787021)
        ·
          refine ⟨117726014673692563450045133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313936039129846835866787021 117726014673692563450045133)
          ·
            refine ⟨44147255502634711293766925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117726014673692563450045133 44147255502634711293766925)
            ·
              refine ⟨16555220813488016735162597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44147255502634711293766925 16555220813488016735162597)
              ·
                refine ⟨3104103902529003137842987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16555220813488016735162597 3104103902529003137842987)
                ·
                  refine ⟨4656155853793504706764481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104103902529003137842987 4656155853793504706764481)
                  ·
                    refine ⟨3492116890345128530073361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656155853793504706764481 3492116890345128530073361)
                    ·
                      refine ⟨2619087667758846397555021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492116890345128530073361 2619087667758846397555021)
                      ·
                        rfl

theorem cell23_5100655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 2, 2].length) (baseStart_5100655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100655 prefixEnd_5100655 := by exact prefixLift 5100655
  have htrace : WordTrace (prefixWord ++ tailWord_5100655) baseStart_5100655 baseEnd_5100655 := by
    simpa [prefixWord, tailWord_5100655, baseEnd_5100655] using wordTrace_append hprefix tailTrace_5100655
  have hstable : (prefixWord ++ tailWord_5100655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100655).length < 2 ^ (prefixWord ++ tailWord_5100655).sum := by decide
  have hdescent : baseEnd_5100655 < baseStart_5100655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100704 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 6]
def baseStart_5100704 : Nat := 118140960795 + 5100704 * 2 ^ 59
def prefixEnd_5100704 : Nat := 4983230072969 + 3 ^ 40 * 5100704 * 2
def baseEnd_5100704 : Nat := 873037609436972235280765

theorem tailTrace_5100704 : CollatzResearch.WordTrace tailWord_5100704 prefixEnd_5100704 873037609436972235280765 := by
  unfold tailWord_5100704
  simp only [CollatzResearch.WordTrace]
  refine ⟨93018979256514006867018583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124025305675352009156024777 93018979256514006867018583)
  ·
    refine ⟨139528468884771010300527875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93018979256514006867018583 139528468884771010300527875)
    ·
      refine ⟨209292703327156515450791813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139528468884771010300527875 209292703327156515450791813)
      ·
        refine ⟨39242381873841846647023465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209292703327156515450791813 39242381873841846647023465)
        ·
          refine ⟨29431786405381384985267599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39242381873841846647023465 29431786405381384985267599)
          ·
            refine ⟨44147679608072077477901399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29431786405381384985267599 44147679608072077477901399)
            ·
              refine ⟨66221519412108116216852099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44147679608072077477901399 66221519412108116216852099)
              ·
                refine ⟨99332279118162174325278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66221519412108116216852099 99332279118162174325278149)
                ·
                  refine ⟨18624802334655407685989653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99332279118162174325278149 18624802334655407685989653)
                  ·
                    refine ⟨873037609436972235280765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18624802334655407685989653 873037609436972235280765)
                    ·
                      rfl

theorem cell23_5100704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_5100704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100704 prefixEnd_5100704 := by exact prefixLift 5100704
  have htrace : WordTrace (prefixWord ++ tailWord_5100704) baseStart_5100704 baseEnd_5100704 := by
    simpa [prefixWord, tailWord_5100704, baseEnd_5100704] using wordTrace_append hprefix tailTrace_5100704
  have hstable : (prefixWord ++ tailWord_5100704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100704).length < 2 ^ (prefixWord ++ tailWord_5100704).sum := by decide
  have hdescent : baseEnd_5100704 < baseStart_5100704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100721 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_5100721 : Nat := 118140960795 + 5100721 * 2 ^ 59
def prefixEnd_5100721 : Nat := 4983230072969 + 3 ^ 40 * 5100721 * 2
def baseEnd_5100721 : Nat := 873040519160681046443239

theorem tailTrace_5100721 : CollatzResearch.WordTrace tailWord_5100721 prefixEnd_5100721 873040519160681046443239 := by
  unfold tailWord_5100721
  simp only [CollatzResearch.WordTrace]
  refine ⟨186038578553966425637406017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124025719035977617091604011 186038578553966425637406017)
  ·
    refine ⟨139528933915474819228054513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186038578553966425637406017 139528933915474819228054513)
    ·
      refine ⟨104646700436606114421040885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139528933915474819228054513 104646700436606114421040885)
      ·
        refine ⟨9810628165931823226972583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104646700436606114421040885 9810628165931823226972583)
        ·
          refine ⟨14715942248897734840458875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9810628165931823226972583 14715942248897734840458875)
          ·
            refine ⟨22073913373346602260688313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14715942248897734840458875 22073913373346602260688313)
            ·
              refine ⟨16555435030009951695516235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22073913373346602260688313 16555435030009951695516235)
              ·
                refine ⟨24833152545014927543274353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16555435030009951695516235 24833152545014927543274353)
                ·
                  refine ⟨18624864408761195657455765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24833152545014927543274353 18624864408761195657455765)
                  ·
                    refine ⟨873040519160681046443239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18624864408761195657455765 873040519160681046443239)
                    ·
                      rfl

theorem cell23_5100721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_5100721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100721 prefixEnd_5100721 := by exact prefixLift 5100721
  have htrace : WordTrace (prefixWord ++ tailWord_5100721) baseStart_5100721 baseEnd_5100721 := by
    simpa [prefixWord, tailWord_5100721, baseEnd_5100721] using wordTrace_append hprefix tailTrace_5100721
  have hstable : (prefixWord ++ tailWord_5100721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100721).length < 2 ^ (prefixWord ++ tailWord_5100721).sum := by decide
  have hdescent : baseEnd_5100721 < baseStart_5100721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100751 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 5]
def baseStart_5100751 : Nat := 118140960795 + 5100751 * 2 ^ 59
def prefixEnd_5100751 : Nat := 4983230072969 + 3 ^ 40 * 5100751 * 2
def baseEnd_5100751 : Nat := 291015217989075335772731

theorem tailTrace_5100751 : CollatzResearch.WordTrace tailWord_5100751 prefixEnd_5100751 291015217989075335772731 := by
  unfold tailWord_5100751
  simp only [CollatzResearch.WordTrace]
  refine ⟨186039672743857740760998107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124026448495905160507332071 186039672743857740760998107)
  ·
    refine ⟨279059509115786611141497161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186039672743857740760998107 279059509115786611141497161)
    ·
      refine ⟨209294631836839958356122871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279059509115786611141497161 209294631836839958356122871)
      ·
        refine ⟨313941947755259937534184307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209294631836839958356122871 313941947755259937534184307)
        ·
          refine ⟨470912921632889906301276461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313941947755259937534184307 470912921632889906301276461)
          ·
            refine ⟨176592345612333714862978673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470912921632889906301276461 176592345612333714862978673)
            ·
              refine ⟨132444259209250286147234005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176592345612333714862978673 132444259209250286147234005)
              ·
                refine ⟨3104162325216803581575797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132444259209250286147234005 3104162325216803581575797)
                ·
                  refine ⟨291015217989075335772731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104162325216803581575797 291015217989075335772731)
                  ·
                    rfl

theorem cell23_5100751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 5].length) (baseStart_5100751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100751 prefixEnd_5100751 := by exact prefixLift 5100751
  have htrace : WordTrace (prefixWord ++ tailWord_5100751) baseStart_5100751 baseEnd_5100751 := by
    simpa [prefixWord, tailWord_5100751, baseEnd_5100751] using wordTrace_append hprefix tailTrace_5100751
  have hstable : (prefixWord ++ tailWord_5100751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100751).length < 2 ^ (prefixWord ++ tailWord_5100751).sum := by decide
  have hdescent : baseEnd_5100751 < baseStart_5100751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100798 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_5100798 : Nat := 118140960795 + 5100798 * 2 ^ 59
def prefixEnd_5100798 : Nat := 4983230072969 + 3 ^ 40 * 5100798 * 2
def baseEnd_5100798 : Nat := 873053698497479779355621

theorem tailTrace_5100798 : CollatzResearch.WordTrace tailWord_5100798 prefixEnd_5100798 873053698497479779355621 := by
  unfold tailWord_5100798
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255173371835933473494881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124027591316458311858639365 23255173371835933473494881)
  ·
    refine ⟨17441380028876950105121161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23255173371835933473494881 17441380028876950105121161)
    ·
      refine ⟨13081035021657712578840871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17441380028876950105121161 13081035021657712578840871)
      ·
        refine ⟨19621552532486568868261307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13081035021657712578840871 19621552532486568868261307)
        ·
          refine ⟨29432328798729853302391961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19621552532486568868261307 29432328798729853302391961)
          ·
            refine ⟨22074246599047389976793971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29432328798729853302391961 22074246599047389976793971)
            ·
              refine ⟨33111369898571084965190957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074246599047389976793971 33111369898571084965190957)
              ·
                refine ⟨12416763711964156861946609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33111369898571084965190957 12416763711964156861946609)
                ·
                  refine ⟨9312572783973117646459957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12416763711964156861946609 9312572783973117646459957)
                  ·
                    refine ⟨873053698497479779355621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9312572783973117646459957 873053698497479779355621)
                    ·
                      rfl

theorem cell23_5100798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_5100798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100798 prefixEnd_5100798 := by exact prefixLift 5100798
  have htrace : WordTrace (prefixWord ++ tailWord_5100798) baseStart_5100798 baseEnd_5100798 := by
    simpa [prefixWord, tailWord_5100798, baseEnd_5100798] using wordTrace_append hprefix tailTrace_5100798
  have hstable : (prefixWord ++ tailWord_5100798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100798).length < 2 ^ (prefixWord ++ tailWord_5100798).sum := by decide
  have hdescent : baseEnd_5100798 < baseStart_5100798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100821 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_5100821 : Nat := 118140960795 + 5100821 * 2 ^ 59
def prefixEnd_5100821 : Nat := 4983230072969 + 3 ^ 40 * 5100821 * 2
def baseEnd_5100821 : Nat := 2619172905547492748079257

theorem tailTrace_5100821 : CollatzResearch.WordTrace tailWord_5100821 prefixEnd_5100821 2619172905547492748079257 := by
  unfold tailWord_5100821
  simp only [CollatzResearch.WordTrace]
  refine ⟨186042225853604142716046317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124028150569069428477364211 186042225853604142716046317)
  ·
    refine ⟨69765834695101553518517369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186042225853604142716046317 69765834695101553518517369)
    ·
      refine ⟨52324376021326165138888027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69765834695101553518517369 52324376021326165138888027)
      ·
        refine ⟨78486564031989247708332041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52324376021326165138888027 78486564031989247708332041)
        ·
          refine ⟨58864923023991935781249031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78486564031989247708332041 58864923023991935781249031)
          ·
            refine ⟨88297384535987903671873547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58864923023991935781249031 88297384535987903671873547)
            ·
              refine ⟨132446076803981855507810321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88297384535987903671873547 132446076803981855507810321)
              ·
                refine ⟨99334557602986391630857741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132446076803981855507810321 99334557602986391630857741)
                ·
                  refine ⟨37250459101119896861571653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99334557602986391630857741 37250459101119896861571653)
                  ·
                    refine ⟨6984461081459980661544685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37250459101119896861571653 6984461081459980661544685)
                    ·
                      refine ⟨2619172905547492748079257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6984461081459980661544685 2619172905547492748079257)
                      ·
                        rfl

theorem cell23_5100821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_5100821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100821 prefixEnd_5100821 := by exact prefixLift 5100821
  have htrace : WordTrace (prefixWord ++ tailWord_5100821) baseStart_5100821 baseEnd_5100821 := by
    simpa [prefixWord, tailWord_5100821, baseEnd_5100821] using wordTrace_append hprefix tailTrace_5100821
  have hstable : (prefixWord ++ tailWord_5100821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100821).length < 2 ^ (prefixWord ++ tailWord_5100821).sum := by decide
  have hdescent : baseEnd_5100821 < baseStart_5100821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100845 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5100845 : Nat := 118140960795 + 5100845 * 2 ^ 59
def prefixEnd_5100845 : Nat := 4983230072969 + 3 ^ 40 * 5100845 * 2
def baseEnd_5100845 : Nat := 873061743027733551393049

theorem tailTrace_5100845 : CollatzResearch.WordTrace tailWord_5100845 prefixEnd_5100845 873061743027733551393049 := by
  unfold tailWord_5100845
  simp only [CollatzResearch.WordTrace]
  refine ⟨186043101205517194814919989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124028734137011463209946659 186043101205517194814919989)
  ·
    refine ⟨17441540738017237013898749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186043101205517194814919989 17441540738017237013898749)
    ·
      refine ⟨6540577776756463880212031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17441540738017237013898749 6540577776756463880212031)
      ·
        refine ⟨9810866665134695820318047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540577776756463880212031 9810866665134695820318047)
        ·
          refine ⟨14716299997702043730477071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9810866665134695820318047 14716299997702043730477071)
          ·
            refine ⟨22074449996553065595715607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14716299997702043730477071 22074449996553065595715607)
            ·
              refine ⟨33111674994829598393573411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074449996553065595715607 33111674994829598393573411)
              ·
                refine ⟨49667512492244397590360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33111674994829598393573411 49667512492244397590360117)
                ·
                  refine ⟨4656329296147912274096261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49667512492244397590360117 4656329296147912274096261)
                  ·
                    refine ⟨873061743027733551393049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656329296147912274096261 873061743027733551393049)
                    ·
                      rfl

theorem cell23_5100845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5100845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100845 prefixEnd_5100845 := by exact prefixLift 5100845
  have htrace : WordTrace (prefixWord ++ tailWord_5100845) baseStart_5100845 baseEnd_5100845 := by
    simpa [prefixWord, tailWord_5100845, baseEnd_5100845] using wordTrace_append hprefix tailTrace_5100845
  have hstable : (prefixWord ++ tailWord_5100845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100845).length < 2 ^ (prefixWord ++ tailWord_5100845).sum := by decide
  have hdescent : baseEnd_5100845 < baseStart_5100845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100862 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_5100862 : Nat := 118140960795 + 5100862 * 2 ^ 59
def prefixEnd_5100862 : Nat := 4983230072969 + 3 ^ 40 * 5100862 * 2
def baseEnd_5100862 : Nat := 873064652751442362555523

theorem tailTrace_5100862 : CollatzResearch.WordTrace tailWord_5100862 prefixEnd_5100862 873064652751442362555523 := by
  unfold tailWord_5100862
  simp only [CollatzResearch.WordTrace]
  refine ⟨23255465155806950839786105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124029147497637071145525893 23255465155806950839786105)
  ·
    refine ⟨17441598866855213129839579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23255465155806950839786105 17441598866855213129839579)
    ·
      refine ⟨26162398300282819694759369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17441598866855213129839579 26162398300282819694759369)
      ·
        refine ⟨19621798725212114771069527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26162398300282819694759369 19621798725212114771069527)
        ·
          refine ⟨29432698087818172156604291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19621798725212114771069527 29432698087818172156604291)
          ·
            refine ⟨44149047131727258234906437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29432698087818172156604291 44149047131727258234906437)
            ·
              refine ⟨8277946337198860919044957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44149047131727258234906437 8277946337198860919044957)
              ·
                refine ⟨3104229876449572844641859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8277946337198860919044957 3104229876449572844641859)
                ·
                  refine ⟨4656344814674359266962789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104229876449572844641859 4656344814674359266962789)
                  ·
                    refine ⟨873064652751442362555523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656344814674359266962789 873064652751442362555523)
                    ·
                      rfl

theorem cell23_5100862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_5100862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100862 prefixEnd_5100862 := by exact prefixLift 5100862
  have htrace : WordTrace (prefixWord ++ tailWord_5100862) baseStart_5100862 baseEnd_5100862 := by
    simpa [prefixWord, tailWord_5100862, baseEnd_5100862] using wordTrace_append hprefix tailTrace_5100862
  have hstable : (prefixWord ++ tailWord_5100862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100862).length < 2 ^ (prefixWord ++ tailWord_5100862).sum := by decide
  have hdescent : baseEnd_5100862 < baseStart_5100862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100885 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5100885 : Nat := 118140960795 + 5100885 * 2 ^ 59
def prefixEnd_5100885 : Nat := 4983230072969 + 3 ^ 40 * 5100885 * 2
def baseEnd_5100885 : Nat := 2619205768309380497678963

theorem tailTrace_5100885 : CollatzResearch.WordTrace tailWord_5100885 prefixEnd_5100885 2619205768309380497678963 := by
  unfold tailWord_5100885
  simp only [CollatzResearch.WordTrace]
  refine ⟨186044560125372281646376109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124029706750248187764250739 186044560125372281646376109)
  ·
    refine ⟨69766710047014605617391041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186044560125372281646376109 69766710047014605617391041)
    ·
      refine ⟨52325032535260954213043281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69766710047014605617391041 52325032535260954213043281)
      ·
        refine ⟨39243774401445715659782461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52325032535260954213043281 39243774401445715659782461)
        ·
          refine ⟨14716415400542143372418423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39243774401445715659782461 14716415400542143372418423)
          ·
            refine ⟨22074623100813215058627635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14716415400542143372418423 22074623100813215058627635)
            ·
              refine ⟨33111934651219822587941453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074623100813215058627635 33111934651219822587941453)
              ·
                refine ⟨12416975494207433470478045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33111934651219822587941453 12416975494207433470478045)
                ·
                  refine ⟨4656365810327787551429267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12416975494207433470478045 4656365810327787551429267)
                  ·
                    refine ⟨6984548715491681327143901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4656365810327787551429267 6984548715491681327143901)
                    ·
                      refine ⟨2619205768309380497678963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6984548715491681327143901 2619205768309380497678963)
                      ·
                        rfl

theorem cell23_5100885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5100885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100885 prefixEnd_5100885 := by exact prefixLift 5100885
  have htrace : WordTrace (prefixWord ++ tailWord_5100885) baseStart_5100885 baseEnd_5100885 := by
    simpa [prefixWord, tailWord_5100885, baseEnd_5100885] using wordTrace_append hprefix tailTrace_5100885
  have hstable : (prefixWord ++ tailWord_5100885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100885).length < 2 ^ (prefixWord ++ tailWord_5100885).sum := by decide
  have hdescent : baseEnd_5100885 < baseStart_5100885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100911 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_5100911 : Nat := 118140960795 + 5100911 * 2 ^ 59
def prefixEnd_5100911 : Nat := 4983230072969 + 3 ^ 40 * 5100911 * 2
def baseEnd_5100911 : Nat := 2619219118806397395953843

theorem tailTrace_5100911 : CollatzResearch.WordTrace tailWord_5100911 prefixEnd_5100911 2619219118806397395953843 := by
  unfold tailWord_5100911
  simp only [CollatzResearch.WordTrace]
  refine ⟨186045508423278088086822587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124030338948852058724548391 186045508423278088086822587)
  ·
    refine ⟨279068262634917132130233881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186045508423278088086822587 279068262634917132130233881)
    ·
      refine ⟨209301196976187849097675411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279068262634917132130233881 209301196976187849097675411)
      ·
        refine ⟨313951795464281773646513117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209301196976187849097675411 313951795464281773646513117)
        ·
          refine ⟨117731923299105665117442419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313951795464281773646513117 117731923299105665117442419)
          ·
            refine ⟨176597884948658497676163629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117731923299105665117442419 176597884948658497676163629)
            ·
              refine ⟨66224206855746936628561361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176597884948658497676163629 66224206855746936628561361)
              ·
                refine ⟨49668155141810202471421021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66224206855746936628561361 49668155141810202471421021)
                ·
                  refine ⟨18625558178178825926782883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49668155141810202471421021 18625558178178825926782883)
                  ·
                    refine ⟨27938337267268238890174325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18625558178178825926782883 27938337267268238890174325)
                    ·
                      refine ⟨2619219118806397395953843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27938337267268238890174325 2619219118806397395953843)
                      ·
                        rfl

theorem cell23_5100911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_5100911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100911 prefixEnd_5100911 := by exact prefixLift 5100911
  have htrace : WordTrace (prefixWord ++ tailWord_5100911) baseStart_5100911 baseEnd_5100911 := by
    simpa [prefixWord, tailWord_5100911, baseEnd_5100911] using wordTrace_append hprefix tailTrace_5100911
  have hstable : (prefixWord ++ tailWord_5100911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100911).length < 2 ^ (prefixWord ++ tailWord_5100911).sum := by decide
  have hdescent : baseEnd_5100911 < baseStart_5100911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100931 : List Nat := [1, 1, 1, 3, 5, 1, 11]
def baseStart_5100931 : Nat := 118140960795 + 5100931 * 2 ^ 59
def prefixEnd_5100931 : Nat := 4983230072969 + 3 ^ 40 * 5100931 * 2
def baseEnd_5100931 : Nat := 32336165289129473058071

theorem tailTrace_5100931 : CollatzResearch.WordTrace tailWord_5100931 prefixEnd_5100931 32336165289129473058071 := by
  unfold tailWord_5100931
  simp only [CollatzResearch.WordTrace]
  refine ⟨186046237883205631502550647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124030825255470421001700431 186046237883205631502550647)
  ·
    refine ⟨279069356824808447253825971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186046237883205631502550647 279069356824808447253825971)
    ·
      refine ⟨418604035237212670880738957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279069356824808447253825971 418604035237212670880738957)
      ·
        refine ⟨156976513213954751580277109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418604035237212670880738957 156976513213954751580277109)
        ·
          refine ⟨14716548113808257960650979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156976513213954751580277109 14716548113808257960650979)
          ·
            refine ⟨22074822170712386940976469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14716548113808257960650979 22074822170712386940976469)
            ·
              refine ⟨32336165289129473058071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22074822170712386940976469 32336165289129473058071)
              ·
                rfl

theorem cell23_5100931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 11].length) (baseStart_5100931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100931 prefixEnd_5100931 := by exact prefixLift 5100931
  have htrace : WordTrace (prefixWord ++ tailWord_5100931) baseStart_5100931 baseEnd_5100931 := by
    simpa [prefixWord, tailWord_5100931, baseEnd_5100931] using wordTrace_append hprefix tailTrace_5100931
  have hstable : (prefixWord ++ tailWord_5100931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100931).length < 2 ^ (prefixWord ++ tailWord_5100931).sum := by decide
  have hdescent : baseEnd_5100931 < baseStart_5100931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100948 : List Nat := [2, 4, 2, 1, 2, 1, 1, 10]
def baseStart_5100948 : Nat := 118140960795 + 5100948 * 2 ^ 59
def prefixEnd_5100948 : Nat := 4983230072969 + 3 ^ 40 * 5100948 * 2
def baseEnd_5100948 : Nat := 97008819170022731525599

theorem tailTrace_5100948 : CollatzResearch.WordTrace tailWord_5100948 prefixEnd_5100948 97008819170022731525599 := by
  unfold tailWord_5100948
  simp only [CollatzResearch.WordTrace]
  refine ⟨93023428962072021702959749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124031238616096028937279665 93023428962072021702959749)
  ·
    refine ⟨17441892930388504069304953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93023428962072021702959749 17441892930388504069304953)
    ·
      refine ⟨13081419697791378051978715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17441892930388504069304953 13081419697791378051978715)
      ·
        refine ⟨19622129546687067077968073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13081419697791378051978715 19622129546687067077968073)
        ·
          refine ⟨14716597160015300308476055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19622129546687067077968073 14716597160015300308476055)
          ·
            refine ⟨22074895740022950462714083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14716597160015300308476055 22074895740022950462714083)
            ·
              refine ⟨33112343610034425694071125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22074895740022950462714083 33112343610034425694071125)
              ·
                refine ⟨97008819170022731525599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33112343610034425694071125 97008819170022731525599)
                ·
                  rfl

theorem cell23_5100948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 10].length) (baseStart_5100948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100948 prefixEnd_5100948 := by exact prefixLift 5100948
  have htrace : WordTrace (prefixWord ++ tailWord_5100948) baseStart_5100948 baseEnd_5100948 := by
    simpa [prefixWord, tailWord_5100948, baseEnd_5100948] using wordTrace_append hprefix tailTrace_5100948
  have hstable : (prefixWord ++ tailWord_5100948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100948).length < 2 ^ (prefixWord ++ tailWord_5100948).sum := by decide
  have hdescent : baseEnd_5100948 < baseStart_5100948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5100951 : Nat := 118140960795 + 5100951 * 2 ^ 59
def prefixEnd_5100951 : Nat := 4983230072969 + 3 ^ 40 * 5100951 * 2
def baseEnd_5100951 : Nat := 2619239658032577239453659

theorem tailTrace_5100951 : CollatzResearch.WordTrace tailWord_5100951 prefixEnd_5100951 2619239658032577239453659 := by
  unfold tailWord_5100951
  simp only [CollatzResearch.WordTrace]
  refine ⟨186046967343133174918278707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124031311562088783278852471 186046967343133174918278707)
  ·
    refine ⟨279070451014699762377418061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186046967343133174918278707 279070451014699762377418061)
    ·
      refine ⟨104651419130512410891531773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279070451014699762377418061 104651419130512410891531773)
      ·
        refine ⟨39244282173942154084324415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104651419130512410891531773 39244282173942154084324415)
        ·
          refine ⟨58866423260913231126486623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39244282173942154084324415 58866423260913231126486623)
          ·
            refine ⟨88299634891369846689729935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58866423260913231126486623 88299634891369846689729935)
            ·
              refine ⟨132449452337054770034594903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88299634891369846689729935 132449452337054770034594903)
              ·
                refine ⟨198674178505582155051892355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132449452337054770034594903 198674178505582155051892355)
                ·
                  refine ⟨298011267758373232577838533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198674178505582155051892355 298011267758373232577838533)
                  ·
                    refine ⟨55877112704694981108344725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298011267758373232577838533 55877112704694981108344725)
                    ·
                      refine ⟨2619239658032577239453659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55877112704694981108344725 2619239658032577239453659)
                      ·
                        rfl

theorem cell23_5100951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5100951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100951 prefixEnd_5100951 := by exact prefixLift 5100951
  have htrace : WordTrace (prefixWord ++ tailWord_5100951) baseStart_5100951 baseEnd_5100951 := by
    simpa [prefixWord, tailWord_5100951, baseEnd_5100951] using wordTrace_append hprefix tailTrace_5100951
  have hstable : (prefixWord ++ tailWord_5100951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100951).length < 2 ^ (prefixWord ++ tailWord_5100951).sum := by decide
  have hdescent : baseEnd_5100951 < baseStart_5100951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100952 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_5100952 : Nat := 118140960795 + 5100952 * 2 ^ 59
def prefixEnd_5100952 : Nat := 4983230072969 + 3 ^ 40 * 5100952 * 2
def baseEnd_5100952 : Nat := 873080057171077245180385

theorem tailTrace_5100952 : CollatzResearch.WordTrace tailWord_5100952 prefixEnd_5100952 873080057171077245180385 := by
  unfold tailWord_5100952
  simp only [CollatzResearch.WordTrace]
  refine ⟨93023501908064776044532555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124031335877419701392710073 93023501908064776044532555)
  ·
    refine ⟨139535252862097164066798833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93023501908064776044532555 139535252862097164066798833)
    ·
      refine ⟨104651439646572873050099125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139535252862097164066798833 104651439646572873050099125)
      ·
        refine ⟨9811072466866206848446793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104651439646572873050099125 9811072466866206848446793)
        ·
          refine ⟨7358304350149655136335095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9811072466866206848446793 7358304350149655136335095)
          ·
            refine ⟨11037456525224482704502643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358304350149655136335095 11037456525224482704502643)
            ·
              refine ⟨16556184787836724056753965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037456525224482704502643 16556184787836724056753965)
              ·
                refine ⟨6208569295438771521282737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16556184787836724056753965 6208569295438771521282737)
                ·
                  refine ⟨4656426971579078640962053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6208569295438771521282737 4656426971579078640962053)
                  ·
                    refine ⟨873080057171077245180385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656426971579078640962053 873080057171077245180385)
                    ·
                      rfl

theorem cell23_5100952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_5100952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100952 prefixEnd_5100952 := by exact prefixLift 5100952
  have htrace : WordTrace (prefixWord ++ tailWord_5100952) baseStart_5100952 baseEnd_5100952 := by
    simpa [prefixWord, tailWord_5100952, baseEnd_5100952] using wordTrace_append hprefix tailTrace_5100952
  have hstable : (prefixWord ++ tailWord_5100952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100952).length < 2 ^ (prefixWord ++ tailWord_5100952).sum := by decide
  have hdescent : baseEnd_5100952 < baseStart_5100952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100962 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_5100962 : Nat := 118140960795 + 5100962 * 2 ^ 59
def prefixEnd_5100962 : Nat := 4983230072969 + 3 ^ 40 * 5100962 * 2
def baseEnd_5100962 : Nat := 2619245306319776696416109

theorem tailTrace_5100962 : CollatzResearch.WordTrace tailWord_5100962 prefixEnd_5100962 2619245306319776696416109 := by
  unfold tailWord_5100962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46511842136523330949232285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124031579030728882531286093 46511842136523330949232285)
  ·
    refine ⟨17441940801196249105962107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46511842136523330949232285 17441940801196249105962107)
    ·
      refine ⟨26162911201794373658943161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17441940801196249105962107 26162911201794373658943161)
      ·
        refine ⟨19622183401345780244207371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26162911201794373658943161 19622183401345780244207371)
        ·
          refine ⟨29433275102018670366311057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19622183401345780244207371 29433275102018670366311057)
          ·
            refine ⟨22074956326514002774733293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29433275102018670366311057 22074956326514002774733293)
            ·
              refine ⟨8278108622442751040524985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22074956326514002774733293 8278108622442751040524985)
              ·
                refine ⟨6208581466832063280393739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8278108622442751040524985 6208581466832063280393739)
                ·
                  refine ⟨9312872200248094920590609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6208581466832063280393739 9312872200248094920590609)
                  ·
                    refine ⟨6984654150186071190442957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9312872200248094920590609 6984654150186071190442957)
                    ·
                      refine ⟨2619245306319776696416109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6984654150186071190442957 2619245306319776696416109)
                      ·
                        rfl

theorem cell23_5100962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_5100962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100962 prefixEnd_5100962 := by exact prefixLift 5100962
  have htrace : WordTrace (prefixWord ++ tailWord_5100962) baseStart_5100962 baseEnd_5100962 := by
    simpa [prefixWord, tailWord_5100962, baseEnd_5100962] using wordTrace_append hprefix tailTrace_5100962
  have hstable : (prefixWord ++ tailWord_5100962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100962).length < 2 ^ (prefixWord ++ tailWord_5100962).sum := by decide
  have hdescent : baseEnd_5100962 < baseStart_5100962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100971 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_5100971 : Nat := 118140960795 + 5100971 * 2 ^ 59
def prefixEnd_5100971 : Nat := 4983230072969 + 3 ^ 40 * 5100971 * 2
def baseEnd_5100971 : Nat := 2619249927645667161203567

theorem tailTrace_5100971 : CollatzResearch.WordTrace tailWord_5100971 prefixEnd_5100971 2619249927645667161203567 := by
  unfold tailWord_5100971
  simp only [CollatzResearch.WordTrace]
  refine ⟨186047696803060718334006767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124031797868707145556004511 186047696803060718334006767)
  ·
    refine ⟨279071545204591077501010151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186047696803060718334006767 279071545204591077501010151)
    ·
      refine ⟨418607317806886616251515227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279071545204591077501010151 418607317806886616251515227)
      ·
        refine ⟨627910976710329924377272841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418607317806886616251515227 627910976710329924377272841)
        ·
          refine ⟨470933232532747443282954631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627910976710329924377272841 470933232532747443282954631)
          ·
            refine ⟨706399848799121164924431947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470933232532747443282954631 706399848799121164924431947)
            ·
              refine ⟨1059599773198681747386647921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706399848799121164924431947 1059599773198681747386647921)
              ·
                refine ⟨794699829899011310539985941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1059599773198681747386647921 794699829899011310539985941)
                ·
                  refine ⟨37251554526516155181561841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 794699829899011310539985941 37251554526516155181561841)
                  ·
                    refine ⟨27938665894887116386171381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37251554526516155181561841 27938665894887116386171381)
                    ·
                      refine ⟨2619249927645667161203567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27938665894887116386171381 2619249927645667161203567)
                      ·
                        rfl

theorem cell23_5100971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_5100971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100971 prefixEnd_5100971 := by exact prefixLift 5100971
  have htrace : WordTrace (prefixWord ++ tailWord_5100971) baseStart_5100971 baseEnd_5100971 := by
    simpa [prefixWord, tailWord_5100971, baseEnd_5100971] using wordTrace_append hprefix tailTrace_5100971
  have hstable : (prefixWord ++ tailWord_5100971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100971).length < 2 ^ (prefixWord ++ tailWord_5100971).sum := by decide
  have hdescent : baseEnd_5100971 < baseStart_5100971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5100991 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 8]
def baseStart_5100991 : Nat := 118140960795 + 5100991 * 2 ^ 59
def prefixEnd_5100991 : Nat := 4983230072969 + 3 ^ 40 * 5100991 * 2
def baseEnd_5100991 : Nat := 873086732419585694317825

theorem tailTrace_5100991 : CollatzResearch.WordTrace tailWord_5100991 prefixEnd_5100991 873086732419585694317825 := by
  unfold tailWord_5100991
  simp only [CollatzResearch.WordTrace]
  refine ⟨186048426262988261749734827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124032284175325507833156551 186048426262988261749734827)
  ·
    refine ⟨279072639394482392624602241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186048426262988261749734827 279072639394482392624602241)
    ·
      refine ⟨209304479545861794468451681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279072639394482392624602241 209304479545861794468451681)
      ·
        refine ⟨156978359659396345851338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209304479545861794468451681 156978359659396345851338761)
        ·
          refine ⟨117733769744547259388504071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156978359659396345851338761 117733769744547259388504071)
          ·
            refine ⟨176600654616820889082756107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117733769744547259388504071 176600654616820889082756107)
            ·
              refine ⟨264900981925231333624134161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176600654616820889082756107 264900981925231333624134161)
              ·
                refine ⟨198675736443923500218100621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264900981925231333624134161 198675736443923500218100621)
                ·
                  refine ⟨74503401166471312581787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198675736443923500218100621 74503401166471312581787733)
                  ·
                    refine ⟨873086732419585694317825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74503401166471312581787733 873086732419585694317825)
                    ·
                      rfl

theorem cell23_5100991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_5100991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5100991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5100991 prefixEnd_5100991 := by exact prefixLift 5100991
  have htrace : WordTrace (prefixWord ++ tailWord_5100991) baseStart_5100991 baseEnd_5100991 := by
    simpa [prefixWord, tailWord_5100991, baseEnd_5100991] using wordTrace_append hprefix tailTrace_5100991
  have hstable : (prefixWord ++ tailWord_5100991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5100991).length < 2 ^ (prefixWord ++ tailWord_5100991).sum := by decide
  have hdescent : baseEnd_5100991 < baseStart_5100991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5100991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101032 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_5101032 : Nat := 118140960795 + 5101032 * 2 ^ 59
def prefixEnd_5101032 : Nat := 4983230072969 + 3 ^ 40 * 5101032 * 2
def baseEnd_5101032 : Nat := 2619281249965591422540787

theorem tailTrace_5101032 : CollatzResearch.WordTrace tailWord_5101032 prefixEnd_5101032 2619281249965591422540787 := by
  unfold tailWord_5101032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93024960827919862875988675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124033281103893150501318233 93024960827919862875988675)
  ·
    refine ⟨139537441241879794313983013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93024960827919862875988675 139537441241879794313983013)
    ·
      refine ⟨26163270232852461433871815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139537441241879794313983013 26163270232852461433871815)
      ·
        refine ⟨39244905349278692150807723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26163270232852461433871815 39244905349278692150807723)
        ·
          refine ⟨58867358023918038226211585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39244905349278692150807723 58867358023918038226211585)
          ·
            refine ⟨44150518517938528669658689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58867358023918038226211585 44150518517938528669658689)
            ·
              refine ⟨33112888888453896502244017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44150518517938528669658689 33112888888453896502244017)
              ·
                refine ⟨24834666666340422376683013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33112888888453896502244017 24834666666340422376683013)
                ·
                  refine ⟨4656499999938829195628065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24834666666340422376683013 4656499999938829195628065)
                  ·
                    refine ⟨3492374999954121896721049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656499999938829195628065 3492374999954121896721049)
                    ·
                      refine ⟨2619281249965591422540787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492374999954121896721049 2619281249965591422540787)
                      ·
                        rfl

theorem cell23_5101032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_5101032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101032 prefixEnd_5101032 := by exact prefixLift 5101032
  have htrace : WordTrace (prefixWord ++ tailWord_5101032) baseStart_5101032 baseEnd_5101032 := by
    simpa [prefixWord, tailWord_5101032, baseEnd_5101032] using wordTrace_append hprefix tailTrace_5101032
  have hstable : (prefixWord ++ tailWord_5101032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101032).length < 2 ^ (prefixWord ++ tailWord_5101032).sum := by decide
  have hdescent : baseEnd_5101032 < baseStart_5101032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101038 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_5101038 : Nat := 118140960795 + 5101038 * 2 ^ 59
def prefixEnd_5101038 : Nat := 4983230072969 + 3 ^ 40 * 5101038 * 2
def baseEnd_5101038 : Nat := 291031592316613155451751

theorem tailTrace_5101038 : CollatzResearch.WordTrace tailWord_5101038 prefixEnd_5101038 291031592316613155451751 := by
  unfold tailWord_5101038
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256267561727248597086971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124033426995878659184463845 23256267561727248597086971)
  ·
    refine ⟨34884401342590872895630457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256267561727248597086971 34884401342590872895630457)
    ·
      refine ⟨26163301006943154671722843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34884401342590872895630457 26163301006943154671722843)
      ·
        refine ⟨39244951510414732007584265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26163301006943154671722843 39244951510414732007584265)
        ·
          refine ⟨29433713632811049005688199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39244951510414732007584265 29433713632811049005688199)
          ·
            refine ⟨44150570449216573508532299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29433713632811049005688199 44150570449216573508532299)
            ·
              refine ⟨66225855673824860262798449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44150570449216573508532299 66225855673824860262798449)
              ·
                refine ⟨49669391755368645197098837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66225855673824860262798449 49669391755368645197098837)
                ·
                  refine ⟨291031592316613155451751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49669391755368645197098837 291031592316613155451751)
                  ·
                    rfl

theorem cell23_5101038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_5101038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101038 prefixEnd_5101038 := by exact prefixLift 5101038
  have htrace : WordTrace (prefixWord ++ tailWord_5101038) baseStart_5101038 baseEnd_5101038 := by
    simpa [prefixWord, tailWord_5101038, baseEnd_5101038] using wordTrace_append hprefix tailTrace_5101038
  have hstable : (prefixWord ++ tailWord_5101038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101038).length < 2 ^ (prefixWord ++ tailWord_5101038).sum := by decide
  have hdescent : baseEnd_5101038 < baseStart_5101038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101066 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_5101066 : Nat := 118140960795 + 5101066 * 2 ^ 59
def prefixEnd_5101066 : Nat := 4983230072969 + 3 ^ 40 * 5101066 * 2
def baseEnd_5101066 : Nat := 2619298708307844289515631

theorem tailTrace_5101066 : CollatzResearch.WordTrace tailWord_5101066 prefixEnd_5101066 2619298708307844289515631 := by
  unfold tailWord_5101066
  simp only [CollatzResearch.WordTrace]
  refine ⟨46512790434429137389678763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124034107825144366372476701 46512790434429137389678763)
  ·
    refine ⟨69769185651643706084518145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46512790434429137389678763 69769185651643706084518145)
    ·
      refine ⟨52326889238732779563388609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69769185651643706084518145 52326889238732779563388609)
      ·
        refine ⟨39245166929049584672541457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52326889238732779563388609 39245166929049584672541457)
        ·
          refine ⟨29433875196787188504406093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39245166929049584672541457 29433875196787188504406093)
          ·
            refine ⟨11037703198795195689152285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29433875196787188504406093 11037703198795195689152285)
            ·
              refine ⟨4139138699548198383432107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11037703198795195689152285 4139138699548198383432107)
              ·
                refine ⟨6208708049322297575148161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139138699548198383432107 6208708049322297575148161)
                ·
                  refine ⟨4656531036991723181361121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6208708049322297575148161 4656531036991723181361121)
                  ·
                    refine ⟨3492398277743792386020841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656531036991723181361121 3492398277743792386020841)
                    ·
                      refine ⟨2619298708307844289515631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492398277743792386020841 2619298708307844289515631)
                      ·
                        rfl

theorem cell23_5101066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_5101066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101066 prefixEnd_5101066 := by exact prefixLift 5101066
  have htrace : WordTrace (prefixWord ++ tailWord_5101066) baseStart_5101066 baseEnd_5101066 := by
    simpa [prefixWord, tailWord_5101066, baseEnd_5101066] using wordTrace_append hprefix tailTrace_5101066
  have hstable : (prefixWord ++ tailWord_5101066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101066).length < 2 ^ (prefixWord ++ tailWord_5101066).sum := by decide
  have hdescent : baseEnd_5101066 < baseStart_5101066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101085 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_5101085 : Nat := 118140960795 + 5101085 * 2 ^ 59
def prefixEnd_5101085 : Nat := 4983230072969 + 3 ^ 40 * 5101085 * 2
def baseEnd_5101085 : Nat := 873102821480093238392681

theorem tailTrace_5101085 : CollatzResearch.WordTrace tailWord_5101085 prefixEnd_5101085 873102821480093238392681 := by
  unfold tailWord_5101085
  simp only [CollatzResearch.WordTrace]
  refine ⟨186051854724647715803656709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124034569816431810535771139 186051854724647715803656709)
  ·
    refine ⟨34884722760871446713185633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186051854724647715803656709 34884722760871446713185633)
    ·
      refine ⟨26163542070653585034889225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34884722760871446713185633 26163542070653585034889225)
      ·
        refine ⟨19622656552990188776166919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163542070653585034889225 19622656552990188776166919)
        ·
          refine ⟨29433984829485283164250379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19622656552990188776166919 29433984829485283164250379)
          ·
            refine ⟨44150977244227924746375569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29433984829485283164250379 44150977244227924746375569)
            ·
              refine ⟨33113232933170943559781677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44150977244227924746375569 33113232933170943559781677)
              ·
                refine ⟨12417462349939103834918129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33113232933170943559781677 12417462349939103834918129)
                ·
                  refine ⟨9313096762454327876188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12417462349939103834918129 9313096762454327876188597)
                  ·
                    refine ⟨873102821480093238392681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9313096762454327876188597 873102821480093238392681)
                    ·
                      rfl

theorem cell23_5101085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_5101085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101085 prefixEnd_5101085 := by exact prefixLift 5101085
  have htrace : WordTrace (prefixWord ++ tailWord_5101085) baseStart_5101085 baseEnd_5101085 := by
    simpa [prefixWord, tailWord_5101085, baseEnd_5101085] using wordTrace_append hprefix tailTrace_5101085
  have hstable : (prefixWord ++ tailWord_5101085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101085).length < 2 ^ (prefixWord ++ tailWord_5101085).sum := by decide
  have hdescent : baseEnd_5101085 < baseStart_5101085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101086 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_5101086 : Nat := 118140960795 + 5101086 * 2 ^ 59
def prefixEnd_5101086 : Nat := 4983230072969 + 3 ^ 40 * 5101086 * 2
def baseEnd_5101086 : Nat := 2619308977920934211265539

theorem tailTrace_5101086 : CollatzResearch.WordTrace tailWord_5101086 prefixEnd_5101086 2619308977920934211265539 := by
  unfold tailWord_5101086
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256486399705511621805389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124034594131762728649628741 23256486399705511621805389)
  ·
    refine ⟨8721182399889566858177021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23256486399705511621805389 8721182399889566858177021)
    ·
      refine ⟨3270443399958587571816383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8721182399889566858177021 3270443399958587571816383)
      ·
        refine ⟨4905665099937881357724575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270443399958587571816383 4905665099937881357724575)
        ·
          refine ⟨7358497649906822036586863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905665099937881357724575 7358497649906822036586863)
          ·
            refine ⟨11037746474860233054880295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358497649906822036586863 11037746474860233054880295)
            ·
              refine ⟨16556619712290349582320443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037746474860233054880295 16556619712290349582320443)
              ·
                refine ⟨24834929568435524373480665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16556619712290349582320443 24834929568435524373480665)
                ·
                  refine ⟨18626197176326643280110499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24834929568435524373480665 18626197176326643280110499)
                  ·
                    refine ⟨27939295764489964920165749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18626197176326643280110499 27939295764489964920165749)
                    ·
                      refine ⟨2619308977920934211265539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27939295764489964920165749 2619308977920934211265539)
                      ·
                        rfl

theorem cell23_5101086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_5101086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101086 prefixEnd_5101086 := by exact prefixLift 5101086
  have htrace : WordTrace (prefixWord ++ tailWord_5101086) baseStart_5101086 baseEnd_5101086 := by
    simpa [prefixWord, tailWord_5101086, baseEnd_5101086] using wordTrace_append hprefix tailTrace_5101086
  have hstable : (prefixWord ++ tailWord_5101086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101086).length < 2 ^ (prefixWord ++ tailWord_5101086).sum := by decide
  have hdescent : baseEnd_5101086 < baseStart_5101086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101102 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5101102 : Nat := 118140960795 + 5101102 * 2 ^ 59
def prefixEnd_5101102 : Nat := 4983230072969 + 3 ^ 40 * 5101102 * 2
def baseEnd_5101102 : Nat := 873105731203802049555155

theorem tailTrace_5101102 : CollatzResearch.WordTrace tailWord_5101102 prefixEnd_5101102 873105731203802049555155 := by
  unfold tailWord_5101102
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256559345698265963378195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124034983177057418471350373 23256559345698265963378195)
  ·
    refine ⟨34884839018547398945067293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256559345698265963378195 34884839018547398945067293)
    ·
      refine ⟨13081814631955274604400235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34884839018547398945067293 13081814631955274604400235)
      ·
        refine ⟨19622721947932911906600353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13081814631955274604400235 19622721947932911906600353)
        ·
          refine ⟨14717041460949683929950265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19622721947932911906600353 14717041460949683929950265)
          ·
            refine ⟨11037781095712262947462699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14717041460949683929950265 11037781095712262947462699)
            ·
              refine ⟨16556671643568394421194049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037781095712262947462699 16556671643568394421194049)
              ·
                refine ⟨12417503732676295815895537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16556671643568394421194049 12417503732676295815895537)
                ·
                  refine ⟨9313127799507221861921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12417503732676295815895537 9313127799507221861921653)
                  ·
                    refine ⟨873105731203802049555155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9313127799507221861921653 873105731203802049555155)
                    ·
                      rfl

theorem cell23_5101102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5101102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101102 prefixEnd_5101102 := by exact prefixLift 5101102
  have htrace : WordTrace (prefixWord ++ tailWord_5101102) baseStart_5101102 baseEnd_5101102 := by
    simpa [prefixWord, tailWord_5101102, baseEnd_5101102] using wordTrace_append hprefix tailTrace_5101102
  have hstable : (prefixWord ++ tailWord_5101102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101102).length < 2 ^ (prefixWord ++ tailWord_5101102).sum := by decide
  have hdescent : baseEnd_5101102 < baseStart_5101102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101125 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_5101125 : Nat := 118140960795 + 5101125 * 2 ^ 59
def prefixEnd_5101125 : Nat := 4983230072969 + 3 ^ 40 * 5101125 * 2
def baseEnd_5101125 : Nat := 2619329003666459558677859

theorem tailTrace_5101125 : CollatzResearch.WordTrace tailWord_5101125 prefixEnd_5101125 2619329003666459558677859 := by
  unfold tailWord_5101125
  simp only [CollatzResearch.WordTrace]
  refine ⟨186053313644502802635112829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124035542429668535090075219 186053313644502802635112829)
  ·
    refine ⟨69769992616688550988167311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186053313644502802635112829 69769992616688550988167311)
    ·
      refine ⟨104654988925032826482250967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69769992616688550988167311 104654988925032826482250967)
      ·
        refine ⟨156982483387549239723376451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104654988925032826482250967 156982483387549239723376451)
        ·
          refine ⟨235473725081323859585064677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156982483387549239723376451 235473725081323859585064677)
          ·
            refine ⟨44151323452748223672199627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235473725081323859585064677 44151323452748223672199627)
            ·
              refine ⟨66226985179122335508299441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44151323452748223672199627 66226985179122335508299441)
              ·
                refine ⟨49670238884341751631224581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66226985179122335508299441 49670238884341751631224581)
                ·
                  refine ⟨9313169790814078430854609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49670238884341751631224581 9313169790814078430854609)
                  ·
                    refine ⟨6984877343110558823140957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9313169790814078430854609 6984877343110558823140957)
                    ·
                      refine ⟨2619329003666459558677859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6984877343110558823140957 2619329003666459558677859)
                      ·
                        rfl

theorem cell23_5101125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_5101125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101125 prefixEnd_5101125 := by exact prefixLift 5101125
  have htrace : WordTrace (prefixWord ++ tailWord_5101125) baseStart_5101125 baseEnd_5101125 := by
    simpa [prefixWord, tailWord_5101125, baseEnd_5101125] using wordTrace_append hprefix tailTrace_5101125
  have hstable : (prefixWord ++ tailWord_5101125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101125).length < 2 ^ (prefixWord ++ tailWord_5101125).sum := by decide
  have hdescent : baseEnd_5101125 < baseStart_5101125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101162 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_5101162 : Nat := 118140960795 + 5101162 * 2 ^ 59
def prefixEnd_5101162 : Nat := 4983230072969 + 3 ^ 40 * 5101162 * 2
def baseEnd_5101162 : Nat := 291038666938963990435021

theorem tailTrace_5101162 : CollatzResearch.WordTrace tailWord_5101162 prefixEnd_5101162 291038666938963990435021 := by
  unfold tailWord_5101162
  simp only [CollatzResearch.WordTrace]
  refine ⟨46513665786342189488552435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124036442096912505302806493 46513665786342189488552435)
  ·
    refine ⟨69770498679513284232828653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46513665786342189488552435 69770498679513284232828653)
    ·
      refine ⟨26163937004817481587310745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69770498679513284232828653 26163937004817481587310745)
      ·
        refine ⟨19622952753613111190483059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163937004817481587310745 19622952753613111190483059)
        ·
          refine ⟨29434429130419666785724589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19622952753613111190483059 29434429130419666785724589)
          ·
            refine ⟨11037910923907375044646721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29434429130419666785724589 11037910923907375044646721)
            ·
              refine ⟨8278433192930531283485041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11037910923907375044646721 8278433192930531283485041)
              ·
                refine ⟨6208824894697898462613781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8278433192930531283485041 6208824894697898462613781)
                ·
                  refine ⟨291038666938963990435021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6208824894697898462613781 291038666938963990435021)
                  ·
                    rfl

theorem cell23_5101162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_5101162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101162 prefixEnd_5101162 := by exact prefixLift 5101162
  have htrace : WordTrace (prefixWord ++ tailWord_5101162) baseStart_5101162 baseEnd_5101162 := by
    simpa [prefixWord, tailWord_5101162, baseEnd_5101162] using wordTrace_append hprefix tailTrace_5101162
  have hstable : (prefixWord ++ tailWord_5101162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101162).length < 2 ^ (prefixWord ++ tailWord_5101162).sum := by decide
  have hdescent : baseEnd_5101162 < baseStart_5101162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101166 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5101166 : Nat := 118140960795 + 5101166 * 2 ^ 59
def prefixEnd_5101166 : Nat := 4983230072969 + 3 ^ 40 * 5101166 * 2
def baseEnd_5101166 : Nat := 873116685457764632755057

theorem tailTrace_5101166 : CollatzResearch.WordTrace tailWord_5101166 prefixEnd_5101166 873116685457764632755057 := by
  unfold tailWord_5101166
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256851129669283329669419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124036539358236177758236901 23256851129669283329669419)
  ·
    refine ⟨34885276694503924994504129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256851129669283329669419 34885276694503924994504129)
    ·
      refine ⟨26163957520877943745878097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34885276694503924994504129 26163957520877943745878097)
      ·
        refine ⟨19622968140658457809408573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26163957520877943745878097 19622968140658457809408573)
        ·
          refine ⟨7358613052746921678528215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19622968140658457809408573 7358613052746921678528215)
          ·
            refine ⟨11037919579120382517792323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358613052746921678528215 11037919579120382517792323)
            ·
              refine ⟨16556879368680573776688485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037919579120382517792323 16556879368680573776688485)
              ·
                refine ⟨3104414881627607583129091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16556879368680573776688485 3104414881627607583129091)
                ·
                  refine ⟨4656622322441411374693637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104414881627607583129091 4656622322441411374693637)
                  ·
                    refine ⟨873116685457764632755057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656622322441411374693637 873116685457764632755057)
                    ·
                      rfl

theorem cell23_5101166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5101166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101166 prefixEnd_5101166 := by exact prefixLift 5101166
  have htrace : WordTrace (prefixWord ++ tailWord_5101166) baseStart_5101166 baseEnd_5101166 := by
    simpa [prefixWord, tailWord_5101166, baseEnd_5101166] using wordTrace_append hprefix tailTrace_5101166
  have hstable : (prefixWord ++ tailWord_5101166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101166).length < 2 ^ (prefixWord ++ tailWord_5101166).sum := by decide
  have hdescent : baseEnd_5101166 < baseStart_5101166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101195 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4]
def baseStart_5101195 : Nat := 118140960795 + 5101195 * 2 ^ 59
def prefixEnd_5101195 : Nat := 4983230072969 + 3 ^ 40 * 5101195 * 2
def baseEnd_5101195 : Nat := 2619364947312274284802537

theorem tailTrace_5101195 : CollatzResearch.WordTrace tailWord_5101195 prefixEnd_5101195 2619364947312274284802537 := by
  unfold tailWord_5101195
  simp only [CollatzResearch.WordTrace]
  refine ⟨186055866754249204590161039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124037244502832803060107359 186055866754249204590161039)
  ·
    refine ⟨279083800131373806885241559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186055866754249204590161039 279083800131373806885241559)
    ·
      refine ⟨418625700197060710327862339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279083800131373806885241559 418625700197060710327862339)
      ·
        refine ⟨627938550295591065491793509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418625700197060710327862339 627938550295591065491793509)
        ·
          refine ⟨117738478180423324779711283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 627938550295591065491793509 117738478180423324779711283)
          ·
            refine ⟨176607717270634987169566925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117738478180423324779711283 176607717270634987169566925)
            ·
              refine ⟨66227893976488120188587597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176607717270634987169566925 66227893976488120188587597)
              ·
                refine ⟨24835460241183045070720349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66227893976488120188587597 24835460241183045070720349)
                ·
                  refine ⟨9313297590443641901520131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24835460241183045070720349 9313297590443641901520131)
                  ·
                    refine ⟨13969946385665462852280197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9313297590443641901520131 13969946385665462852280197)
                    ·
                      refine ⟨2619364947312274284802537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13969946385665462852280197 2619364947312274284802537)
                      ·
                        rfl

theorem cell23_5101195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 4].length) (baseStart_5101195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101195 prefixEnd_5101195 := by exact prefixLift 5101195
  have htrace : WordTrace (prefixWord ++ tailWord_5101195) baseStart_5101195 baseEnd_5101195 := by
    simpa [prefixWord, tailWord_5101195, baseEnd_5101195] using wordTrace_append hprefix tailTrace_5101195
  have hstable : (prefixWord ++ tailWord_5101195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101195).length < 2 ^ (prefixWord ++ tailWord_5101195).sum := by decide
  have hdescent : baseEnd_5101195 < baseStart_5101195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101242 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_5101242 : Nat := 118140960795 + 5101242 * 2 ^ 59
def prefixEnd_5101242 : Nat := 4983230072969 + 3 ^ 40 * 5101242 * 2
def baseEnd_5101242 : Nat := 2619389080903035600914821

theorem tailTrace_5101242 : CollatzResearch.WordTrace tailWord_5101242 prefixEnd_5101242 2619389080903035600914821 := by
  unfold tailWord_5101242
  simp only [CollatzResearch.WordTrace]
  refine ⟨46514395246269732904280495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124038387323385954411414653 46514395246269732904280495)
  ·
    refine ⟨69771592869404599356420743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46514395246269732904280495 69771592869404599356420743)
    ·
      refine ⟨104657389304106899034631115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69771592869404599356420743 104657389304106899034631115)
      ·
        refine ⟨156986083956160348551946673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104657389304106899034631115 156986083956160348551946673)
        ·
          refine ⟨117739562967120261413960005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156986083956160348551946673 117739562967120261413960005)
          ·
            refine ⟨22076168056335049015117501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117739562967120261413960005 22076168056335049015117501)
            ·
              refine ⟨8278563021125643380669063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22076168056335049015117501 8278563021125643380669063)
              ·
                refine ⟨12417844531688465071003595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8278563021125643380669063 12417844531688465071003595)
                ·
                  refine ⟨18626766797532697606505393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12417844531688465071003595 18626766797532697606505393)
                  ·
                    refine ⟨13970075098149523204879045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18626766797532697606505393 13970075098149523204879045)
                    ·
                      refine ⟨2619389080903035600914821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13970075098149523204879045 2619389080903035600914821)
                      ·
                        rfl

theorem cell23_5101242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_5101242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101242 prefixEnd_5101242 := by exact prefixLift 5101242
  have htrace : WordTrace (prefixWord ++ tailWord_5101242) baseStart_5101242 baseEnd_5101242 := by
    simpa [prefixWord, tailWord_5101242, baseEnd_5101242] using wordTrace_append hprefix tailTrace_5101242
  have hstable : (prefixWord ++ tailWord_5101242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101242).length < 2 ^ (prefixWord ++ tailWord_5101242).sum := by decide
  have hdescent : baseEnd_5101242 < baseStart_5101242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
