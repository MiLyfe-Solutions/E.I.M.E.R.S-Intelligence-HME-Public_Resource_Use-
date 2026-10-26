import V185TrunkScan23Chunk0474

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2809030 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2809030 : Nat := 118140960795 + 2809030 * 2 ^ 59
def prefixEnd_2809030 : Nat := 4983230072969 + 3 ^ 40 * 2809030 * 2
def baseEnd_2809030 : Nat := 1442382562899249890906513

theorem tailTrace_2809030 : CollatzResearch.WordTrace tailWord_2809030 prefixEnd_2809030 1442382562899249890906513 := by
  unfold tailWord_2809030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201679406667860280460267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68302494008914352649819029 3201679406667860280460267)
  ·
    refine ⟨4802519110001790420690401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3201679406667860280460267 4802519110001790420690401)
    ·
      refine ⟨3601889332501342815517801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4802519110001790420690401 3601889332501342815517801)
      ·
        refine ⟨2701416999376007111638351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601889332501342815517801 2701416999376007111638351)
        ·
          refine ⟨4052125499064010667457527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701416999376007111638351 4052125499064010667457527)
          ·
            refine ⟨6078188248596016001186291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052125499064010667457527 6078188248596016001186291)
            ·
              refine ⟨9117282372894024001779437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078188248596016001186291 9117282372894024001779437)
              ·
                refine ⟨3418980889835259000667289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9117282372894024001779437 3418980889835259000667289)
                ·
                  refine ⟨2564235667376444250500467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418980889835259000667289 2564235667376444250500467)
                  ·
                    refine ⟨3846353501064666375750701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2564235667376444250500467 3846353501064666375750701)
                    ·
                      refine ⟨1442382562899249890906513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846353501064666375750701 1442382562899249890906513)
                      ·
                        rfl

theorem cell23_2809030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2809030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809030 prefixEnd_2809030 := by exact prefixLift 2809030
  have htrace : WordTrace (prefixWord ++ tailWord_2809030) baseStart_2809030 baseEnd_2809030 := by
    simpa [prefixWord, tailWord_2809030, baseEnd_2809030] using wordTrace_append hprefix tailTrace_2809030
  have hstable : (prefixWord ++ tailWord_2809030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809030).length < 2 ^ (prefixWord ++ tailWord_2809030).sum := by decide
  have hdescent : baseEnd_2809030 < baseStart_2809030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809055 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 2, 5]
def baseStart_2809055 : Nat := 118140960795 + 2809055 * 2 ^ 59
def prefixEnd_2809055 : Nat := 4983230072969 + 3 ^ 40 * 2809055 * 2
def baseEnd_2809055 : Nat := 480798466638537431031299

theorem tailTrace_2809055 : CollatzResearch.WordTrace tailWord_2809055 prefixEnd_2809055 480798466638537431031299 := by
  unfold tailWord_2809055
  simp only [CollatzResearch.WordTrace]
  refine ⟨102454652838280958244388619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68303101892187305496259079 102454652838280958244388619)
  ·
    refine ⟨153681979257421437366582929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102454652838280958244388619 153681979257421437366582929)
    ·
      refine ⟨115261484443066078024937197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153681979257421437366582929 115261484443066078024937197)
      ·
        refine ⟨43223056666149779259351449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115261484443066078024937197 43223056666149779259351449)
        ·
          refine ⟨32417292499612334444513587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43223056666149779259351449 32417292499612334444513587)
          ·
            refine ⟨48625938749418501666770381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32417292499612334444513587 48625938749418501666770381)
            ·
              refine ⟨18234727031031938125038893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48625938749418501666770381 18234727031031938125038893)
              ·
                refine ⟨6838022636636976796889585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18234727031031938125038893 6838022636636976796889585)
                ·
                  refine ⟨5128516977477732597667189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838022636636976796889585 5128516977477732597667189)
                  ·
                    refine ⟨480798466638537431031299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5128516977477732597667189 480798466638537431031299)
                    ·
                      rfl

theorem cell23_2809055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 5].length) (baseStart_2809055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809055 prefixEnd_2809055 := by exact prefixLift 2809055
  have htrace : WordTrace (prefixWord ++ tailWord_2809055) baseStart_2809055 baseEnd_2809055 := by
    simpa [prefixWord, tailWord_2809055, baseEnd_2809055] using wordTrace_append hprefix tailTrace_2809055
  have hstable : (prefixWord ++ tailWord_2809055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809055).length < 2 ^ (prefixWord ++ tailWord_2809055).sum := by decide
  have hdescent : baseEnd_2809055 < baseStart_2809055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809102 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_2809102 : Nat := 118140960795 + 2809102 * 2 ^ 59
def prefixEnd_2809102 : Nat := 4983230072969 + 3 ^ 40 * 2809102 * 2
def baseEnd_2809102 : Nat := 480806511168791203068727

theorem tailTrace_2809102 : CollatzResearch.WordTrace tailWord_2809102 prefixEnd_2809102 480806511168791203068727 := by
  unfold tailWord_2809102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807045883638835658918695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68304244712740456847566373 12807045883638835658918695)
  ·
    refine ⟨19210568825458253488378043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12807045883638835658918695 19210568825458253488378043)
    ·
      refine ⟨28815853238187380232567065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19210568825458253488378043 28815853238187380232567065)
      ·
        refine ⟨21611889928640535174425299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28815853238187380232567065 21611889928640535174425299)
        ·
          refine ⟨32417834892960802761637949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611889928640535174425299 32417834892960802761637949)
          ·
            refine ⟨12156688084860301035614231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32417834892960802761637949 12156688084860301035614231)
            ·
              refine ⟨18235032127290451553421347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12156688084860301035614231 18235032127290451553421347)
              ·
                refine ⟨27352548190935677330132021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18235032127290451553421347 27352548190935677330132021)
                ·
                  refine ⟨2564301392900219749699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27352548190935677330132021 2564301392900219749699877)
                  ·
                    refine ⟨480806511168791203068727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564301392900219749699877 480806511168791203068727)
                    ·
                      rfl

theorem cell23_2809102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_2809102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809102 prefixEnd_2809102 := by exact prefixLift 2809102
  have htrace : WordTrace (prefixWord ++ tailWord_2809102) baseStart_2809102 baseEnd_2809102 := by
    simpa [prefixWord, tailWord_2809102, baseEnd_2809102] using wordTrace_append hprefix tailTrace_2809102
  have hstable : (prefixWord ++ tailWord_2809102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809102).length < 2 ^ (prefixWord ++ tailWord_2809102).sum := by decide
  have hdescent : baseEnd_2809102 < baseStart_2809102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809112 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_2809112 : Nat := 118140960795 + 2809112 * 2 ^ 59
def prefixEnd_2809112 : Nat := 4983230072969 + 3 ^ 40 * 2809112 * 2
def baseEnd_2809112 : Nat := 1442424668312918570081135

theorem tailTrace_2809112 : CollatzResearch.WordTrace tailWord_2809112 prefixEnd_2809112 1442424668312918570081135 := by
  unfold tailWord_2809112
  simp only [CollatzResearch.WordTrace]
  refine ⟨51228365899537228489606795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68304487866049637986142393 51228365899537228489606795)
  ·
    refine ⟨76842548849305842734410193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51228365899537228489606795 76842548849305842734410193)
    ·
      refine ⟨57631911636979382050807645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76842548849305842734410193 57631911636979382050807645)
      ·
        refine ⟨21611966863867268269052867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57631911636979382050807645 21611966863867268269052867)
        ·
          refine ⟨32417950295800902403579301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21611966863867268269052867 32417950295800902403579301)
          ·
            refine ⟨6078365680462669200671119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32417950295800902403579301 6078365680462669200671119)
            ·
              refine ⟨9117548520694003801006679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078365680462669200671119 9117548520694003801006679)
              ·
                refine ⟨13676322781041005701510019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9117548520694003801006679 13676322781041005701510019)
                ·
                  refine ⟨20514484171561508552265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13676322781041005701510019 20514484171561508552265029)
                  ·
                    refine ⟨3846465782167782853549693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20514484171561508552265029 3846465782167782853549693)
                    ·
                      refine ⟨1442424668312918570081135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846465782167782853549693 1442424668312918570081135)
                      ·
                        rfl

theorem cell23_2809112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_2809112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809112 prefixEnd_2809112 := by exact prefixLift 2809112
  have htrace : WordTrace (prefixWord ++ tailWord_2809112) baseStart_2809112 baseEnd_2809112 := by
    simpa [prefixWord, tailWord_2809112, baseEnd_2809112] using wordTrace_append hprefix tailTrace_2809112
  have hstable : (prefixWord ++ tailWord_2809112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809112).length < 2 ^ (prefixWord ++ tailWord_2809112).sum := by decide
  have hdescent : baseEnd_2809112 < baseStart_2809112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809152 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2]
def baseStart_2809152 : Nat := 118140960795 + 2809152 * 2 ^ 59
def prefixEnd_2809152 : Nat := 4983230072969 + 3 ^ 40 * 2809152 * 2
def baseEnd_2809152 : Nat := 1442445207539098413580951

theorem tailTrace_2809152 : CollatzResearch.WordTrace tailWord_2809152 prefixEnd_2809152 1442445207539098413580951 := by
  unfold tailWord_2809152
  simp only [CollatzResearch.WordTrace]
  refine ⟨51229095359464771905334855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68305460479286362540446473 51229095359464771905334855)
  ·
    refine ⟨76843643039197157858002283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51229095359464771905334855 76843643039197157858002283)
    ·
      refine ⟨115265464558795736787003425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76843643039197157858002283 115265464558795736787003425)
      ·
        refine ⟨86449098419096802590252569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115265464558795736787003425 86449098419096802590252569)
        ·
          refine ⟨64836823814322601942689427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86449098419096802590252569 64836823814322601942689427)
          ·
            refine ⟨97255235721483902914034141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64836823814322601942689427 97255235721483902914034141)
            ·
              refine ⟨36470713395556463592762803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97255235721483902914034141 36470713395556463592762803)
              ·
                refine ⟨54706070093334695389144205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36470713395556463592762803 54706070093334695389144205)
                ·
                  refine ⟨20514776285000510770929077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54706070093334695389144205 20514776285000510770929077)
                  ·
                    refine ⟨1923260276718797884774601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20514776285000510770929077 1923260276718797884774601)
                    ·
                      refine ⟨1442445207539098413580951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923260276718797884774601 1442445207539098413580951)
                      ·
                        rfl

theorem cell23_2809152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_2809152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809152 prefixEnd_2809152 := by exact prefixLift 2809152
  have htrace : WordTrace (prefixWord ++ tailWord_2809152) baseStart_2809152 baseEnd_2809152 := by
    simpa [prefixWord, tailWord_2809152, baseEnd_2809152] using wordTrace_append hprefix tailTrace_2809152
  have hstable : (prefixWord ++ tailWord_2809152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809152).length < 2 ^ (prefixWord ++ tailWord_2809152).sum := by decide
  have hdescent : baseEnd_2809152 < baseStart_2809152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809159 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_2809159 : Nat := 118140960795 + 2809159 * 2 ^ 59
def prefixEnd_2809159 : Nat := 4983230072969 + 3 ^ 40 * 2809159 * 2
def baseEnd_2809159 : Nat := 1442448801903679886193419

theorem tailTrace_2809159 : CollatzResearch.WordTrace tailWord_2809159 prefixEnd_2809159 1442448801903679886193419 := by
  unfold tailWord_2809159
  simp only [CollatzResearch.WordTrace]
  refine ⟨102458446029904184006174531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68305630686602789337449687 102458446029904184006174531)
  ·
    refine ⟨153687669044856276009261797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102458446029904184006174531 153687669044856276009261797)
    ·
      refine ⟨28816437945910551751736587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153687669044856276009261797 28816437945910551751736587)
      ·
        refine ⟨43224656918865827627604881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28816437945910551751736587 43224656918865827627604881)
        ·
          refine ⟨32418492689149370720703661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43224656918865827627604881 32418492689149370720703661)
          ·
            refine ⟨12156934758431014020263873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32418492689149370720703661 12156934758431014020263873)
            ·
              refine ⟨9117701068823260515197905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12156934758431014020263873 9117701068823260515197905)
              ·
                refine ⟨6838275801617445386398429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9117701068823260515197905 6838275801617445386398429)
                ·
                  refine ⟨2564353425606542019899411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6838275801617445386398429 2564353425606542019899411)
                  ·
                    refine ⟨3846530138409813029849117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2564353425606542019899411 3846530138409813029849117)
                    ·
                      refine ⟨1442448801903679886193419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846530138409813029849117 1442448801903679886193419)
                      ·
                        rfl

theorem cell23_2809159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_2809159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809159 prefixEnd_2809159 := by exact prefixLift 2809159
  have htrace : WordTrace (prefixWord ++ tailWord_2809159) baseStart_2809159 baseEnd_2809159 := by
    simpa [prefixWord, tailWord_2809159, baseEnd_2809159] using wordTrace_append hprefix tailTrace_2809159
  have hstable : (prefixWord ++ tailWord_2809159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809159).length < 2 ^ (prefixWord ++ tailWord_2809159).sum := by decide
  have hdescent : baseEnd_2809159 < baseStart_2809159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809169 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_2809169 : Nat := 118140960795 + 2809169 * 2 ^ 59
def prefixEnd_2809169 : Nat := 4983230072969 + 3 ^ 40 * 2809169 * 2
def baseEnd_2809169 : Nat := 1442453936710224847068373

theorem tailTrace_2809169 : CollatzResearch.WordTrace tailWord_2809169 prefixEnd_2809169 1442453936710224847068373 := by
  unfold tailWord_2809169
  simp only [CollatzResearch.WordTrace]
  refine ⟨102458810759867955714038561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68305873839911970476025707 102458810759867955714038561)
  ·
    refine ⟨76844108069900966785528921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102458810759867955714038561 76844108069900966785528921)
    ·
      refine ⟨57633081052425725089146691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76844108069900966785528921 57633081052425725089146691)
      ·
        refine ⟨86449621578638587633720037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57633081052425725089146691 86449621578638587633720037)
        ·
          refine ⟨16209304045994735181322507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86449621578638587633720037 16209304045994735181322507)
          ·
            refine ⟨24313956068992102771983761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16209304045994735181322507 24313956068992102771983761)
            ·
              refine ⟨18235467051744077078987821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24313956068992102771983761 18235467051744077078987821)
              ·
                refine ⟨6838300144404028904620433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18235467051744077078987821 6838300144404028904620433)
                ·
                  refine ⟨5128725108303021678465325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838300144404028904620433 5128725108303021678465325)
                  ·
                    refine ⟨1923271915613633129424497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128725108303021678465325 1923271915613633129424497)
                    ·
                      refine ⟨1442453936710224847068373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923271915613633129424497 1442453936710224847068373)
                      ·
                        rfl

theorem cell23_2809169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_2809169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809169 prefixEnd_2809169 := by exact prefixLift 2809169
  have htrace : WordTrace (prefixWord ++ tailWord_2809169) baseStart_2809169 baseEnd_2809169 := by
    simpa [prefixWord, tailWord_2809169, baseEnd_2809169] using wordTrace_append hprefix tailTrace_2809169
  have hstable : (prefixWord ++ tailWord_2809169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809169).length < 2 ^ (prefixWord ++ tailWord_2809169).sum := by decide
  have hdescent : baseEnd_2809169 < baseStart_2809169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809186 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2809186 : Nat := 118140960795 + 2809186 * 2 ^ 59
def prefixEnd_2809186 : Nat := 4983230072969 + 3 ^ 40 * 2809186 * 2
def baseEnd_2809186 : Nat := 1442462665881351280555795

theorem tailTrace_2809186 : CollatzResearch.WordTrace tailWord_2809186 prefixEnd_2809186 1442462665881351280555795 := by
  unfold tailWord_2809186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25614857700201591904351853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68306287200537578411604941 25614857700201591904351853)
  ·
    refine ⟨9605571637575596964131945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25614857700201591904351853 9605571637575596964131945)
    ·
      refine ⟨7204178728181697723098959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9605571637575596964131945 7204178728181697723098959)
      ·
        refine ⟨10806268092272546584648439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204178728181697723098959 10806268092272546584648439)
        ·
          refine ⟨16209402138408819876972659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806268092272546584648439 16209402138408819876972659)
          ·
            refine ⟨24314103207613229815458989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16209402138408819876972659 24314103207613229815458989)
            ·
              refine ⟨9117788702854961180797121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24314103207613229815458989 9117788702854961180797121)
              ·
                refine ⟨6838341527141220885597841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9117788702854961180797121 6838341527141220885597841)
                ·
                  refine ⟨5128756145355915664198381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838341527141220885597841 5128756145355915664198381)
                  ·
                    refine ⟨1923283554508468374074393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128756145355915664198381 1923283554508468374074393)
                    ·
                      refine ⟨1442462665881351280555795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923283554508468374074393 1442462665881351280555795)
                      ·
                        rfl

theorem cell23_2809186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2809186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809186 prefixEnd_2809186 := by exact prefixLift 2809186
  have htrace : WordTrace (prefixWord ++ tailWord_2809186) baseStart_2809186 baseEnd_2809186 := by
    simpa [prefixWord, tailWord_2809186, baseEnd_2809186] using wordTrace_append hprefix tailTrace_2809186
  have hstable : (prefixWord ++ tailWord_2809186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809186).length < 2 ^ (prefixWord ++ tailWord_2809186).sum := by decide
  have hdescent : baseEnd_2809186 < baseStart_2809186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809195 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_2809195 : Nat := 118140960795 + 2809195 * 2 ^ 59
def prefixEnd_2809195 : Nat := 4983230072969 + 3 ^ 40 * 2809195 * 2
def baseEnd_2809195 : Nat := 1442467287207241745343253

theorem tailTrace_2809195 : CollatzResearch.WordTrace tailWord_2809195 prefixEnd_2809195 1442467287207241745343253 := by
  unfold tailWord_2809195
  simp only [CollatzResearch.WordTrace]
  refine ⟨102459759057773762154485039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68306506038515841436323359 102459759057773762154485039)
  ·
    refine ⟨153689638586660643231727559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102459759057773762154485039 153689638586660643231727559)
    ·
      refine ⟨230534457879990964847591339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153689638586660643231727559 230534457879990964847591339)
      ·
        refine ⟨345801686819986447271387009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230534457879990964847591339 345801686819986447271387009)
        ·
          refine ⟨259351265114989835453540257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345801686819986447271387009 259351265114989835453540257)
          ·
            refine ⟨194513448836242376590155193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259351265114989835453540257 194513448836242376590155193)
            ·
              refine ⟨145885086627181782442616395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194513448836242376590155193 145885086627181782442616395)
              ·
                refine ⟨218827629940772673663924593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145885086627181782442616395 218827629940772673663924593)
                ·
                  refine ⟨164120722455579505247943445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218827629940772673663924593 164120722455579505247943445)
                  ·
                    refine ⟨7693158865105289308497349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164120722455579505247943445 7693158865105289308497349)
                    ·
                      refine ⟨1442467287207241745343253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7693158865105289308497349 1442467287207241745343253)
                      ·
                        rfl

theorem cell23_2809195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_2809195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809195 prefixEnd_2809195 := by exact prefixLift 2809195
  have htrace : WordTrace (prefixWord ++ tailWord_2809195) baseStart_2809195 baseEnd_2809195 := by
    simpa [prefixWord, tailWord_2809195, baseEnd_2809195] using wordTrace_append hprefix tailTrace_2809195
  have hstable : (prefixWord ++ tailWord_2809195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809195).length < 2 ^ (prefixWord ++ tailWord_2809195).sum := by decide
  have hdescent : baseEnd_2809195 < baseStart_2809195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809202 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2809202 : Nat := 118140960795 + 2809202 * 2 ^ 59
def prefixEnd_2809202 : Nat := 4983230072969 + 3 ^ 40 * 2809202 * 2
def baseEnd_2809202 : Nat := 1442470881571823217955721

theorem tailTrace_2809202 : CollatzResearch.WordTrace tailWord_2809202 prefixEnd_2809202 1442470881571823217955721 := by
  unfold tailWord_2809202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615003592187100587497465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68306676245832268233326573 25615003592187100587497465)
  ·
    refine ⟨19211252694140325440623099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25615003592187100587497465 19211252694140325440623099)
    ·
      refine ⟨28816879041210488160934649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19211252694140325440623099 28816879041210488160934649)
      ·
        refine ⟨21612659280907866120700987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28816879041210488160934649 21612659280907866120700987)
        ·
          refine ⟨32418988921361799181051481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21612659280907866120700987 32418988921361799181051481)
          ·
            refine ⟨24314241691021349385788611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32418988921361799181051481 24314241691021349385788611)
            ·
              refine ⟨36471362536532024078682917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24314241691021349385788611 36471362536532024078682917)
              ·
                refine ⟨6838380475599754514753047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36471362536532024078682917 6838380475599754514753047)
                ·
                  refine ⟨10257570713399631772129571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6838380475599754514753047 10257570713399631772129571)
                  ·
                    refine ⟨15386356070099447658194357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10257570713399631772129571 15386356070099447658194357)
                    ·
                      refine ⟨1442470881571823217955721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15386356070099447658194357 1442470881571823217955721)
                      ·
                        rfl

theorem cell23_2809202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2809202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809202 prefixEnd_2809202 := by exact prefixLift 2809202
  have htrace : WordTrace (prefixWord ++ tailWord_2809202) baseStart_2809202 baseEnd_2809202 := by
    simpa [prefixWord, tailWord_2809202, baseEnd_2809202] using wordTrace_append hprefix tailTrace_2809202
  have hstable : (prefixWord ++ tailWord_2809202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809202).length < 2 ^ (prefixWord ++ tailWord_2809202).sum := by decide
  have hdescent : baseEnd_2809202 < baseStart_2809202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809212 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2809212 : Nat := 118140960795 + 2809212 * 2 ^ 59
def prefixEnd_2809212 : Nat := 4983230072969 + 3 ^ 40 * 2809212 * 2
def baseEnd_2809212 : Nat := 1442476016378368178830675

theorem tailTrace_2809212 : CollatzResearch.WordTrace tailWord_2809212 prefixEnd_2809212 1442476016378368178830675 := by
  unfold tailWord_2809212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230189549356087028926945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68306919399141449371902593 51230189549356087028926945)
  ·
    refine ⟨38422642162017065271695209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51230189549356087028926945 38422642162017065271695209)
    ·
      refine ⟨28816981621512798953771407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38422642162017065271695209 28816981621512798953771407)
      ·
        refine ⟨43225472432269198430657111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28816981621512798953771407 43225472432269198430657111)
        ·
          refine ⟨64838208648403797645985667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43225472432269198430657111 64838208648403797645985667)
          ·
            refine ⟨97257312972605696468978501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64838208648403797645985667 97257312972605696468978501)
            ·
              refine ⟨18235746182363568087933469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97257312972605696468978501 18235746182363568087933469)
              ·
                refine ⟨6838404818386338032975051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18235746182363568087933469 6838404818386338032975051)
                ·
                  refine ⟨10257607227579507049462577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6838404818386338032975051 10257607227579507049462577)
                  ·
                    refine ⟨7693205420684630287096933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10257607227579507049462577 7693205420684630287096933)
                    ·
                      refine ⟨1442476016378368178830675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7693205420684630287096933 1442476016378368178830675)
                      ·
                        rfl

theorem cell23_2809212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2809212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809212 prefixEnd_2809212 := by exact prefixLift 2809212
  have htrace : WordTrace (prefixWord ++ tailWord_2809212) baseStart_2809212 baseEnd_2809212 := by
    simpa [prefixWord, tailWord_2809212, baseEnd_2809212] using wordTrace_append hprefix tailTrace_2809212
  have hstable : (prefixWord ++ tailWord_2809212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809212).length < 2 ^ (prefixWord ++ tailWord_2809212).sum := by decide
  have hdescent : baseEnd_2809212 < baseStart_2809212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809219 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3]
def baseStart_2809219 : Nat := 118140960795 + 2809219 * 2 ^ 59
def prefixEnd_2809219 : Nat := 4983230072969 + 3 ^ 40 * 2809219 * 2
def baseEnd_2809219 : Nat := 1442479610742949651443143

theorem tailTrace_2809219 : CollatzResearch.WordTrace tailWord_2809219 prefixEnd_2809219 1442479610742949651443143 := by
  unfold tailWord_2809219
  simp only [CollatzResearch.WordTrace]
  refine ⟨102460634409686814253358711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68307089606457876168905807 102460634409686814253358711)
  ·
    refine ⟨153690951614530221380038067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102460634409686814253358711 153690951614530221380038067)
    ·
      refine ⟨230536427421795332070057101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153690951614530221380038067 230536427421795332070057101)
      ·
        refine ⟨86451160283173249526271413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230536427421795332070057101 86451160283173249526271413)
        ·
          refine ⟨8104796276547492143087945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86451160283173249526271413 8104796276547492143087945)
          ·
            refine ⟨6078597207410619107315959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8104796276547492143087945 6078597207410619107315959)
            ·
              refine ⟨9117895811115928660973939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078597207410619107315959 9117895811115928660973939)
              ·
                refine ⟨13676843716673892991460909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9117895811115928660973939 13676843716673892991460909)
                ·
                  refine ⟨5128816393752709871797841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13676843716673892991460909 5128816393752709871797841)
                  ·
                    refine ⟨3846612295314532403848381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128816393752709871797841 3846612295314532403848381)
                    ·
                      refine ⟨1442479610742949651443143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846612295314532403848381 1442479610742949651443143)
                      ·
                        rfl

theorem cell23_2809219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_2809219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809219 prefixEnd_2809219 := by exact prefixLift 2809219
  have htrace : WordTrace (prefixWord ++ tailWord_2809219) baseStart_2809219 baseEnd_2809219 := by
    simpa [prefixWord, tailWord_2809219, baseEnd_2809219] using wordTrace_append hprefix tailTrace_2809219
  have hstable : (prefixWord ++ tailWord_2809219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809219).length < 2 ^ (prefixWord ++ tailWord_2809219).sum := by decide
  have hdescent : baseEnd_2809219 < baseStart_2809219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809235 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 7]
def baseStart_2809235 : Nat := 118140960795 + 2809235 * 2 ^ 59
def prefixEnd_2809235 : Nat := 4983230072969 + 3 ^ 40 * 2809235 * 2
def baseEnd_2809235 : Nat := 480829275477807196281023

theorem tailTrace_2809235 : CollatzResearch.WordTrace tailWord_2809235 prefixEnd_2809235 480829275477807196281023 := by
  unfold tailWord_2809235
  simp only [CollatzResearch.WordTrace]
  refine ⟨102461217977628848985941159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68307478651752565990627439 102461217977628848985941159)
  ·
    refine ⟨153691826966443273478911739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102461217977628848985941159 153691826966443273478911739)
    ·
      refine ⟨230537740449664910218367609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153691826966443273478911739 230537740449664910218367609)
      ·
        refine ⟨172903305337248682663775707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230537740449664910218367609 172903305337248682663775707)
        ·
          refine ⟨259354958005873023995663561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172903305337248682663775707 259354958005873023995663561)
          ·
            refine ⟨194516218504404767996747671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259354958005873023995663561 194516218504404767996747671)
            ·
              refine ⟨291774327756607151995121507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194516218504404767996747671 291774327756607151995121507)
              ·
                refine ⟨437661491634910727992682261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291774327756607151995121507 437661491634910727992682261)
                ·
                  refine ⟨20515382420386440374656981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437661491634910727992682261 20515382420386440374656981)
                  ·
                    refine ⟨480829275477807196281023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20515382420386440374656981 480829275477807196281023)
                    ·
                      rfl

theorem cell23_2809235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_2809235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809235 prefixEnd_2809235 := by exact prefixLift 2809235
  have htrace : WordTrace (prefixWord ++ tailWord_2809235) baseStart_2809235 baseEnd_2809235 := by
    simpa [prefixWord, tailWord_2809235, baseEnd_2809235] using wordTrace_append hprefix tailTrace_2809235
  have hstable : (prefixWord ++ tailWord_2809235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809235).length < 2 ^ (prefixWord ++ tailWord_2809235).sum := by decide
  have hdescent : baseEnd_2809235 < baseStart_2809235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809236 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2809236 : Nat := 118140960795 + 2809236 * 2 ^ 59
def prefixEnd_2809236 : Nat := 4983230072969 + 3 ^ 40 * 2809236 * 2
def baseEnd_2809236 : Nat := 1442488339914076084930565

theorem tailTrace_2809236 : CollatzResearch.WordTrace tailWord_2809236 prefixEnd_2809236 1442488339914076084930565 := by
  unfold tailWord_2809236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230627225312613078363781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68307502967083484104485041 51230627225312613078363781)
  ·
    refine ⟨9605742604746114952193209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51230627225312613078363781 9605742604746114952193209)
    ·
      refine ⟨7204306953559586214144907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9605742604746114952193209 7204306953559586214144907)
      ·
        refine ⟨10806460430339379321217361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204306953559586214144907 10806460430339379321217361)
        ·
          refine ⟨8104845322754534490913021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10806460430339379321217361 8104845322754534490913021)
          ·
            refine ⟨3039316996032950434092383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8104845322754534490913021 3039316996032950434092383)
            ·
              refine ⟨4558975494049425651138575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039316996032950434092383 4558975494049425651138575)
              ·
                refine ⟨6838463241074138476707863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558975494049425651138575 6838463241074138476707863)
                ·
                  refine ⟨10257694861611207715061795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6838463241074138476707863 10257694861611207715061795)
                  ·
                    refine ⟨15386542292416811572592693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10257694861611207715061795 15386542292416811572592693)
                    ·
                      refine ⟨1442488339914076084930565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15386542292416811572592693 1442488339914076084930565)
                      ·
                        rfl

theorem cell23_2809236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2809236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809236 prefixEnd_2809236 := by exact prefixLift 2809236
  have htrace : WordTrace (prefixWord ++ tailWord_2809236) baseStart_2809236 baseEnd_2809236 := by
    simpa [prefixWord, tailWord_2809236, baseEnd_2809236] using wordTrace_append hprefix tailTrace_2809236
  have hstable : (prefixWord ++ tailWord_2809236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809236).length < 2 ^ (prefixWord ++ tailWord_2809236).sum := by decide
  have hdescent : baseEnd_2809236 < baseStart_2809236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809244 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2809244 : Nat := 118140960795 + 2809244 * 2 ^ 59
def prefixEnd_2809244 : Nat := 4983230072969 + 3 ^ 40 * 2809244 * 2
def baseEnd_2809244 : Nat := 1442492447759312053630529

theorem tailTrace_2809244 : CollatzResearch.WordTrace tailWord_2809244 prefixEnd_2809244 1442492447759312053630529 := by
  unfold tailWord_2809244
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230773117298121761509393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68307697489730829015345857 51230773117298121761509393)
  ·
    refine ⟨38423079837973591321132045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51230773117298121761509393 38423079837973591321132045)
    ·
      refine ⟨14408654939240096745424517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38423079837973591321132045 14408654939240096745424517)
      ·
        refine ⟨2701622801107518139767097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14408654939240096745424517 2701622801107518139767097)
        ·
          refine ⟨2026217100830638604825323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701622801107518139767097 2026217100830638604825323)
          ·
            refine ⟨3039325651245957907237985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026217100830638604825323 3039325651245957907237985)
            ·
              refine ⟨2279494238434468430428489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039325651245957907237985 2279494238434468430428489)
              ·
                refine ⟨1709620678825851322821367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279494238434468430428489 1709620678825851322821367)
                ·
                  refine ⟨2564431018238776984232051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709620678825851322821367 2564431018238776984232051)
                  ·
                    refine ⟨3846646527358165476348077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2564431018238776984232051 3846646527358165476348077)
                    ·
                      refine ⟨1442492447759312053630529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846646527358165476348077 1442492447759312053630529)
                      ·
                        rfl

theorem cell23_2809244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2809244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809244 prefixEnd_2809244 := by exact prefixLift 2809244
  have htrace : WordTrace (prefixWord ++ tailWord_2809244) baseStart_2809244 baseEnd_2809244 := by
    simpa [prefixWord, tailWord_2809244, baseEnd_2809244] using wordTrace_append hprefix tailTrace_2809244
  have hstable : (prefixWord ++ tailWord_2809244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809244).length < 2 ^ (prefixWord ++ tailWord_2809244).sum := by decide
  have hdescent : baseEnd_2809244 < baseStart_2809244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809250 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2809250 : Nat := 118140960795 + 2809250 * 2 ^ 59
def prefixEnd_2809250 : Nat := 4983230072969 + 3 ^ 40 * 2809250 * 2
def baseEnd_2809250 : Nat := 1442495528643239030155501

theorem tailTrace_2809250 : CollatzResearch.WordTrace tailWord_2809250 prefixEnd_2809250 1442495528643239030155501 := by
  unfold tailWord_2809250
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615441268143626636934301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68307843381716337698491469 25615441268143626636934301)
  ·
    refine ⟨9605790475553859988850363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25615441268143626636934301 9605790475553859988850363)
    ·
      refine ⟨14408685713330789983275545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605790475553859988850363 14408685713330789983275545)
      ·
        refine ⟨10806514284998092487456659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14408685713330789983275545 10806514284998092487456659)
        ·
          refine ⟨16209771427497138731184989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806514284998092487456659 16209771427497138731184989)
          ·
            refine ⟨6078664285311427024194371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16209771427497138731184989 6078664285311427024194371)
            ·
              refine ⟨9117996427967140536291557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078664285311427024194371 9117996427967140536291557)
              ·
                refine ⟨1709624330243838850554667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9117996427967140536291557 1709624330243838850554667)
                ·
                  refine ⟨2564436495365758275832001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709624330243838850554667 2564436495365758275832001)
                  ·
                    refine ⟨1923327371524318706874001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2564436495365758275832001 1923327371524318706874001)
                    ·
                      refine ⟨1442495528643239030155501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923327371524318706874001 1442495528643239030155501)
                      ·
                        rfl

theorem cell23_2809250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2809250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809250 prefixEnd_2809250 := by exact prefixLift 2809250
  have htrace : WordTrace (prefixWord ++ tailWord_2809250) baseStart_2809250 baseEnd_2809250 := by
    simpa [prefixWord, tailWord_2809250, baseEnd_2809250] using wordTrace_append hprefix tailTrace_2809250
  have hstable : (prefixWord ++ tailWord_2809250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809250).length < 2 ^ (prefixWord ++ tailWord_2809250).sum := by decide
  have hdescent : baseEnd_2809250 < baseStart_2809250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809256 : List Nat := [2, 1, 6, 1, 2, 2, 1, 8]
def baseStart_2809256 : Nat := 118140960795 + 2809256 * 2 ^ 59
def prefixEnd_2809256 : Nat := 4983230072969 + 3 ^ 40 * 2809256 * 2
def baseEnd_2809256 : Nat := 53425874426932074321499

theorem tailTrace_2809256 : CollatzResearch.WordTrace tailWord_2809256 prefixEnd_2809256 53425874426932074321499 := by
  unfold tailWord_2809256
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230991955276384786227811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68307989273701846381637081 51230991955276384786227811)
  ·
    refine ⟨76846487932914577179341717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51230991955276384786227811 76846487932914577179341717)
    ·
      refine ⟨3602179121855370805281643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76846487932914577179341717 3602179121855370805281643)
      ·
        refine ⟨5403268682783056207922465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602179121855370805281643 5403268682783056207922465)
        ·
          refine ⟨4052451512087292155941849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5403268682783056207922465 4052451512087292155941849)
          ·
            refine ⟨3039338634065469116956387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4052451512087292155941849 3039338634065469116956387)
            ·
              refine ⟨4559007951098203675434581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039338634065469116956387 4559007951098203675434581)
              ·
                refine ⟨53425874426932074321499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4559007951098203675434581 53425874426932074321499)
                ·
                  rfl

theorem cell23_2809256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 8].length) (baseStart_2809256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809256 prefixEnd_2809256 := by exact prefixLift 2809256
  have htrace : WordTrace (prefixWord ++ tailWord_2809256) baseStart_2809256 baseEnd_2809256 := by
    simpa [prefixWord, tailWord_2809256, baseEnd_2809256] using wordTrace_append hprefix tailTrace_2809256
  have hstable : (prefixWord ++ tailWord_2809256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809256).length < 2 ^ (prefixWord ++ tailWord_2809256).sum := by decide
  have hdescent : baseEnd_2809256 < baseStart_2809256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809300 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2809300 : Nat := 118140960795 + 2809300 * 2 ^ 59
def prefixEnd_2809300 : Nat := 4983230072969 + 3 ^ 40 * 2809300 * 2
def baseEnd_2809300 : Nat := 1442521202675963834530271

theorem tailTrace_2809300 : CollatzResearch.WordTrace tailWord_2809300 prefixEnd_2809300 1442521202675963834530271 := by
  unfold tailWord_2809300
  simp only [CollatzResearch.WordTrace]
  refine ⟨51231794361196682543528677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68309059148262243391371569 51231794361196682543528677)
  ·
    refine ⟨9605961442724377976911627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51231794361196682543528677 9605961442724377976911627)
    ·
      refine ⟨14408942164086566965367441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605961442724377976911627 14408942164086566965367441)
      ·
        refine ⟨10806706623064925224025581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14408942164086566965367441 10806706623064925224025581)
        ·
          refine ⟨4052514983649346959009593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10806706623064925224025581 4052514983649346959009593)
          ·
            refine ⟨3039386237737010219257195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4052514983649346959009593 3039386237737010219257195)
            ·
              refine ⟨4559079356605515328885793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039386237737010219257195 4559079356605515328885793)
              ·
                refine ⟨3419309517454136496664345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559079356605515328885793 3419309517454136496664345)
                ·
                  refine ⟨2564482138090602372498259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3419309517454136496664345 2564482138090602372498259)
                  ·
                    refine ⟨3846723207135903558747389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2564482138090602372498259 3846723207135903558747389)
                    ·
                      refine ⟨1442521202675963834530271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846723207135903558747389 1442521202675963834530271)
                      ·
                        rfl

theorem cell23_2809300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2809300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809300 prefixEnd_2809300 := by exact prefixLift 2809300
  have htrace : WordTrace (prefixWord ++ tailWord_2809300) baseStart_2809300 baseEnd_2809300 := by
    simpa [prefixWord, tailWord_2809300, baseEnd_2809300] using wordTrace_append hprefix tailTrace_2809300
  have hstable : (prefixWord ++ tailWord_2809300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809300).length < 2 ^ (prefixWord ++ tailWord_2809300).sum := by decide
  have hdescent : baseEnd_2809300 < baseStart_2809300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809319 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2809319 : Nat := 118140960795 + 2809319 * 2 ^ 59
def prefixEnd_2809319 : Nat := 4983230072969 + 3 ^ 40 * 2809319 * 2
def baseEnd_2809319 : Nat := 1442530958808399260192683

theorem tailTrace_2809319 : CollatzResearch.WordTrace tailWord_2809319 prefixEnd_2809319 1442530958808399260192683 := by
  unfold tailWord_2809319
  simp only [CollatzResearch.WordTrace]
  refine ⟨102464281709324531331999011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68309521139549687554666007 102464281709324531331999011)
  ·
    refine ⟨153696422563986796997998517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102464281709324531331999011 153696422563986796997998517)
    ·
      refine ⟨14409039615373762218562361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153696422563986796997998517 14409039615373762218562361)
      ·
        refine ⟨10806779711530321663921771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14409039615373762218562361 10806779711530321663921771)
        ·
          refine ⟨16210169567295482495882657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806779711530321663921771 16210169567295482495882657)
          ·
            refine ⟨12157627175471611871911993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16210169567295482495882657 12157627175471611871911993)
            ·
              refine ⟨9118220381603708903933995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157627175471611871911993 9118220381603708903933995)
              ·
                refine ⟨13677330572405563355900993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118220381603708903933995 13677330572405563355900993)
                ·
                  refine ⟨10257997929304172516925745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13677330572405563355900993 10257997929304172516925745)
                  ·
                    refine ⟨7693498446978129387694309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10257997929304172516925745 7693498446978129387694309)
                    ·
                      refine ⟨1442530958808399260192683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7693498446978129387694309 1442530958808399260192683)
                      ·
                        rfl

theorem cell23_2809319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2809319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809319 prefixEnd_2809319 := by exact prefixLift 2809319
  have htrace : WordTrace (prefixWord ++ tailWord_2809319) baseStart_2809319 baseEnd_2809319 := by
    simpa [prefixWord, tailWord_2809319, baseEnd_2809319] using wordTrace_append hprefix tailTrace_2809319
  have hstable : (prefixWord ++ tailWord_2809319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809319).length < 2 ^ (prefixWord ++ tailWord_2809319).sum := by decide
  have hdescent : baseEnd_2809319 < baseStart_2809319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809349 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_2809349 : Nat := 118140960795 + 2809349 * 2 ^ 59
def prefixEnd_2809349 : Nat := 4983230072969 + 3 ^ 40 * 2809349 * 2
def baseEnd_2809349 : Nat := 1442546363228034142817545

theorem tailTrace_2809349 : CollatzResearch.WordTrace tailWord_2809349 prefixEnd_2809349 1442546363228034142817545 := by
  unfold tailWord_2809349
  simp only [CollatzResearch.WordTrace]
  refine ⟨102465375899215846455591101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68310250599477230970394067 102465375899215846455591101)
  ·
    refine ⟨38424515962205942420846663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102465375899215846455591101 38424515962205942420846663)
    ·
      refine ⟨57636773943308913631269995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38424515962205942420846663 57636773943308913631269995)
      ·
        refine ⟨86455160914963370446904993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57636773943308913631269995 86455160914963370446904993)
        ·
          refine ⟨64841370686222527835178745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86455160914963370446904993 64841370686222527835178745)
          ·
            refine ⟨48631028014666895876384059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64841370686222527835178745 48631028014666895876384059)
            ·
              refine ⟨72946542022000343814576089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48631028014666895876384059 72946542022000343814576089)
              ·
                refine ⟨54709906516500257860932067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72946542022000343814576089 54709906516500257860932067)
                ·
                  refine ⟨82064859774750386791398101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54709906516500257860932067 82064859774750386791398101)
                  ·
                    refine ⟨1923395150970712190423393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82064859774750386791398101 1923395150970712190423393)
                    ·
                      refine ⟨1442546363228034142817545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923395150970712190423393 1442546363228034142817545)
                      ·
                        rfl

theorem cell23_2809349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_2809349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809349 prefixEnd_2809349 := by exact prefixLift 2809349
  have htrace : WordTrace (prefixWord ++ tailWord_2809349) baseStart_2809349 baseEnd_2809349 := by
    simpa [prefixWord, tailWord_2809349, baseEnd_2809349] using wordTrace_append hprefix tailTrace_2809349
  have hstable : (prefixWord ++ tailWord_2809349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809349).length < 2 ^ (prefixWord ++ tailWord_2809349).sum := by decide
  have hdescent : baseEnd_2809349 < baseStart_2809349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809392 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_2809392 : Nat := 118140960795 + 2809392 * 2 ^ 59
def prefixEnd_2809392 : Nat := 4983230072969 + 3 ^ 40 * 2809392 * 2
def baseEnd_2809392 : Nat := 1442568442896177474579847

theorem tailTrace_2809392 : CollatzResearch.WordTrace tailWord_2809392 prefixEnd_2809392 1442568442896177474579847 := by
  unfold tailWord_2809392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51233472119030032399703215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68311296158706709866270953 51233472119030032399703215)
  ·
    refine ⟨76850208178545048599554823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51233472119030032399703215 76850208178545048599554823)
    ·
      refine ⟨115275312267817572899332235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76850208178545048599554823 115275312267817572899332235)
      ·
        refine ⟨172912968401726359348998353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115275312267817572899332235 172912968401726359348998353)
        ·
          refine ⟨129684726301294769511748765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172912968401726359348998353 129684726301294769511748765)
          ·
            refine ⟨48631772362985538566905787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129684726301294769511748765 48631772362985538566905787)
            ·
              refine ⟨72947658544478307850358681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48631772362985538566905787 72947658544478307850358681)
              ·
                refine ⟨54710743908358730887769011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72947658544478307850358681 54710743908358730887769011)
                ·
                  refine ⟨82066115862538096331653517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54710743908358730887769011 82066115862538096331653517)
                  ·
                    refine ⟨30774793448451786124370069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82066115862538096331653517 30774793448451786124370069)
                    ·
                      refine ⟨1442568442896177474579847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30774793448451786124370069 1442568442896177474579847)
                      ·
                        rfl

theorem cell23_2809392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_2809392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809392 prefixEnd_2809392 := by exact prefixLift 2809392
  have htrace : WordTrace (prefixWord ++ tailWord_2809392) baseStart_2809392 baseEnd_2809392 := by
    simpa [prefixWord, tailWord_2809392, baseEnd_2809392] using wordTrace_append hprefix tailTrace_2809392
  have hstable : (prefixWord ++ tailWord_2809392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809392).length < 2 ^ (prefixWord ++ tailWord_2809392).sum := by decide
  have hdescent : baseEnd_2809392 < baseStart_2809392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809409 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2809409 : Nat := 118140960795 + 2809409 * 2 ^ 59
def prefixEnd_2809409 : Nat := 4983230072969 + 3 ^ 40 * 2809409 * 2
def baseEnd_2809409 : Nat := 1442577172067303908067269

theorem tailTrace_2809409 : CollatzResearch.WordTrace tailWord_2809409 prefixEnd_2809409 1442577172067303908067269 := by
  unfold tailWord_2809409
  simp only [CollatzResearch.WordTrace]
  refine ⟨102467564278998476702775281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68311709519332317801850187 102467564278998476702775281)
  ·
    refine ⟨76850673209248857527081461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102467564278998476702775281 76850673209248857527081461)
    ·
      refine ⟨7204750613367080393163887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76850673209248857527081461 7204750613367080393163887)
      ·
        refine ⟨10807125920050620589745831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204750613367080393163887 10807125920050620589745831)
        ·
          refine ⟨16210688880075930884618747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10807125920050620589745831 16210688880075930884618747)
          ·
            refine ⟨24316033320113896326928121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16210688880075930884618747 24316033320113896326928121)
            ·
              refine ⟨18237024990085422245196091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24316033320113896326928121 18237024990085422245196091)
              ·
                refine ⟨27355537485128133367794137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18237024990085422245196091 27355537485128133367794137)
                ·
                  refine ⟨20516653113846100025845603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27355537485128133367794137 20516653113846100025845603)
                  ·
                    refine ⟨30774979670769150038768405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20516653113846100025845603 30774979670769150038768405)
                    ·
                      refine ⟨1442577172067303908067269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30774979670769150038768405 1442577172067303908067269)
                      ·
                        rfl

theorem cell23_2809409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2809409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809409 prefixEnd_2809409 := by exact prefixLift 2809409
  have htrace : WordTrace (prefixWord ++ tailWord_2809409) baseStart_2809409 baseEnd_2809409 := by
    simpa [prefixWord, tailWord_2809409, baseEnd_2809409] using wordTrace_append hprefix tailTrace_2809409
  have hstable : (prefixWord ++ tailWord_2809409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809409).length < 2 ^ (prefixWord ++ tailWord_2809409).sum := by decide
  have hdescent : baseEnd_2809409 < baseStart_2809409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809414 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2809414 : Nat := 118140960795 + 2809414 * 2 ^ 59
def prefixEnd_2809414 : Nat := 4983230072969 + 3 ^ 40 * 2809414 * 2
def baseEnd_2809414 : Nat := 160286637718952932056083

theorem tailTrace_2809414 : CollatzResearch.WordTrace tailWord_2809414 prefixEnd_2809414 160286637718952932056083 := by
  unfold tailWord_2809414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202117082624386329897103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68311831095986908371138197 3202117082624386329897103)
  ·
    refine ⟨4803175623936579494845655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202117082624386329897103 4803175623936579494845655)
    ·
      refine ⟨7204763435904869242268483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803175623936579494845655 7204763435904869242268483)
      ·
        refine ⟨10807145153857303863402725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204763435904869242268483 10807145153857303863402725)
        ·
          refine ⟨2026339716348244474388011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10807145153857303863402725 2026339716348244474388011)
          ·
            refine ⟨3039509574522366711582017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026339716348244474388011 3039509574522366711582017)
            ·
              refine ⟨2279632180891775033686513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039509574522366711582017 2279632180891775033686513)
              ·
                refine ⟨1709724135668831275264885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279632180891775033686513 1709724135668831275264885)
                ·
                  refine ⟨160286637718952932056083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709724135668831275264885 160286637718952932056083)
                  ·
                    rfl

theorem cell23_2809414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2809414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809414 prefixEnd_2809414 := by exact prefixLift 2809414
  have htrace : WordTrace (prefixWord ++ tailWord_2809414) baseStart_2809414 baseEnd_2809414 := by
    simpa [prefixWord, tailWord_2809414, baseEnd_2809414] using wordTrace_append hprefix tailTrace_2809414
  have hstable : (prefixWord ++ tailWord_2809414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809414).length < 2 ^ (prefixWord ++ tailWord_2809414).sum := by decide
  have hdescent : baseEnd_2809414 < baseStart_2809414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809429 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2809429 : Nat := 118140960795 + 2809429 * 2 ^ 59
def prefixEnd_2809429 : Nat := 4983230072969 + 3 ^ 40 * 2809429 * 2
def baseEnd_2809429 : Nat := 1442587441680393829817177

theorem tailTrace_2809429 : CollatzResearch.WordTrace tailWord_2809429 prefixEnd_2809429 1442587441680393829817177 := by
  unfold tailWord_2809429
  simp only [CollatzResearch.WordTrace]
  refine ⟨102468293738926020118503341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68312195825950680079002227 102468293738926020118503341)
  ·
    refine ⟨38425610152097257544438753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102468293738926020118503341 38425610152097257544438753)
    ·
      refine ⟨28819207614072943158329065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38425610152097257544438753 28819207614072943158329065)
      ·
        refine ⟨21614405710554707368746799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28819207614072943158329065 21614405710554707368746799)
        ·
          refine ⟨32421608565832061053120199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21614405710554707368746799 32421608565832061053120199)
          ·
            refine ⟨48632412848748091579680299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32421608565832061053120199 48632412848748091579680299)
            ·
              refine ⟨72948619273122137369520449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48632412848748091579680299 72948619273122137369520449)
              ·
                refine ⟨54711464454841603027140337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72948619273122137369520449 54711464454841603027140337)
                ·
                  refine ⟨41033598341131202270355253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54711464454841603027140337 41033598341131202270355253)
                  ·
                    refine ⟨3846899844481050212845805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41033598341131202270355253 3846899844481050212845805)
                    ·
                      refine ⟨1442587441680393829817177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846899844481050212845805 1442587441680393829817177)
                      ·
                        rfl

theorem cell23_2809429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2809429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809429 prefixEnd_2809429 := by exact prefixLift 2809429
  have htrace : WordTrace (prefixWord ++ tailWord_2809429) baseStart_2809429 baseEnd_2809429 := by
    simpa [prefixWord, tailWord_2809429, baseEnd_2809429] using wordTrace_append hprefix tailTrace_2809429
  have hstable : (prefixWord ++ tailWord_2809429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809429).length < 2 ^ (prefixWord ++ tailWord_2809429).sum := by decide
  have hdescent : baseEnd_2809429 < baseStart_2809429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809436 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 6]
def baseStart_2809436 : Nat := 118140960795 + 2809436 * 2 ^ 59
def prefixEnd_2809436 : Nat := 4983230072969 + 3 ^ 40 * 2809436 * 2
def baseEnd_2809436 : Nat := 160287892893886144714405

theorem tailTrace_2809436 : CollatzResearch.WordTrace tailWord_2809436 prefixEnd_2809436 160287892893886144714405 := by
  unfold tailWord_2809436
  simp only [CollatzResearch.WordTrace]
  refine ⟨51234274524950330157004081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68312366033267106876005441 51234274524950330157004081)
  ·
    refine ⟨38425705893712747617753061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51234274524950330157004081 38425705893712747617753061)
    ·
      refine ⟨7204819855071140178328699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38425705893712747617753061 7204819855071140178328699)
      ·
        refine ⟨10807229782606710267493049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204819855071140178328699 10807229782606710267493049)
        ·
          refine ⟨8105422336955032700619787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10807229782606710267493049 8105422336955032700619787)
          ·
            refine ⟨12158133505432549050929681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105422336955032700619787 12158133505432549050929681)
            ·
              refine ⟨9118600129074411788197261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12158133505432549050929681 9118600129074411788197261)
              ·
                refine ⟨3419475048402904420573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9118600129074411788197261 3419475048402904420573973)
                ·
                  refine ⟨160287892893886144714405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3419475048402904420573973 160287892893886144714405)
                  ·
                    rfl

theorem cell23_2809436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_2809436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809436 prefixEnd_2809436 := by exact prefixLift 2809436
  have htrace : WordTrace (prefixWord ++ tailWord_2809436) baseStart_2809436 baseEnd_2809436 := by
    simpa [prefixWord, tailWord_2809436, baseEnd_2809436] using wordTrace_append hprefix tailTrace_2809436
  have hstable : (prefixWord ++ tailWord_2809436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809436).length < 2 ^ (prefixWord ++ tailWord_2809436).sum := by decide
  have hdescent : baseEnd_2809436 < baseStart_2809436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809449 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_2809449 : Nat := 118140960795 + 2809449 * 2 ^ 59
def prefixEnd_2809449 : Nat := 4983230072969 + 3 ^ 40 * 2809449 * 2
def baseEnd_2809449 : Nat := 480865903764494583855695

theorem tailTrace_2809449 : CollatzResearch.WordTrace tailWord_2809449 prefixEnd_2809449 480865903764494583855695 := by
  unfold tailWord_2809449
  simp only [CollatzResearch.WordTrace]
  refine ⟨102469023198853563534231401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68312682132569042356154267 102469023198853563534231401)
  ·
    refine ⟨76851767399140172650673551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102469023198853563534231401 76851767399140172650673551)
    ·
      refine ⟨115277651098710258976010327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76851767399140172650673551 115277651098710258976010327)
      ·
        refine ⟨172916476648065388464015491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115277651098710258976010327 172916476648065388464015491)
        ·
          refine ⟨259374714972098082696023237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172916476648065388464015491 259374714972098082696023237)
          ·
            refine ⟨48632759057268390505504357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259374714972098082696023237 48632759057268390505504357)
            ·
              refine ⟨9118642323237823219782067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48632759057268390505504357 9118642323237823219782067)
              ·
                refine ⟨13677963484856734829673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118642323237823219782067 13677963484856734829673101)
                ·
                  refine ⟨5129236306821275561127413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13677963484856734829673101 5129236306821275561127413)
                  ·
                    refine ⟨480865903764494583855695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5129236306821275561127413 480865903764494583855695)
                    ·
                      rfl

theorem cell23_2809449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_2809449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809449 prefixEnd_2809449 := by exact prefixLift 2809449
  have htrace : WordTrace (prefixWord ++ tailWord_2809449) baseStart_2809449 baseEnd_2809449 := by
    simpa [prefixWord, tailWord_2809449, baseEnd_2809449] using wordTrace_append hprefix tailTrace_2809449
  have hstable : (prefixWord ++ tailWord_2809449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809449).length < 2 ^ (prefixWord ++ tailWord_2809449).sum := by decide
  have hdescent : baseEnd_2809449 < baseStart_2809449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809489 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_2809489 : Nat := 118140960795 + 2809489 * 2 ^ 59
def prefixEnd_2809489 : Nat := 4983230072969 + 3 ^ 40 * 2809489 * 2
def baseEnd_2809489 : Nat := 1442618250519663595066901

theorem tailTrace_2809489 : CollatzResearch.WordTrace tailWord_2809489 prefixEnd_2809489 1442618250519663595066901 := by
  unfold tailWord_2809489
  simp only [CollatzResearch.WordTrace]
  refine ⟨102470482118708650365687521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68313654745805766910458347 102470482118708650365687521)
  ·
    refine ⟨76852861589031487774265641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102470482118708650365687521 76852861589031487774265641)
    ·
      refine ⟨57639646191773615830699231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76852861589031487774265641 57639646191773615830699231)
      ·
        refine ⟨86459469287660423746048847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57639646191773615830699231 86459469287660423746048847)
        ·
          refine ⟨129689203931490635619073271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86459469287660423746048847 129689203931490635619073271)
          ·
            refine ⟨194533805897235953428609907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129689203931490635619073271 194533805897235953428609907)
            ·
              refine ⟨291800708845853930142914861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194533805897235953428609907 291800708845853930142914861)
              ·
                refine ⟨109425265817195223803593073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291800708845853930142914861 109425265817195223803593073)
                ·
                  refine ⟨82068949362896417852694805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109425265817195223803593073 82068949362896417852694805)
                  ·
                    refine ⟨3846982001385769586845069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82068949362896417852694805 3846982001385769586845069)
                    ·
                      refine ⟨1442618250519663595066901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3846982001385769586845069 1442618250519663595066901)
                      ·
                        rfl

theorem cell23_2809489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_2809489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809489 prefixEnd_2809489 := by exact prefixLift 2809489
  have htrace : WordTrace (prefixWord ++ tailWord_2809489) baseStart_2809489 baseEnd_2809489 := by
    simpa [prefixWord, tailWord_2809489, baseEnd_2809489] using wordTrace_append hprefix tailTrace_2809489
  have hstable : (prefixWord ++ tailWord_2809489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809489).length < 2 ^ (prefixWord ++ tailWord_2809489).sum := by decide
  have hdescent : baseEnd_2809489 < baseStart_2809489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809496 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_2809496 : Nat := 118140960795 + 2809496 * 2 ^ 59
def prefixEnd_2809496 : Nat := 4983230072969 + 3 ^ 40 * 2809496 * 2
def baseEnd_2809496 : Nat := 480873948294748355893123

theorem tailTrace_2809496 : CollatzResearch.WordTrace tailWord_2809496 prefixEnd_2809496 480873948294748355893123 := by
  unfold tailWord_2809496
  simp only [CollatzResearch.WordTrace]
  refine ⟨51235368714841645280596171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68313824953122193707461561 51235368714841645280596171)
  ·
    refine ⟨76853053072262467920894257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51235368714841645280596171 76853053072262467920894257)
    ·
      refine ⟨57639789804196850940670693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76853053072262467920894257 57639789804196850940670693)
      ·
        refine ⟨10807460588286909551375755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57639789804196850940670693 10807460588286909551375755)
        ·
          refine ⟨16211190882430364327063633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10807460588286909551375755 16211190882430364327063633)
          ·
            refine ⟨12158393161822773245297725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16211190882430364327063633 12158393161822773245297725)
            ·
              refine ⟨4559397435683539966986647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12158393161822773245297725 4559397435683539966986647)
              ·
                refine ⟨6839096153525309950479971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559397435683539966986647 6839096153525309950479971)
                ·
                  refine ⟨10258644230287964925719957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839096153525309950479971 10258644230287964925719957)
                  ·
                    refine ⟨480873948294748355893123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10258644230287964925719957 480873948294748355893123)
                    ·
                      rfl

theorem cell23_2809496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_2809496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809496 prefixEnd_2809496 := by exact prefixLift 2809496
  have htrace : WordTrace (prefixWord ++ tailWord_2809496) baseStart_2809496 baseEnd_2809496 := by
    simpa [prefixWord, tailWord_2809496, baseEnd_2809496] using wordTrace_append hprefix tailTrace_2809496
  have hstable : (prefixWord ++ tailWord_2809496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809496).length < 2 ^ (prefixWord ++ tailWord_2809496).sum := by decide
  have hdescent : baseEnd_2809496 < baseStart_2809496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809586 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_2809586 : Nat := 118140960795 + 2809586 * 2 ^ 59
def prefixEnd_2809586 : Nat := 4983230072969 + 3 ^ 40 * 2809586 * 2
def baseEnd_2809586 : Nat := 480889352714383238517985

theorem tailTrace_2809586 : CollatzResearch.WordTrace tailWord_2809586 prefixEnd_2809586 480889352714383238517985 := by
  unfold tailWord_2809586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618504999839308982992153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68316013332904823954645741 25618504999839308982992153)
  ·
    refine ⟨19213878749879481737244115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25618504999839308982992153 19213878749879481737244115)
    ·
      refine ⟨28820818124819222605866173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19213878749879481737244115 28820818124819222605866173)
      ·
        refine ⟨10807806796807208477199815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28820818124819222605866173 10807806796807208477199815)
        ·
          refine ⟨16211710195210812715799723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10807806796807208477199815 16211710195210812715799723)
          ·
            refine ⟨24317565292816219073699585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16211710195210812715799723 24317565292816219073699585)
            ·
              refine ⟨18238173969612164305274689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24317565292816219073699585 18238173969612164305274689)
              ·
                refine ⟨13678630477209123228956017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18238173969612164305274689 13678630477209123228956017)
                ·
                  refine ⟨10258972857906842421717013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13678630477209123228956017 10258972857906842421717013)
                  ·
                    refine ⟨480889352714383238517985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10258972857906842421717013 480889352714383238517985)
                    ·
                      rfl

theorem cell23_2809586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_2809586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809586 prefixEnd_2809586 := by exact prefixLift 2809586
  have htrace : WordTrace (prefixWord ++ tailWord_2809586) baseStart_2809586 baseEnd_2809586 := by
    simpa [prefixWord, tailWord_2809586, baseEnd_2809586] using wordTrace_append hprefix tailTrace_2809586
  have hstable : (prefixWord ++ tailWord_2809586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809586).length < 2 ^ (prefixWord ++ tailWord_2809586).sum := by decide
  have hdescent : baseEnd_2809586 < baseStart_2809586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809588 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2809588 : Nat := 118140960795 + 2809588 * 2 ^ 59
def prefixEnd_2809588 : Nat := 4983230072969 + 3 ^ 40 * 2809588 * 2
def baseEnd_2809588 : Nat := 1442669085104458707728947

theorem tailTrace_2809588 : CollatzResearch.WordTrace tailWord_2809588 prefixEnd_2809588 1442669085104458707728947 := by
  unfold tailWord_2809588
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237046472674995136770709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68316061963566660182360945 51237046472674995136770709)
  ·
    refine ⟨2401736553406640397036127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51237046472674995136770709 2401736553406640397036127)
    ·
      refine ⟨3602604830109960595554191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401736553406640397036127 3602604830109960595554191)
      ·
        refine ⟨5403907245164940893331287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602604830109960595554191 5403907245164940893331287)
        ·
          refine ⟨8105860867747411339996931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403907245164940893331287 8105860867747411339996931)
          ·
            refine ⟨12158791301621117009995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105860867747411339996931 12158791301621117009995397)
            ·
              refine ⟨2279773369053959439374137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12158791301621117009995397 2279773369053959439374137)
              ·
                refine ⟨1709830026790469579530603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279773369053959439374137 1709830026790469579530603)
                ·
                  refine ⟨2564745040185704369295905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709830026790469579530603 2564745040185704369295905)
                  ·
                    refine ⟨1923558780139278276971929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2564745040185704369295905 1923558780139278276971929)
                    ·
                      refine ⟨1442669085104458707728947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923558780139278276971929 1442669085104458707728947)
                      ·
                        rfl

theorem cell23_2809588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2809588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809588 prefixEnd_2809588 := by exact prefixLift 2809588
  have htrace : WordTrace (prefixWord ++ tailWord_2809588) baseStart_2809588 baseEnd_2809588 := by
    simpa [prefixWord, tailWord_2809588, baseEnd_2809588] using wordTrace_append hprefix tailTrace_2809588
  have hstable : (prefixWord ++ tailWord_2809588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809588).length < 2 ^ (prefixWord ++ tailWord_2809588).sum := by decide
  have hdescent : baseEnd_2809588 < baseStart_2809588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809596 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2809596 : Nat := 118140960795 + 2809596 * 2 ^ 59
def prefixEnd_2809596 : Nat := 4983230072969 + 3 ^ 40 * 2809596 * 2
def baseEnd_2809596 : Nat := 1442673192949694676428909

theorem tailTrace_2809596 : CollatzResearch.WordTrace tailWord_2809596 prefixEnd_2809596 1442673192949694676428909 := by
  unfold tailWord_2809596
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237192364660503819916321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68316256486214005093221761 51237192364660503819916321)
  ·
    refine ⟨38427894273495377864937241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51237192364660503819916321 38427894273495377864937241)
    ·
      refine ⟨28820920705121533398702931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38427894273495377864937241 28820920705121533398702931)
      ·
        refine ⟨43231381057682300098054397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28820920705121533398702931 43231381057682300098054397)
        ·
          refine ⟨16211767896630862536770399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43231381057682300098054397 16211767896630862536770399)
          ·
            refine ⟨24317651844946293805155599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16211767896630862536770399 24317651844946293805155599)
            ·
              refine ⟨36476477767419440707733399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24317651844946293805155599 36476477767419440707733399)
              ·
                refine ⟨54714716651129161061600099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36476477767419440707733399 54714716651129161061600099)
                ·
                  refine ⟨82072074976693741592400149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54714716651129161061600099 82072074976693741592400149)
                  ·
                    refine ⟨3847128514532519137143757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82072074976693741592400149 3847128514532519137143757)
                    ·
                      refine ⟨1442673192949694676428909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847128514532519137143757 1442673192949694676428909)
                      ·
                        rfl

theorem cell23_2809596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2809596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809596 prefixEnd_2809596 := by exact prefixLift 2809596
  have htrace : WordTrace (prefixWord ++ tailWord_2809596) baseStart_2809596 baseEnd_2809596 := by
    simpa [prefixWord, tailWord_2809596, baseEnd_2809596] using wordTrace_append hprefix tailTrace_2809596
  have hstable : (prefixWord ++ tailWord_2809596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809596).length < 2 ^ (prefixWord ++ tailWord_2809596).sum := by decide
  have hdescent : baseEnd_2809596 < baseStart_2809596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809610 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_2809610 : Nat := 118140960795 + 2809610 * 2 ^ 59
def prefixEnd_2809610 : Nat := 4983230072969 + 3 ^ 40 * 2809610 * 2
def baseEnd_2809610 : Nat := 1442680381678857621653845

theorem tailTrace_2809610 : CollatzResearch.WordTrace tailWord_2809610 prefixEnd_2809610 1442680381678857621653845 := by
  unfold tailWord_2809610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618723837817572007710571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68316596900846858687228189 25618723837817572007710571)
  ·
    refine ⟨38428085756726358011565857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25618723837817572007710571 38428085756726358011565857)
    ·
      refine ⟨28821064317544768508674393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38428085756726358011565857 28821064317544768508674393)
      ·
        refine ⟨21615798238158576381505795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28821064317544768508674393 21615798238158576381505795)
        ·
          refine ⟨32423697357237864572258693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21615798238158576381505795 32423697357237864572258693)
          ·
            refine ⟨6079443254482099607298505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32423697357237864572258693 6079443254482099607298505)
            ·
              refine ⟨4559582440861574705473879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6079443254482099607298505 4559582440861574705473879)
              ·
                refine ⟨6839373661292362058210819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559582440861574705473879 6839373661292362058210819)
                ·
                  refine ⟨10259060491938543087316229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839373661292362058210819 10259060491938543087316229)
                  ·
                    refine ⟨1923573842238476828871793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10259060491938543087316229 1923573842238476828871793)
                    ·
                      refine ⟨1442680381678857621653845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923573842238476828871793 1442680381678857621653845)
                      ·
                        rfl

theorem cell23_2809610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_2809610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809610 prefixEnd_2809610 := by exact prefixLift 2809610
  have htrace : WordTrace (prefixWord ++ tailWord_2809610) baseStart_2809610 baseEnd_2809610 := by
    simpa [prefixWord, tailWord_2809610, baseEnd_2809610] using wordTrace_append hprefix tailTrace_2809610
  have hstable : (prefixWord ++ tailWord_2809610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809610).length < 2 ^ (prefixWord ++ tailWord_2809610).sum := by decide
  have hdescent : baseEnd_2809610 < baseStart_2809610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809633 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 5]
def baseStart_2809633 : Nat := 118140960795 + 2809633 * 2 ^ 59
def prefixEnd_2809633 : Nat := 4983230072969 + 3 ^ 40 * 2809633 * 2
def baseEnd_2809633 : Nat := 160299132414879003518471

theorem tailTrace_2809633 : CollatzResearch.WordTrace tailWord_2809633 prefixEnd_2809633 160299132414879003518471 := by
  unfold tailWord_2809633
  simp only [CollatzResearch.WordTrace]
  refine ⟨102475734230186962958929553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68317156153457975305953035 102475734230186962958929553)
  ·
    refine ⟨76856800672640222219197165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102475734230186962958929553 76856800672640222219197165)
    ·
      refine ⟨28821300252240083332198937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76856800672640222219197165 28821300252240083332198937)
      ·
        refine ⟨21615975189180062499149203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28821300252240083332198937 21615975189180062499149203)
        ·
          refine ⟨32423962783770093748723805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21615975189180062499149203 32423962783770093748723805)
          ·
            refine ⟨12158986043913785155771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32423962783770093748723805 12158986043913785155771427)
            ·
              refine ⟨18238479065870677733657141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12158986043913785155771427 18238479065870677733657141)
              ·
                refine ⟨1709857412425376037530357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18238479065870677733657141 1709857412425376037530357)
                ·
                  refine ⟨160299132414879003518471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709857412425376037530357 160299132414879003518471)
                  ·
                    rfl

theorem cell23_2809633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 5].length) (baseStart_2809633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809633 prefixEnd_2809633 := by exact prefixLift 2809633
  have htrace : WordTrace (prefixWord ++ tailWord_2809633) baseStart_2809633 baseEnd_2809633 := by
    simpa [prefixWord, tailWord_2809633, baseEnd_2809633] using wordTrace_append hprefix tailTrace_2809633
  have hstable : (prefixWord ++ tailWord_2809633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809633).length < 2 ^ (prefixWord ++ tailWord_2809633).sum := by decide
  have hdescent : baseEnd_2809633 < baseStart_2809633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809700 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_2809700 : Nat := 118140960795 + 2809700 * 2 ^ 59
def prefixEnd_2809700 : Nat := 4983230072969 + 3 ^ 40 * 2809700 * 2
def baseEnd_2809700 : Nat := 1442726594937762269528431

theorem tailTrace_2809700 : CollatzResearch.WordTrace tailWord_2809700 prefixEnd_2809700 1442726594937762269528431 := by
  unfold tailWord_2809700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51239088960472116700809277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68318785280629488934412369 51239088960472116700809277)
  ·
    refine ⟨19214658360177043762803479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51239088960472116700809277 19214658360177043762803479)
    ·
      refine ⟨28821987540265565644205219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19214658360177043762803479 28821987540265565644205219)
      ·
        refine ⟨43232981310398348466307829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28821987540265565644205219 43232981310398348466307829)
        ·
          refine ⟨4053091997849845168716359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43232981310398348466307829 4053091997849845168716359)
          ·
            refine ⟨6079637996774767753074539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053091997849845168716359 6079637996774767753074539)
            ·
              refine ⟨9119456995162151629611809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079637996774767753074539 9119456995162151629611809)
              ·
                refine ⟨6839592746371613722208857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9119456995162151629611809 6839592746371613722208857)
                ·
                  refine ⟨5129694559778710291656643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6839592746371613722208857 5129694559778710291656643)
                  ·
                    refine ⟨7694541839668065437484965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129694559778710291656643 7694541839668065437484965)
                    ·
                      refine ⟨1442726594937762269528431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7694541839668065437484965 1442726594937762269528431)
                      ·
                        rfl

theorem cell23_2809700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_2809700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809700 prefixEnd_2809700 := by exact prefixLift 2809700
  have htrace : WordTrace (prefixWord ++ tailWord_2809700) baseStart_2809700 baseEnd_2809700 := by
    simpa [prefixWord, tailWord_2809700, baseEnd_2809700] using wordTrace_append hprefix tailTrace_2809700
  have hstable : (prefixWord ++ tailWord_2809700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809700).length < 2 ^ (prefixWord ++ tailWord_2809700).sum := by decide
  have hdescent : baseEnd_2809700 < baseStart_2809700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809743 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 5, 2]
def baseStart_2809743 : Nat := 118140960795 + 2809743 * 2 ^ 59
def prefixEnd_2809743 : Nat := 4983230072969 + 3 ^ 40 * 2809743 * 2
def baseEnd_2809743 : Nat := 1442748674605905601290733

theorem tailTrace_2809743 : CollatzResearch.WordTrace tailWord_2809743 prefixEnd_2809743 1442748674605905601290733 := by
  unfold tailWord_2809743
  simp only [CollatzResearch.WordTrace]
  refine ⟨102479746259788451745433883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68319830839858967830289255 102479746259788451745433883)
  ·
    refine ⟨153719619389682677618150825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102479746259788451745433883 153719619389682677618150825)
    ·
      refine ⟨115289714542262008213613119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153719619389682677618150825 115289714542262008213613119)
      ·
        refine ⟨172934571813393012320419679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115289714542262008213613119 172934571813393012320419679)
        ·
          refine ⟨259401857720089518480629519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172934571813393012320419679 259401857720089518480629519)
          ·
            refine ⟨389102786580134277720944279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259401857720089518480629519 389102786580134277720944279)
            ·
              refine ⟨583654179870201416581416419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389102786580134277720944279 583654179870201416581416419)
              ·
                refine ⟨875481269805302124872124629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583654179870201416581416419 875481269805302124872124629)
                ·
                  refine ⟨20519092261061768551690421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 875481269805302124872124629 20519092261061768551690421)
                  ·
                    refine ⟨1923664899474540801720977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20519092261061768551690421 1923664899474540801720977)
                    ·
                      refine ⟨1442748674605905601290733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923664899474540801720977 1442748674605905601290733)
                      ·
                        rfl

theorem cell23_2809743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5, 2].length) (baseStart_2809743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809743 prefixEnd_2809743 := by exact prefixLift 2809743
  have htrace : WordTrace (prefixWord ++ tailWord_2809743) baseStart_2809743 baseEnd_2809743 := by
    simpa [prefixWord, tailWord_2809743, baseEnd_2809743] using wordTrace_append hprefix tailTrace_2809743
  have hstable : (prefixWord ++ tailWord_2809743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809743).length < 2 ^ (prefixWord ++ tailWord_2809743).sum := by decide
  have hdescent : baseEnd_2809743 < baseStart_2809743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809753 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_2809753 : Nat := 118140960795 + 2809753 * 2 ^ 59
def prefixEnd_2809753 : Nat := 4983230072969 + 3 ^ 40 * 2809753 * 2
def baseEnd_2809753 : Nat := 480917936470816854055229

theorem tailTrace_2809753 : CollatzResearch.WordTrace tailWord_2809753 prefixEnd_2809753 480917936470816854055229 := by
  unfold tailWord_2809753
  simp only [CollatzResearch.WordTrace]
  refine ⟨102480110989752223453297913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68320073993168148968865275 102480110989752223453297913)
  ·
    refine ⟨76860083242314167589973435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102480110989752223453297913 76860083242314167589973435)
    ·
      refine ⟨115290124863471251384960153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76860083242314167589973435 115290124863471251384960153)
      ·
        refine ⟨86467593647603438538720115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115290124863471251384960153 86467593647603438538720115)
        ·
          refine ⟨129701390471405157808080173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86467593647603438538720115 129701390471405157808080173)
          ·
            refine ⟨48638021426776934178030065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129701390471405157808080173 48638021426776934178030065)
            ·
              refine ⟨36478516070082700633522549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48638021426776934178030065 36478516070082700633522549)
              ·
                refine ⟨3419860881570253184392739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36478516070082700633522549 3419860881570253184392739)
                ·
                  refine ⟨5129791322355379776589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419860881570253184392739 5129791322355379776589109)
                  ·
                    refine ⟨480917936470816854055229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5129791322355379776589109 480917936470816854055229)
                    ·
                      rfl

theorem cell23_2809753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_2809753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809753 prefixEnd_2809753 := by exact prefixLift 2809753
  have htrace : WordTrace (prefixWord ++ tailWord_2809753) baseStart_2809753 baseEnd_2809753 := by
    simpa [prefixWord, tailWord_2809753, baseEnd_2809753] using wordTrace_append hprefix tailTrace_2809753
  have hstable : (prefixWord ++ tailWord_2809753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809753).length < 2 ^ (prefixWord ++ tailWord_2809753).sum := by decide
  have hdescent : baseEnd_2809753 < baseStart_2809753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809761 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 1, 4]
def baseStart_2809761 : Nat := 118140960795 + 2809761 * 2 ^ 59
def prefixEnd_2809761 : Nat := 4983230072969 + 3 ^ 40 * 2809761 * 2
def baseEnd_2809761 : Nat := 480919305752562176955217

theorem tailTrace_2809761 : CollatzResearch.WordTrace tailWord_2809761 prefixEnd_2809761 480919305752562176955217 := by
  unfold tailWord_2809761
  simp only [CollatzResearch.WordTrace]
  refine ⟨102480402773723240819589137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68320268515815493879726091 102480402773723240819589137)
  ·
    refine ⟨76860302080292430614691853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102480402773723240819589137 76860302080292430614691853)
    ·
      refine ⟨28822613280109661480509445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76860302080292430614691853 28822613280109661480509445)
      ·
        refine ⟨5404239990020561527595521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28822613280109661480509445 5404239990020561527595521)
        ·
          refine ⟨4053179992515421145696641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404239990020561527595521 4053179992515421145696641)
          ·
            refine ⟨3039884994386565859272481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4053179992515421145696641 3039884994386565859272481)
            ·
              refine ⟨2279913745789924394454361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039884994386565859272481 2279913745789924394454361)
              ·
                refine ⟨1709935309342443295840771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2279913745789924394454361 1709935309342443295840771)
                ·
                  refine ⟨2564902964013664943761157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709935309342443295840771 2564902964013664943761157)
                  ·
                    refine ⟨480919305752562176955217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564902964013664943761157 480919305752562176955217)
                    ·
                      rfl

theorem cell23_2809761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_2809761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809761 prefixEnd_2809761 := by exact prefixLift 2809761
  have htrace : WordTrace (prefixWord ++ tailWord_2809761) baseStart_2809761 baseEnd_2809761 := by
    simpa [prefixWord, tailWord_2809761, baseEnd_2809761] using wordTrace_append hprefix tailTrace_2809761
  have hstable : (prefixWord ++ tailWord_2809761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809761).length < 2 ^ (prefixWord ++ tailWord_2809761).sum := by decide
  have hdescent : baseEnd_2809761 < baseStart_2809761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809783 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 6, 4]
def baseStart_2809783 : Nat := 118140960795 + 2809783 * 2 ^ 59
def prefixEnd_2809783 : Nat := 4983230072969 + 3 ^ 40 * 2809783 * 2
def baseEnd_2809783 : Nat := 480923071277361814930183

theorem tailTrace_2809783 : CollatzResearch.WordTrace tailWord_2809783 prefixEnd_2809783 480923071277361814930183 := by
  unfold tailWord_2809783
  simp only [CollatzResearch.WordTrace]
  refine ⟨102481205179643538576890003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68320803453095692384593335 102481205179643538576890003)
  ·
    refine ⟨153721807769465307865335005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102481205179643538576890003 153721807769465307865335005)
    ·
      refine ⟨57645677913549490449500627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153721807769465307865335005 57645677913549490449500627)
      ·
        refine ⟨86468516870324235674250941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57645677913549490449500627 86468516870324235674250941)
        ·
          refine ⟨32425693826371588377844103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86468516870324235674250941 32425693826371588377844103)
          ·
            refine ⟨48638540739557382566766155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32425693826371588377844103 48638540739557382566766155)
            ·
              refine ⟨72957811109336073850149233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48638540739557382566766155 72957811109336073850149233)
              ·
                refine ⟨54718358332002055387611925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72957811109336073850149233 54718358332002055387611925)
                ·
                  refine ⟨2564923046812596346294309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54718358332002055387611925 2564923046812596346294309)
                  ·
                    refine ⟨480923071277361814930183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2564923046812596346294309 480923071277361814930183)
                    ·
                      rfl

theorem cell23_2809783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_2809783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809783 prefixEnd_2809783 := by exact prefixLift 2809783
  have htrace : WordTrace (prefixWord ++ tailWord_2809783) baseStart_2809783 baseEnd_2809783 := by
    simpa [prefixWord, tailWord_2809783, baseEnd_2809783] using wordTrace_append hprefix tailTrace_2809783
  have hstable : (prefixWord ++ tailWord_2809783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809783).length < 2 ^ (prefixWord ++ tailWord_2809783).sum := by decide
  have hdescent : baseEnd_2809783 < baseStart_2809783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809790 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2809790 : Nat := 118140960795 + 2809790 * 2 ^ 59
def prefixEnd_2809790 : Nat := 4983230072969 + 3 ^ 40 * 2809790 * 2
def baseEnd_2809790 : Nat := 1442772808196666917403017

theorem tailTrace_2809790 : CollatzResearch.WordTrace tailWord_2809790 prefixEnd_2809790 1442772808196666917403017 := by
  unfold tailWord_2809790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810182561327272346549353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68320973660412119181596549 12810182561327272346549353)
  ·
    refine ⟨9607636920995454259912015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12810182561327272346549353 9607636920995454259912015)
    ·
      refine ⟨14411455381493181389868023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9607636920995454259912015 14411455381493181389868023)
      ·
        refine ⟨21617183072239772084802035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14411455381493181389868023 21617183072239772084802035)
        ·
          refine ⟨32425774608359658127203053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21617183072239772084802035 32425774608359658127203053)
          ·
            refine ⟨12159665478134871797701145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32425774608359658127203053 12159665478134871797701145)
            ·
              refine ⟨9119749108601153848275859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12159665478134871797701145 9119749108601153848275859)
              ·
                refine ⟨13679623662901730772413789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9119749108601153848275859 13679623662901730772413789)
                ·
                  refine ⟨5129858873588149039655171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13679623662901730772413789 5129858873588149039655171)
                  ·
                    refine ⟨7694788310382223559482757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129858873588149039655171 7694788310382223559482757)
                    ·
                      refine ⟨1442772808196666917403017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7694788310382223559482757 1442772808196666917403017)
                      ·
                        rfl

theorem cell23_2809790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2809790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809790 prefixEnd_2809790 := by exact prefixLift 2809790
  have htrace : WordTrace (prefixWord ++ tailWord_2809790) baseStart_2809790 baseEnd_2809790 := by
    simpa [prefixWord, tailWord_2809790, baseEnd_2809790] using wordTrace_append hprefix tailTrace_2809790
  have hstable : (prefixWord ++ tailWord_2809790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809790).length < 2 ^ (prefixWord ++ tailWord_2809790).sum := by decide
  have hdescent : baseEnd_2809790 < baseStart_2809790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809803 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_2809803 : Nat := 118140960795 + 2809803 * 2 ^ 59
def prefixEnd_2809803 : Nat := 4983230072969 + 3 ^ 40 * 2809803 * 2
def baseEnd_2809803 : Nat := 1442779483445175366540457

theorem tailTrace_2809803 : CollatzResearch.WordTrace tailWord_2809803 prefixEnd_2809803 1442779483445175366540457 := by
  unfold tailWord_2809803
  simp only [CollatzResearch.WordTrace]
  refine ⟨102481934639571081992618063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68321289759714054661745375 102481934639571081992618063)
  ·
    refine ⟨153722901959356622988927095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102481934639571081992618063 153722901959356622988927095)
    ·
      refine ⟨230584352939034934483390643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153722901959356622988927095 230584352939034934483390643)
      ·
        refine ⟨345876529408552401725085965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230584352939034934483390643 345876529408552401725085965)
        ·
          refine ⟨129703698528207150646907237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345876529408552401725085965 129703698528207150646907237)
          ·
            refine ⟨24319443474038840746295107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129703698528207150646907237 24319443474038840746295107)
            ·
              refine ⟨36479165211058261119442661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24319443474038840746295107 36479165211058261119442661)
              ·
                refine ⟨6839843477073423959895499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36479165211058261119442661 6839843477073423959895499)
                ·
                  refine ⟨10259765215610135939843249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839843477073423959895499 10259765215610135939843249)
                  ·
                    refine ⟨7694823911707601954882437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10259765215610135939843249 7694823911707601954882437)
                    ·
                      refine ⟨1442779483445175366540457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7694823911707601954882437 1442779483445175366540457)
                      ·
                        rfl

theorem cell23_2809803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_2809803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809803 prefixEnd_2809803 := by exact prefixLift 2809803
  have htrace : WordTrace (prefixWord ++ tailWord_2809803) baseStart_2809803 baseEnd_2809803 := by
    simpa [prefixWord, tailWord_2809803, baseEnd_2809803] using wordTrace_append hprefix tailTrace_2809803
  have hstable : (prefixWord ++ tailWord_2809803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809803).length < 2 ^ (prefixWord ++ tailWord_2809803).sum := by decide
  have hdescent : baseEnd_2809803 < baseStart_2809803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809813 : List Nat := [1, 3, 2, 3, 2, 2, 10]
def baseStart_2809813 : Nat := 118140960795 + 2809813 * 2 ^ 59
def prefixEnd_2809813 : Nat := 4983230072969 + 3 ^ 40 * 2809813 * 2
def baseEnd_2809813 : Nat := 17812155780885436140931

theorem tailTrace_2809813 : CollatzResearch.WordTrace tailWord_2809813 prefixEnd_2809813 17812155780885436140931 := by
  unfold tailWord_2809813
  simp only [CollatzResearch.WordTrace]
  refine ⟨102482299369534853700482093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68321532913023235800321395 102482299369534853700482093)
  ·
    refine ⟨38430862263575570137680785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102482299369534853700482093 38430862263575570137680785)
    ·
      refine ⟨28823146697681677603260589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38430862263575570137680785 28823146697681677603260589)
      ·
        refine ⟨10808680011630629101222721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28823146697681677603260589 10808680011630629101222721)
        ·
          refine ⟨8106510008722971825917041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10808680011630629101222721 8106510008722971825917041)
          ·
            refine ⟨6079882506542228869437781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8106510008722971825917041 6079882506542228869437781)
            ·
              refine ⟨17812155780885436140931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6079882506542228869437781 17812155780885436140931)
              ·
                rfl

theorem cell23_2809813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 10].length) (baseStart_2809813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809813 prefixEnd_2809813 := by exact prefixLift 2809813
  have htrace : WordTrace (prefixWord ++ tailWord_2809813) baseStart_2809813 baseEnd_2809813 := by
    simpa [prefixWord, tailWord_2809813, baseEnd_2809813] using wordTrace_append hprefix tailTrace_2809813
  have hstable : (prefixWord ++ tailWord_2809813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809813).length < 2 ^ (prefixWord ++ tailWord_2809813).sum := by decide
  have hdescent : baseEnd_2809813 < baseStart_2809813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809837 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2809837 : Nat := 118140960795 + 2809837 * 2 ^ 59
def prefixEnd_2809837 : Nat := 4983230072969 + 3 ^ 40 * 2809837 * 2
def baseEnd_2809837 : Nat := 1442796941787428233515301

theorem tailTrace_2809837 : CollatzResearch.WordTrace tailWord_2809837 prefixEnd_2809837 1442796941787428233515301 := by
  unfold tailWord_2809837
  simp only [CollatzResearch.WordTrace]
  refine ⟨102483174721447905799355765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68322116480965270532903843 102483174721447905799355765)
  ·
    refine ⟨9607797630135741168689603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102483174721447905799355765 9607797630135741168689603)
    ·
      refine ⟨14411696445203611753034405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9607797630135741168689603 14411696445203611753034405)
      ·
        refine ⟨2702193083475677203693951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14411696445203611753034405 2702193083475677203693951)
        ·
          refine ⟨4053289625213515805540927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702193083475677203693951 4053289625213515805540927)
          ·
            refine ⟨6079934437820273708311391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053289625213515805540927 6079934437820273708311391)
            ·
              refine ⟨9119901656730410562467087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079934437820273708311391 9119901656730410562467087)
              ·
                refine ⟨13679852485095615843700631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9119901656730410562467087 13679852485095615843700631)
                ·
                  refine ⟨20519778727643423765550947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13679852485095615843700631 20519778727643423765550947)
                  ·
                    refine ⟨30779668091465135648326421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20519778727643423765550947 30779668091465135648326421)
                    ·
                      refine ⟨1442796941787428233515301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30779668091465135648326421 1442796941787428233515301)
                      ·
                        rfl

theorem cell23_2809837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2809837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809837 prefixEnd_2809837 := by exact prefixLift 2809837
  have htrace : WordTrace (prefixWord ++ tailWord_2809837) baseStart_2809837 baseEnd_2809837 := by
    simpa [prefixWord, tailWord_2809837, baseEnd_2809837] using wordTrace_append hprefix tailTrace_2809837
  have hstable : (prefixWord ++ tailWord_2809837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809837).length < 2 ^ (prefixWord ++ tailWord_2809837).sum := by decide
  have hdescent : baseEnd_2809837 < baseStart_2809837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809840 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_2809840 : Nat := 118140960795 + 2809840 * 2 ^ 59
def prefixEnd_2809840 : Nat := 4983230072969 + 3 ^ 40 * 2809840 * 2
def baseEnd_2809840 : Nat := 1442798482229391721777787

theorem tailTrace_2809840 : CollatzResearch.WordTrace tailWord_2809840 prefixEnd_2809840 1442798482229391721777787 := by
  unfold tailWord_2809840
  simp only [CollatzResearch.WordTrace]
  refine ⟨51241642070218518655857487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68322189426958024874476649 51241642070218518655857487)
  ·
    refine ⟨76862463105327777983786231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51241642070218518655857487 76862463105327777983786231)
    ·
      refine ⟨115293694657991666975679347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76862463105327777983786231 115293694657991666975679347)
      ·
        refine ⟨172940541986987500463519021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115293694657991666975679347 172940541986987500463519021)
        ·
          refine ⟨64852703245120312673819633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172940541986987500463519021 64852703245120312673819633)
          ·
            refine ⟨48639527433840234505364725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64852703245120312673819633 48639527433840234505364725)
            ·
              refine ⟨4559955696922521984877943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48639527433840234505364725 4559955696922521984877943)
              ·
                refine ⟨6839933545383782977316915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559955696922521984877943 6839933545383782977316915)
                ·
                  refine ⟨10259900318075674465975373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6839933545383782977316915 10259900318075674465975373)
                  ·
                    refine ⟨3847462619278377924740765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10259900318075674465975373 3847462619278377924740765)
                    ·
                      refine ⟨1442798482229391721777787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847462619278377924740765 1442798482229391721777787)
                      ·
                        rfl

theorem cell23_2809840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_2809840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809840 prefixEnd_2809840 := by exact prefixLift 2809840
  have htrace : WordTrace (prefixWord ++ tailWord_2809840) baseStart_2809840 baseEnd_2809840 := by
    simpa [prefixWord, tailWord_2809840, baseEnd_2809840] using wordTrace_append hprefix tailTrace_2809840
  have hstable : (prefixWord ++ tailWord_2809840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809840).length < 2 ^ (prefixWord ++ tailWord_2809840).sum := by decide
  have hdescent : baseEnd_2809840 < baseStart_2809840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809853 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2809853 : Nat := 118140960795 + 2809853 * 2 ^ 59
def prefixEnd_2809853 : Nat := 4983230072969 + 3 ^ 40 * 2809853 * 2
def baseEnd_2809853 : Nat := 1442805157477900170915227

theorem tailTrace_2809853 : CollatzResearch.WordTrace tailWord_2809853 prefixEnd_2809853 1442805157477900170915227 := by
  unfold tailWord_2809853
  simp only [CollatzResearch.WordTrace]
  refine ⟨102483758289389940531938213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68322505526259960354625475 102483758289389940531938213)
  ·
    refine ⟨19215704679260613849738415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102483758289389940531938213 19215704679260613849738415)
    ·
      refine ⟨28823557018890920774607623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19215704679260613849738415 28823557018890920774607623)
      ·
        refine ⟨43235335528336381161911435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28823557018890920774607623 43235335528336381161911435)
        ·
          refine ⟨64853003292504571742867153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43235335528336381161911435 64853003292504571742867153)
          ·
            refine ⟨48639752469378428807150365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64853003292504571742867153 48639752469378428807150365)
            ·
              refine ⟨18239907176016910802681387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48639752469378428807150365 18239907176016910802681387)
              ·
                refine ⟨27359860764025366204022081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18239907176016910802681387 27359860764025366204022081)
                ·
                  refine ⟨20519895573019024653016561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27359860764025366204022081 20519895573019024653016561)
                  ·
                    refine ⟨15389921679764268489762421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20519895573019024653016561 15389921679764268489762421)
                    ·
                      refine ⟨1442805157477900170915227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15389921679764268489762421 1442805157477900170915227)
                      ·
                        rfl

theorem cell23_2809853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2809853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809853 prefixEnd_2809853 := by exact prefixLift 2809853
  have htrace : WordTrace (prefixWord ++ tailWord_2809853) baseStart_2809853 baseEnd_2809853 := by
    simpa [prefixWord, tailWord_2809853, baseEnd_2809853] using wordTrace_append hprefix tailTrace_2809853
  have hstable : (prefixWord ++ tailWord_2809853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809853).length < 2 ^ (prefixWord ++ tailWord_2809853).sum := by decide
  have hdescent : baseEnd_2809853 < baseStart_2809853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809867 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 1, 3, 2]
def baseStart_2809867 : Nat := 118140960795 + 2809867 * 2 ^ 59
def prefixEnd_2809867 : Nat := 4983230072969 + 3 ^ 40 * 2809867 * 2
def baseEnd_2809867 : Nat := 1442812346207063116140163

theorem tailTrace_2809867 : CollatzResearch.WordTrace tailWord_2809867 prefixEnd_2809867 1442812346207063116140163 := by
  unfold tailWord_2809867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102484268911339220922947855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68322845940892813948631903 102484268911339220922947855)
  ·
    refine ⟨153726403367008831384421783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102484268911339220922947855 153726403367008831384421783)
    ·
      refine ⟨230589605050513247076632675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153726403367008831384421783 230589605050513247076632675)
      ·
        refine ⟨345884407575769870614949013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230589605050513247076632675 345884407575769870614949013)
        ·
          refine ⟨16213331605114212685075735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 345884407575769870614949013 16213331605114212685075735)
          ·
            refine ⟨24319997407671319027613603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16213331605114212685075735 24319997407671319027613603)
            ·
              refine ⟨36479996111506978541420405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24319997407671319027613603 36479996111506978541420405)
              ·
                refine ⟨3419999635453779238258163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36479996111506978541420405 3419999635453779238258163)
                ·
                  refine ⟨5129999453180668857387245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419999635453779238258163 5129999453180668857387245)
                  ·
                    refine ⟨1923749794942750821520217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5129999453180668857387245 1923749794942750821520217)
                    ·
                      refine ⟨1442812346207063116140163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923749794942750821520217 1442812346207063116140163)
                      ·
                        rfl

theorem cell23_2809867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 3, 2].length) (baseStart_2809867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809867 prefixEnd_2809867 := by exact prefixLift 2809867
  have htrace : WordTrace (prefixWord ++ tailWord_2809867) baseStart_2809867 baseEnd_2809867 := by
    simpa [prefixWord, tailWord_2809867, baseEnd_2809867] using wordTrace_append hprefix tailTrace_2809867
  have hstable : (prefixWord ++ tailWord_2809867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809867).length < 2 ^ (prefixWord ++ tailWord_2809867).sum := by decide
  have hdescent : baseEnd_2809867 < baseStart_2809867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809918 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2809918 : Nat := 118140960795 + 2809918 * 2 ^ 59
def prefixEnd_2809918 : Nat := 4983230072969 + 3 ^ 40 * 2809918 * 2
def baseEnd_2809918 : Nat := 1442838533720442416602429

theorem tailTrace_2809918 : CollatzResearch.WordTrace tailWord_2809918 prefixEnd_2809918 1442838533720442416602429 := by
  unfold tailWord_2809918
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810766129269307079131801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68324086022769637755369605 12810766129269307079131801)
  ·
    refine ⟨9608074596951980309348851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12810766129269307079131801 9608074596951980309348851)
    ·
      refine ⟨14412111895427970464023277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9608074596951980309348851 14412111895427970464023277)
      ·
        refine ⟨5404541960785488924008729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14412111895427970464023277 5404541960785488924008729)
        ·
          refine ⟨4053406470589116693006547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404541960785488924008729 4053406470589116693006547)
          ·
            refine ⟨6080109705883675039509821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053406470589116693006547 6080109705883675039509821)
            ·
              refine ⟨2280041139706378139816183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080109705883675039509821 2280041139706378139816183)
              ·
                refine ⟨3420061709559567209724275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280041139706378139816183 3420061709559567209724275)
                ·
                  refine ⟨5130092564339350814586413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420061709559567209724275 5130092564339350814586413)
                  ·
                    refine ⟨1923784711627256555469905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5130092564339350814586413 1923784711627256555469905)
                    ·
                      refine ⟨1442838533720442416602429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923784711627256555469905 1442838533720442416602429)
                      ·
                        rfl

theorem cell23_2809918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2809918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809918 prefixEnd_2809918 := by exact prefixLift 2809918
  have htrace : WordTrace (prefixWord ++ tailWord_2809918) baseStart_2809918 baseEnd_2809918 := by
    simpa [prefixWord, tailWord_2809918, baseEnd_2809918] using wordTrace_append hprefix tailTrace_2809918
  have hstable : (prefixWord ++ tailWord_2809918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809918).length < 2 ^ (prefixWord ++ tailWord_2809918).sum := by decide
  have hdescent : baseEnd_2809918 < baseStart_2809918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809930 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_2809930 : Nat := 118140960795 + 2809930 * 2 ^ 59
def prefixEnd_2809930 : Nat := 4983230072969 + 3 ^ 40 * 2809930 * 2
def baseEnd_2809930 : Nat := 1442844695488296369652373

theorem tailTrace_2809930 : CollatzResearch.WordTrace tailWord_2809930 prefixEnd_2809930 1442844695488296369652373 := by
  unfold tailWord_2809930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25621641677527745670622811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68324377806740655121660829 25621641677527745670622811)
  ·
    refine ⟨38432462516291618505934217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25621641677527745670622811 38432462516291618505934217)
    ·
      refine ⟨28824346887218713879450663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38432462516291618505934217 28824346887218713879450663)
      ·
        refine ⟨43236520330828070819175995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28824346887218713879450663 43236520330828070819175995)
        ·
          refine ⟨64854780496242106228763993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43236520330828070819175995 64854780496242106228763993)
          ·
            refine ⟨48641085372181579671572995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64854780496242106228763993 48641085372181579671572995)
            ·
              refine ⟨72961628058272369507359493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48641085372181579671572995 72961628058272369507359493)
              ·
                refine ⟨13680305260926069282629905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72961628058272369507359493 13680305260926069282629905)
                ·
                  refine ⟨10260228945694551961972429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13680305260926069282629905 10260228945694551961972429)
                  ·
                    refine ⟨3847585854635456985739661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10260228945694551961972429 3847585854635456985739661)
                    ·
                      refine ⟨1442844695488296369652373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847585854635456985739661 1442844695488296369652373)
                      ·
                        rfl

theorem cell23_2809930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_2809930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809930 prefixEnd_2809930 := by exact prefixLift 2809930
  have htrace : WordTrace (prefixWord ++ tailWord_2809930) baseStart_2809930 baseEnd_2809930 := by
    simpa [prefixWord, tailWord_2809930, baseEnd_2809930] using wordTrace_append hprefix tailTrace_2809930
  have hstable : (prefixWord ++ tailWord_2809930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809930).length < 2 ^ (prefixWord ++ tailWord_2809930).sum := by decide
  have hdescent : baseEnd_2809930 < baseStart_2809930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809967 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 2, 5]
def baseStart_2809967 : Nat := 118140960795 + 2809967 * 2 ^ 59
def prefixEnd_2809967 : Nat := 4983230072969 + 3 ^ 40 * 2809967 * 2
def baseEnd_2809967 : Nat := 480954564757504241629901

theorem tailTrace_2809967 : CollatzResearch.WordTrace tailWord_2809967 prefixEnd_2809967 480954564757504241629901 := by
  unfold tailWord_2809967
  simp only [CollatzResearch.WordTrace]
  refine ⟨102487916210976938001588155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68325277473984625334392103 102487916210976938001588155)
  ·
    refine ⟨153731874316465407002382233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102487916210976938001588155 153731874316465407002382233)
    ·
      refine ⟨115298905737349055251786675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153731874316465407002382233 115298905737349055251786675)
      ·
        refine ⟨172948358606023582877680013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115298905737349055251786675 172948358606023582877680013)
        ·
          refine ⟨64855634477258843579130005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172948358606023582877680013 64855634477258843579130005)
          ·
            refine ⟨3040107866121508292771719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64855634477258843579130005 3040107866121508292771719)
            ·
              refine ⟨4560161799182262439157579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040107866121508292771719 4560161799182262439157579)
              ·
                refine ⟨6840242698773393658736369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560161799182262439157579 6840242698773393658736369)
                ·
                  refine ⟨5130182024080045244052277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6840242698773393658736369 5130182024080045244052277)
                  ·
                    refine ⟨480954564757504241629901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5130182024080045244052277 480954564757504241629901)
                    ·
                      rfl

theorem cell23_2809967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 5].length) (baseStart_2809967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809967 prefixEnd_2809967 := by exact prefixLift 2809967
  have htrace : WordTrace (prefixWord ++ tailWord_2809967) baseStart_2809967 baseEnd_2809967 := by
    simpa [prefixWord, tailWord_2809967, baseEnd_2809967] using wordTrace_append hprefix tailTrace_2809967
  have hstable : (prefixWord ++ tailWord_2809967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809967).length < 2 ^ (prefixWord ++ tailWord_2809967).sum := by decide
  have hdescent : baseEnd_2809967 < baseStart_2809967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2809987 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 4, 2]
def baseStart_2809987 : Nat := 118140960795 + 2809987 * 2 ^ 59
def prefixEnd_2809987 : Nat := 4983230072969 + 3 ^ 40 * 2809987 * 2
def baseEnd_2809987 : Nat := 1442873963885602646639611

theorem tailTrace_2809987 : CollatzResearch.WordTrace tailWord_2809987 prefixEnd_2809987 1442873963885602646639611 := by
  unfold tailWord_2809987
  simp only [CollatzResearch.WordTrace]
  refine ⟨102488645670904481417316215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68325763780602987611544143 102488645670904481417316215)
  ·
    refine ⟨153732968506356722125974323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102488645670904481417316215 153732968506356722125974323)
    ·
      refine ⟨230599452759535083188961485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153732968506356722125974323 230599452759535083188961485)
      ·
        refine ⟨86474794784825656195860557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230599452759535083188961485 86474794784825656195860557)
        ·
          refine ⟨32428048044309621073447709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86474794784825656195860557 32428048044309621073447709)
          ·
            refine ⟨12160518016616107902542891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32428048044309621073447709 12160518016616107902542891)
            ·
              refine ⟨18240777024924161853814337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160518016616107902542891 18240777024924161853814337)
              ·
                refine ⟨13680582768693121390360753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18240777024924161853814337 13680582768693121390360753)
                ·
                  refine ⟨10260437076519841042770565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13680582768693121390360753 10260437076519841042770565)
                  ·
                    refine ⟨1923831951847470195519481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10260437076519841042770565 1923831951847470195519481)
                    ·
                      refine ⟨1442873963885602646639611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923831951847470195519481 1442873963885602646639611)
                      ·
                        rfl

theorem cell23_2809987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_2809987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2809987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2809987 prefixEnd_2809987 := by exact prefixLift 2809987
  have htrace : WordTrace (prefixWord ++ tailWord_2809987) baseStart_2809987 baseEnd_2809987 := by
    simpa [prefixWord, tailWord_2809987, baseEnd_2809987] using wordTrace_append hprefix tailTrace_2809987
  have hstable : (prefixWord ++ tailWord_2809987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2809987).length < 2 ^ (prefixWord ++ tailWord_2809987).sum := by decide
  have hdescent : baseEnd_2809987 < baseStart_2809987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2809987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810087 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 6]
def baseStart_2810087 : Nat := 118140960795 + 2810087 * 2 ^ 59
def prefixEnd_2810087 : Nat := 4983230072969 + 3 ^ 40 * 2810087 * 2
def baseEnd_2810087 : Nat := 480975103983684085129717

theorem tailTrace_2810087 : CollatzResearch.WordTrace tailWord_2810087 prefixEnd_2810087 480975103983684085129717 := by
  unfold tailWord_2810087
  simp only [CollatzResearch.WordTrace]
  refine ⟨102492292970542198495956515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68328195313694798997304343 102492292970542198495956515)
  ·
    refine ⟨153738439455813297743934773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102492292970542198495956515 153738439455813297743934773)
    ·
      refine ⟨14412978698982496663493885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153738439455813297743934773 14412978698982496663493885)
      ·
        refine ⟨5404867012118436248810207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14412978698982496663493885 5404867012118436248810207)
        ·
          refine ⟨8107300518177654373215311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404867012118436248810207 8107300518177654373215311)
          ·
            refine ⟨12160950777266481559822967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107300518177654373215311 12160950777266481559822967)
            ·
              refine ⟨18241426165899722339734451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160950777266481559822967 18241426165899722339734451)
              ·
                refine ⟨27362139248849583509601677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18241426165899722339734451 27362139248849583509601677)
                ·
                  refine ⟨10260802218318593816100629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27362139248849583509601677 10260802218318593816100629)
                  ·
                    refine ⟨480975103983684085129717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10260802218318593816100629 480975103983684085129717)
                    ·
                      rfl

theorem cell23_2810087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_2810087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810087 prefixEnd_2810087 := by exact prefixLift 2810087
  have htrace : WordTrace (prefixWord ++ tailWord_2810087) baseStart_2810087 baseEnd_2810087 := by
    simpa [prefixWord, tailWord_2810087, baseEnd_2810087] using wordTrace_append hprefix tailTrace_2810087
  have hstable : (prefixWord ++ tailWord_2810087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810087).length < 2 ^ (prefixWord ++ tailWord_2810087).sum := by decide
  have hdescent : baseEnd_2810087 < baseStart_2810087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810097 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2810097 : Nat := 118140960795 + 2810097 * 2 ^ 59
def prefixEnd_2810097 : Nat := 4983230072969 + 3 ^ 40 * 2810097 * 2
def baseEnd_2810097 : Nat := 1442930446757597216264105

theorem tailTrace_2810097 : CollatzResearch.WordTrace tailWord_2810097 prefixEnd_2810097 1442930446757597216264105 := by
  unfold tailWord_2810097
  simp only [CollatzResearch.WordTrace]
  refine ⟨102492657700505970203820545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68328438467003980135880363 102492657700505970203820545)
  ·
    refine ⟨76869493275379477652865409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102492657700505970203820545 76869493275379477652865409)
    ·
      refine ⟨57652119956534608239649057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76869493275379477652865409 57652119956534608239649057)
      ·
        refine ⟨43239089967400956179736793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57652119956534608239649057 43239089967400956179736793)
        ·
          refine ⟨32429317475550717134802595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43239089967400956179736793 32429317475550717134802595)
          ·
            refine ⟨48643976213326075702203893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32429317475550717134802595 48643976213326075702203893)
            ·
              refine ⟨4560372769999319597081615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48643976213326075702203893 4560372769999319597081615)
              ·
                refine ⟨6840559154998979395622423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560372769999319597081615 6840559154998979395622423)
                ·
                  refine ⟨10260838732498469093433635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840559154998979395622423 10260838732498469093433635)
                  ·
                    refine ⟨15391258098747703640150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10260838732498469093433635 15391258098747703640150453)
                    ·
                      refine ⟨1442930446757597216264105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15391258098747703640150453 1442930446757597216264105)
                      ·
                        rfl

theorem cell23_2810097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2810097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810097 prefixEnd_2810097 := by exact prefixLift 2810097
  have htrace : WordTrace (prefixWord ++ tailWord_2810097) baseStart_2810097 baseEnd_2810097 := by
    simpa [prefixWord, tailWord_2810097, baseEnd_2810097] using wordTrace_append hprefix tailTrace_2810097
  have hstable : (prefixWord ++ tailWord_2810097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810097).length < 2 ^ (prefixWord ++ tailWord_2810097).sum := by decide
  have hdescent : baseEnd_2810097 < baseStart_2810097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810144 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2810144 : Nat := 118140960795 + 2810144 * 2 ^ 59
def prefixEnd_2810144 : Nat := 4983230072969 + 3 ^ 40 * 2810144 * 2
def baseEnd_2810144 : Nat := 1442954580348358532376389

theorem tailTrace_2810144 : CollatzResearch.WordTrace tailWord_2810144 prefixEnd_2810144 1442954580348358532376389 := by
  unfold tailWord_2810144
  simp only [CollatzResearch.WordTrace]
  refine ⟨51247185965667848615390743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68329581287557131487187657 51247185965667848615390743)
  ·
    refine ⟨76870778948501772923086115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51247185965667848615390743 76870778948501772923086115)
    ·
      refine ⟨115306168422752659384629173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76870778948501772923086115 115306168422752659384629173)
      ·
        refine ⟨10809953289633061817308985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115306168422752659384629173 10809953289633061817308985)
        ·
          refine ⟨8107464967224796362981739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10809953289633061817308985 8107464967224796362981739)
          ·
            refine ⟨12161197450837194544472609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107464967224796362981739 12161197450837194544472609)
            ·
              refine ⟨9120898088127895908354457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12161197450837194544472609 9120898088127895908354457)
              ·
                refine ⟨6840673566095921931265843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9120898088127895908354457 6840673566095921931265843)
                ·
                  refine ⟨10261010349143882896898765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840673566095921931265843 10261010349143882896898765)
                  ·
                    refine ⟨3847878880928956086337037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10261010349143882896898765 3847878880928956086337037)
                    ·
                      refine ⟨1442954580348358532376389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847878880928956086337037 1442954580348358532376389)
                      ·
                        rfl

theorem cell23_2810144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2810144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810144 prefixEnd_2810144 := by exact prefixLift 2810144
  have htrace : WordTrace (prefixWord ++ tailWord_2810144) baseStart_2810144 baseEnd_2810144 := by
    simpa [prefixWord, tailWord_2810144, baseEnd_2810144] using wordTrace_append hprefix tailTrace_2810144
  have hstable : (prefixWord ++ tailWord_2810144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810144).length < 2 ^ (prefixWord ++ tailWord_2810144).sum := by decide
  have hdescent : baseEnd_2810144 < baseStart_2810144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810148 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_2810148 : Nat := 118140960795 + 2810148 * 2 ^ 59
def prefixEnd_2810148 : Nat := 4983230072969 + 3 ^ 40 * 2810148 * 2
def baseEnd_2810148 : Nat := 1442956634270976516726371

theorem tailTrace_2810148 : CollatzResearch.WordTrace tailWord_2810148 prefixEnd_2810148 1442956634270976516726371 := by
  unfold tailWord_2810148
  simp only [CollatzResearch.WordTrace]
  refine ⟨51247258911660602956963549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68329678548880803942618065 51247258911660602956963549)
  ·
    refine ⟨19217722091872726108861331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51247258911660602956963549 19217722091872726108861331)
    ·
      refine ⟨28826583137809089163291997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19217722091872726108861331 28826583137809089163291997)
      ·
        refine ⟨10809968676678408436234499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28826583137809089163291997 10809968676678408436234499)
        ·
          refine ⟨16214953015017612654351749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10809968676678408436234499 16214953015017612654351749)
          ·
            refine ⟨3040303690315802372690953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16214953015017612654351749 3040303690315802372690953)
            ·
              refine ⟨2280227767736851779518215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040303690315802372690953 2280227767736851779518215)
              ·
                refine ⟨3420341651605277669277323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280227767736851779518215 3420341651605277669277323)
                ·
                  refine ⟨5130512477407916503915985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420341651605277669277323 5130512477407916503915985)
                  ·
                    refine ⟨3847884358055937377936989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5130512477407916503915985 3847884358055937377936989)
                    ·
                      refine ⟨1442956634270976516726371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847884358055937377936989 1442956634270976516726371)
                      ·
                        rfl

theorem cell23_2810148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_2810148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810148 prefixEnd_2810148 := by exact prefixLift 2810148
  have htrace : WordTrace (prefixWord ++ tailWord_2810148) baseStart_2810148 baseEnd_2810148 := by
    simpa [prefixWord, tailWord_2810148, baseEnd_2810148] using wordTrace_append hprefix tailTrace_2810148
  have hstable : (prefixWord ++ tailWord_2810148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810148).length < 2 ^ (prefixWord ++ tailWord_2810148).sum := by decide
  have hdescent : baseEnd_2810148 < baseStart_2810148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810151 : List Nat := [1, 1, 8, 1, 1, 1, 10]
def baseStart_2810151 : Nat := 118140960795 + 2810151 * 2 ^ 59
def prefixEnd_2810151 : Nat := 4983230072969 + 3 ^ 40 * 2810151 * 2
def baseEnd_2810151 : Nat := 17814298453246172901097

theorem tailTrace_2810151 : CollatzResearch.WordTrace tailWord_2810151 prefixEnd_2810151 17814298453246172901097 := by
  unfold tailWord_2810151
  simp only [CollatzResearch.WordTrace]
  refine ⟨102494627242310337426286307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68329751494873558284190871 102494627242310337426286307)
  ·
    refine ⟨153741940863465506139429461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102494627242310337426286307 153741940863465506139429461)
    ·
      refine ⟨1801663369493736400071439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 153741940863465506139429461 1801663369493736400071439)
      ·
        refine ⟨2702495054240604600107159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801663369493736400071439 2702495054240604600107159)
        ·
          refine ⟨4053742581360906900160739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702495054240604600107159 4053742581360906900160739)
          ·
            refine ⟨6080613872041360350241109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053742581360906900160739 6080613872041360350241109)
            ·
              refine ⟨17814298453246172901097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6080613872041360350241109 17814298453246172901097)
              ·
                rfl

theorem cell23_2810151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 10].length) (baseStart_2810151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810151 prefixEnd_2810151 := by exact prefixLift 2810151
  have htrace : WordTrace (prefixWord ++ tailWord_2810151) baseStart_2810151 baseEnd_2810151 := by
    simpa [prefixWord, tailWord_2810151, baseEnd_2810151] using wordTrace_append hprefix tailTrace_2810151
  have hstable : (prefixWord ++ tailWord_2810151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810151).length < 2 ^ (prefixWord ++ tailWord_2810151).sum := by decide
  have hdescent : baseEnd_2810151 < baseStart_2810151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810161 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2810161 : Nat := 118140960795 + 2810161 * 2 ^ 59
def prefixEnd_2810161 : Nat := 4983230072969 + 3 ^ 40 * 2810161 * 2
def baseEnd_2810161 : Nat := 1442963309519484965863811

theorem tailTrace_2810161 : CollatzResearch.WordTrace tailWord_2810161 prefixEnd_2810161 1442963309519484965863811 := by
  unfold tailWord_2810161
  simp only [CollatzResearch.WordTrace]
  refine ⟨102494991972274109134150337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68329994648182739422766891 102494991972274109134150337)
  ·
    refine ⟨76871243979205581850612753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102494991972274109134150337 76871243979205581850612753)
    ·
      refine ⟨57653432984404186387959565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76871243979205581850612753 57653432984404186387959565)
      ·
        refine ⟨21620037369151569895484837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57653432984404186387959565 21620037369151569895484837)
        ·
          refine ⟨4053757006715919355403407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21620037369151569895484837 4053757006715919355403407)
          ·
            refine ⟨6080635510073879033105111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053757006715919355403407 6080635510073879033105111)
            ·
              refine ⟨9120953265110818549657667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080635510073879033105111 9120953265110818549657667)
              ·
                refine ⟨13681429897666227824486501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9120953265110818549657667 13681429897666227824486501)
                ·
                  refine ⟨2565268105812417717091219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13681429897666227824486501 2565268105812417717091219)
                  ·
                    refine ⟨3847902158718626575636829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565268105812417717091219 3847902158718626575636829)
                    ·
                      refine ⟨1442963309519484965863811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3847902158718626575636829 1442963309519484965863811)
                      ·
                        rfl

theorem cell23_2810161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2810161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810161 prefixEnd_2810161 := by exact prefixLift 2810161
  have htrace : WordTrace (prefixWord ++ tailWord_2810161) baseStart_2810161 baseEnd_2810161 := by
    simpa [prefixWord, tailWord_2810161, baseEnd_2810161] using wordTrace_append hprefix tailTrace_2810161
  have hstable : (prefixWord ++ tailWord_2810161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810161).length < 2 ^ (prefixWord ++ tailWord_2810161).sum := by decide
  have hdescent : baseEnd_2810161 < baseStart_2810161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810218 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2810218 : Nat := 118140960795 + 2810218 * 2 ^ 59
def prefixEnd_2810218 : Nat := 4983230072969 + 3 ^ 40 * 2810218 * 2
def baseEnd_2810218 : Nat := 1442992577916791242851049

theorem tailTrace_2810218 : CollatzResearch.WordTrace tailWord_2810218 prefixEnd_2810218 1442992577916791242851049 := by
  unfold tailWord_2810218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25624267733266901967243827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68331380622045071912650205 25624267733266901967243827)
  ·
    refine ⟨38436401599900352950865741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25624267733266901967243827 38436401599900352950865741)
    ·
      refine ⟨14413650599962632356574653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38436401599900352950865741 14413650599962632356574653)
      ·
        refine ⟨5405118974985987133715495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14413650599962632356574653 5405118974985987133715495)
        ·
          refine ⟨8107678462478980700573243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405118974985987133715495 8107678462478980700573243)
          ·
            refine ⟨12161517693718471050859865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107678462478980700573243 12161517693718471050859865)
            ·
              refine ⟨9121138270288853288144899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12161517693718471050859865 9121138270288853288144899)
              ·
                refine ⟨13681707405433279932217349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9121138270288853288144899 13681707405433279932217349)
                ·
                  refine ⟨2565320138518739987290753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13681707405433279932217349 2565320138518739987290753)
                  ·
                    refine ⟨1923990103889054990468065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565320138518739987290753 1923990103889054990468065)
                    ·
                      refine ⟨1442992577916791242851049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1923990103889054990468065 1442992577916791242851049)
                      ·
                        rfl

theorem cell23_2810218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2810218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810218 prefixEnd_2810218 := by exact prefixLift 2810218
  have htrace : WordTrace (prefixWord ++ tailWord_2810218) baseStart_2810218 baseEnd_2810218 := by
    simpa [prefixWord, tailWord_2810218, baseEnd_2810218] using wordTrace_append hprefix tailTrace_2810218
  have hstable : (prefixWord ++ tailWord_2810218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810218).length < 2 ^ (prefixWord ++ tailWord_2810218).sum := by decide
  have hdescent : baseEnd_2810218 < baseStart_2810218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810224 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 7]
def baseStart_2810224 : Nat := 118140960795 + 2810224 * 2 ^ 59
def prefixEnd_2810224 : Nat := 4983230072969 + 3 ^ 40 * 2810224 * 2
def baseEnd_2810224 : Nat := 160332850977857579930669

theorem tailTrace_2810224 : CollatzResearch.WordTrace tailWord_2810224 prefixEnd_2810224 160332850977857579930669 := by
  unfold tailWord_2810224
  simp only [CollatzResearch.WordTrace]
  refine ⟨51248644885522935446846863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68331526514030580595795817 51248644885522935446846863)
  ·
    refine ⟨76872967328284403170270295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51248644885522935446846863 76872967328284403170270295)
    ·
      refine ⟨115309450992426604755405443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76872967328284403170270295 115309450992426604755405443)
      ·
        refine ⟨172964176488639907133108165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115309450992426604755405443 172964176488639907133108165)
        ·
          refine ⟨32430783091619982587457781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172964176488639907133108165 32430783091619982587457781)
          ·
            refine ⟨3040385914839373367574167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32430783091619982587457781 3040385914839373367574167)
            ·
              refine ⟨4560578872259060051361251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040385914839373367574167 4560578872259060051361251)
              ·
                refine ⟨6840868308388590077041877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560578872259060051361251 6840868308388590077041877)
                ·
                  refine ⟨160332850977857579930669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6840868308388590077041877 160332850977857579930669)
                  ·
                    rfl

theorem cell23_2810224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_2810224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810224 prefixEnd_2810224 := by exact prefixLift 2810224
  have htrace : WordTrace (prefixWord ++ tailWord_2810224) baseStart_2810224 baseEnd_2810224 := by
    simpa [prefixWord, tailWord_2810224, baseEnd_2810224] using wordTrace_append hprefix tailTrace_2810224
  have hstable : (prefixWord ++ tailWord_2810224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810224).length < 2 ^ (prefixWord ++ tailWord_2810224).sum := by decide
  have hdescent : baseEnd_2810224 < baseStart_2810224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810235 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 2, 2, 2]
def baseStart_2810235 : Nat := 118140960795 + 2810235 * 2 ^ 59
def prefixEnd_2810235 : Nat := 4983230072969 + 3 ^ 40 * 2810235 * 2
def baseEnd_2810235 : Nat := 1443001307087917676338471

theorem tailTrace_2810235 : CollatzResearch.WordTrace tailWord_2810235 prefixEnd_2810235 1443001307087917676338471 := by
  unfold tailWord_2810235
  simp only [CollatzResearch.WordTrace]
  refine ⟨102497690974006019772344159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68331793982670679848229439 102497690974006019772344159)
  ·
    refine ⟨153746536461009029658516239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102497690974006019772344159 153746536461009029658516239)
    ·
      refine ⟨230619804691513544487774359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153746536461009029658516239 230619804691513544487774359)
      ·
        refine ⟨345929707037270316731661539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230619804691513544487774359 345929707037270316731661539)
        ·
          refine ⟨518894560555905475097492309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345929707037270316731661539 518894560555905475097492309)
          ·
            refine ⟨3040397815757258643149369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 518894560555905475097492309 3040397815757258643149369)
            ·
              refine ⟨2280298361817943982362027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040397815757258643149369 2280298361817943982362027)
              ·
                refine ⟨3420447542726915973543041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280298361817943982362027 3420447542726915973543041)
                ·
                  refine ⟨2565335657045186980157281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420447542726915973543041 2565335657045186980157281)
                  ·
                    refine ⟨1924001742783890235117961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565335657045186980157281 1924001742783890235117961)
                    ·
                      refine ⟨1443001307087917676338471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924001742783890235117961 1443001307087917676338471)
                      ·
                        rfl

theorem cell23_2810235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 2, 2].length) (baseStart_2810235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810235 prefixEnd_2810235 := by exact prefixLift 2810235
  have htrace : WordTrace (prefixWord ++ tailWord_2810235) baseStart_2810235 baseEnd_2810235 := by
    simpa [prefixWord, tailWord_2810235, baseEnd_2810235] using wordTrace_append hprefix tailTrace_2810235
  have hstable : (prefixWord ++ tailWord_2810235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810235).length < 2 ^ (prefixWord ++ tailWord_2810235).sum := by decide
  have hdescent : baseEnd_2810235 < baseStart_2810235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810247 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2810247 : Nat := 118140960795 + 2810247 * 2 ^ 59
def prefixEnd_2810247 : Nat := 4983230072969 + 3 ^ 40 * 2810247 * 2
def baseEnd_2810247 : Nat := 1443007468855771629388415

theorem tailTrace_2810247 : CollatzResearch.WordTrace tailWord_2810247 prefixEnd_2810247 1443007468855771629388415 := by
  unfold tailWord_2810247
  simp only [CollatzResearch.WordTrace]
  refine ⟨102498128649962545821780995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68332085766641697214520663 102498128649962545821780995)
  ·
    refine ⟨153747192974943818732671493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102498128649962545821780995 153747192974943818732671493)
    ·
      refine ⟨28827598682801966012375905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153747192974943818732671493 28827598682801966012375905)
      ·
        refine ⟨21620699012101474509281929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28827598682801966012375905 21620699012101474509281929)
        ·
          refine ⟨16215524259076105881961447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21620699012101474509281929 16215524259076105881961447)
          ·
            refine ⟨24323286388614158822942171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16215524259076105881961447 24323286388614158822942171)
            ·
              refine ⟨36484929582921238234413257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24323286388614158822942171 36484929582921238234413257)
              ·
                refine ⟨27363697187190928675809943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36484929582921238234413257 27363697187190928675809943)
                ·
                  refine ⟨41045545780786393013714915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27363697187190928675809943 41045545780786393013714915)
                  ·
                    refine ⟨61568318671179589520572373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41045545780786393013714915 61568318671179589520572373)
                    ·
                      refine ⟨1443007468855771629388415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61568318671179589520572373 1443007468855771629388415)
                      ·
                        rfl

theorem cell23_2810247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2810247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810247 prefixEnd_2810247 := by exact prefixLift 2810247
  have htrace : WordTrace (prefixWord ++ tailWord_2810247) baseStart_2810247 baseEnd_2810247 := by
    simpa [prefixWord, tailWord_2810247, baseEnd_2810247] using wordTrace_append hprefix tailTrace_2810247
  have hstable : (prefixWord ++ tailWord_2810247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810247).length < 2 ^ (prefixWord ++ tailWord_2810247).sum := by decide
  have hdescent : baseEnd_2810247 < baseStart_2810247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810264 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2810264 : Nat := 118140960795 + 2810264 * 2 ^ 59
def prefixEnd_2810264 : Nat := 4983230072969 + 3 ^ 40 * 2810264 * 2
def baseEnd_2810264 : Nat := 1443016198026898062875837

theorem tailTrace_2810264 : CollatzResearch.WordTrace tailWord_2810264 prefixEnd_2810264 1443016198026898062875837 := by
  unfold tailWord_2810264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51249374345450478862574923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68332499127267305150099897 51249374345450478862574923)
  ·
    refine ⟨76874061518175718293862385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51249374345450478862574923 76874061518175718293862385)
    ·
      refine ⟨57655546138631788720396789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76874061518175718293862385 57655546138631788720396789)
      ·
        refine ⟨5405207450496730192537199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57655546138631788720396789 5405207450496730192537199)
        ·
          refine ⟨8107811175745095288805799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405207450496730192537199 8107811175745095288805799)
          ·
            refine ⟨12161716763617642933208699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107811175745095288805799 12161716763617642933208699)
            ·
              refine ⟨18242575145426464399813049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12161716763617642933208699 18242575145426464399813049)
              ·
                refine ⟨13681931359069848299859787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18242575145426464399813049 13681931359069848299859787)
                ·
                  refine ⟨20522897038604772449789681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13681931359069848299859787 20522897038604772449789681)
                  ·
                    refine ⟨15392172778953579337342261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20522897038604772449789681 15392172778953579337342261)
                    ·
                      refine ⟨1443016198026898062875837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15392172778953579337342261 1443016198026898062875837)
                      ·
                        rfl

theorem cell23_2810264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2810264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810264 prefixEnd_2810264 := by exact prefixLift 2810264
  have htrace : WordTrace (prefixWord ++ tailWord_2810264) baseStart_2810264 baseEnd_2810264 := by
    simpa [prefixWord, tailWord_2810264, baseEnd_2810264] using wordTrace_append hprefix tailTrace_2810264
  have hstable : (prefixWord ++ tailWord_2810264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810264).length < 2 ^ (prefixWord ++ tailWord_2810264).sum := by decide
  have hdescent : baseEnd_2810264 < baseStart_2810264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810277 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_2810277 : Nat := 118140960795 + 2810277 * 2 ^ 59
def prefixEnd_2810277 : Nat := 4983230072969 + 3 ^ 40 * 2810277 * 2
def baseEnd_2810277 : Nat := 1443022873275406512013277

theorem tailTrace_2810277 : CollatzResearch.WordTrace tailWord_2810277 prefixEnd_2810277 1443022873275406512013277 := by
  unfold tailWord_2810277
  simp only [CollatzResearch.WordTrace]
  refine ⟨102499222839853860945373085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68332815226569240630248723 102499222839853860945373085)
  ·
    refine ⟨38437208564945197854514907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102499222839853860945373085 38437208564945197854514907)
    ·
      refine ⟨57655812847417796781772361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38437208564945197854514907 57655812847417796781772361)
      ·
        refine ⟨43241859635563347586329271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57655812847417796781772361 43241859635563347586329271)
        ·
          refine ⟨64862789453345021379493907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43241859635563347586329271 64862789453345021379493907)
          ·
            refine ⟨97294184180017532069240861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64862789453345021379493907 97294184180017532069240861)
            ·
              refine ⟨36485319067506574525965323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97294184180017532069240861 36485319067506574525965323)
              ·
                refine ⟨54727978601259861788947985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36485319067506574525965323 54727978601259861788947985)
                ·
                  refine ⟨41045983950944896341710989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54727978601259861788947985 41045983950944896341710989)
                  ·
                    refine ⟨15392243981604336128141621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41045983950944896341710989 15392243981604336128141621)
                    ·
                      refine ⟨1443022873275406512013277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15392243981604336128141621 1443022873275406512013277)
                      ·
                        rfl

theorem cell23_2810277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_2810277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810277 prefixEnd_2810277 := by exact prefixLift 2810277
  have htrace : WordTrace (prefixWord ++ tailWord_2810277) baseStart_2810277 baseEnd_2810277 := by
    simpa [prefixWord, tailWord_2810277, baseEnd_2810277] using wordTrace_append hprefix tailTrace_2810277
  have hstable : (prefixWord ++ tailWord_2810277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810277).length < 2 ^ (prefixWord ++ tailWord_2810277).sum := by decide
  have hdescent : baseEnd_2810277 < baseStart_2810277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810284 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_2810284 : Nat := 118140960795 + 2810284 * 2 ^ 59
def prefixEnd_2810284 : Nat := 4983230072969 + 3 ^ 40 * 2810284 * 2
def baseEnd_2810284 : Nat := 481008822546662661541915

theorem tailTrace_2810284 : CollatzResearch.WordTrace tailWord_2810284 prefixEnd_2810284 481008822546662661541915 := by
  unfold tailWord_2810284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51249739075414250570438953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68332985433885667427251937 51249739075414250570438953)
  ·
    refine ⟨38437304306560687927829215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51249739075414250570438953 38437304306560687927829215)
    ·
      refine ⟨57655956459841031891743823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38437304306560687927829215 57655956459841031891743823)
      ·
        refine ⟨86483934689761547837615735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57655956459841031891743823 86483934689761547837615735)
        ·
          refine ⟨129725902034642321756423603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86483934689761547837615735 129725902034642321756423603)
          ·
            refine ⟨194588853051963482634635405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129725902034642321756423603 194588853051963482634635405)
            ·
              refine ⟨72970819894486305987988277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194588853051963482634635405 72970819894486305987988277)
              ·
                refine ⟨6841014365108091186373901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72970819894486305987988277 6841014365108091186373901)
                ·
                  refine ⟨2565380386915534194890213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841014365108091186373901 2565380386915534194890213)
                  ·
                    refine ⟨481008822546662661541915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2565380386915534194890213 481008822546662661541915)
                    ·
                      rfl

theorem cell23_2810284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_2810284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810284 prefixEnd_2810284 := by exact prefixLift 2810284
  have htrace : WordTrace (prefixWord ++ tailWord_2810284) baseStart_2810284 baseEnd_2810284 := by
    simpa [prefixWord, tailWord_2810284, baseEnd_2810284] using wordTrace_append hprefix tailTrace_2810284
  have hstable : (prefixWord ++ tailWord_2810284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810284).length < 2 ^ (prefixWord ++ tailWord_2810284).sum := by decide
  have hdescent : baseEnd_2810284 < baseStart_2810284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810287 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_2810287 : Nat := 118140960795 + 2810287 * 2 ^ 59
def prefixEnd_2810287 : Nat := 4983230072969 + 3 ^ 40 * 2810287 * 2
def baseEnd_2810287 : Nat := 1443028008081951472888231

theorem tailTrace_2810287 : CollatzResearch.WordTrace tailWord_2810287 prefixEnd_2810287 1443028008081951472888231 := by
  unfold tailWord_2810287
  simp only [CollatzResearch.WordTrace]
  refine ⟨102499587569817632653237115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68333058379878421768824743 102499587569817632653237115)
  ·
    refine ⟨153749381354726448979855673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102499587569817632653237115 153749381354726448979855673)
    ·
      refine ⟨115312036016044836734891755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153749381354726448979855673 115312036016044836734891755)
      ·
        refine ⟨172968054024067255102337633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115312036016044836734891755 172968054024067255102337633)
        ·
          refine ⟨129726040518050441326753225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172968054024067255102337633 129726040518050441326753225)
          ·
            refine ⟨97294530388537830995064919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129726040518050441326753225 97294530388537830995064919)
            ·
              refine ⟨145941795582806746492597379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97294530388537830995064919 145941795582806746492597379)
              ·
                refine ⟨218912693374210119738896069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145941795582806746492597379 218912693374210119738896069)
                ·
                  refine ⟨41046130007664397451043013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218912693374210119738896069 41046130007664397451043013)
                  ·
                    refine ⟨7696149376437074522070565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41046130007664397451043013 7696149376437074522070565)
                    ·
                      refine ⟨1443028008081951472888231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7696149376437074522070565 1443028008081951472888231)
                      ·
                        rfl

theorem cell23_2810287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_2810287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810287 prefixEnd_2810287 := by exact prefixLift 2810287
  have htrace : WordTrace (prefixWord ++ tailWord_2810287) baseStart_2810287 baseEnd_2810287 := by
    simpa [prefixWord, tailWord_2810287, baseEnd_2810287] using wordTrace_append hprefix tailTrace_2810287
  have hstable : (prefixWord ++ tailWord_2810287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810287).length < 2 ^ (prefixWord ++ tailWord_2810287).sum := by decide
  have hdescent : baseEnd_2810287 < baseStart_2810287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810301 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2810301 : Nat := 118140960795 + 2810301 * 2 ^ 59
def prefixEnd_2810301 : Nat := 4983230072969 + 3 ^ 40 * 2810301 * 2
def baseEnd_2810301 : Nat := 481011732270371472704389

theorem tailTrace_2810301 : CollatzResearch.WordTrace tailWord_2810301 prefixEnd_2810301 481011732270371472704389 := by
  unfold tailWord_2810301
  simp only [CollatzResearch.WordTrace]
  refine ⟨102500098191766913044246757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68333398794511275362831171 102500098191766913044246757)
  ·
    refine ⟨19218768410956296195796267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102500098191766913044246757 19218768410956296195796267)
    ·
      refine ⟨28828152616434444293694401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19218768410956296195796267 28828152616434444293694401)
      ·
        refine ⟨21621114462325833220270801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28828152616434444293694401 21621114462325833220270801)
        ·
          refine ⟨16215835846744374915203101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21621114462325833220270801 16215835846744374915203101)
          ·
            refine ⟨6080938442529140593201163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16215835846744374915203101 6080938442529140593201163)
            ·
              refine ⟨9121407663793710889801745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080938442529140593201163 9121407663793710889801745)
              ·
                refine ⟨6841055747845283167351309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9121407663793710889801745 6841055747845283167351309)
                ·
                  refine ⟨2565395905441981187756741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841055747845283167351309 2565395905441981187756741)
                  ·
                    refine ⟨481011732270371472704389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2565395905441981187756741 481011732270371472704389)
                    ·
                      rfl

theorem cell23_2810301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2810301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810301 prefixEnd_2810301 := by exact prefixLift 2810301
  have htrace : WordTrace (prefixWord ++ tailWord_2810301) baseStart_2810301 baseEnd_2810301 := by
    simpa [prefixWord, tailWord_2810301, baseEnd_2810301] using wordTrace_append hprefix tailTrace_2810301
  have hstable : (prefixWord ++ tailWord_2810301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810301).length < 2 ^ (prefixWord ++ tailWord_2810301).sum := by decide
  have hdescent : baseEnd_2810301 < baseStart_2810301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810311 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_2810311 : Nat := 118140960795 + 2810311 * 2 ^ 59
def prefixEnd_2810311 : Nat := 4983230072969 + 3 ^ 40 * 2810311 * 2
def baseEnd_2810311 : Nat := 1443040331617659378988121

theorem tailTrace_2810311 : CollatzResearch.WordTrace tailWord_2810311 prefixEnd_2810311 1443040331617659378988121 := by
  unfold tailWord_2810311
  simp only [CollatzResearch.WordTrace]
  refine ⟨102500462921730684752110787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68333641947820456501407191 102500462921730684752110787)
  ·
    refine ⟨153750694382596027128166181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102500462921730684752110787 153750694382596027128166181)
    ·
      refine ⟨28828255196736755086531159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153750694382596027128166181 28828255196736755086531159)
      ·
        refine ⟨43242382795105132629796739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28828255196736755086531159 43242382795105132629796739)
        ·
          refine ⟨64863574192657698944695109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43242382795105132629796739 64863574192657698944695109)
          ·
            refine ⟨12161920161123318552130333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64863574192657698944695109 12161920161123318552130333)
            ·
              refine ⟨4560720060421244457048875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12161920161123318552130333 4560720060421244457048875)
              ·
                refine ⟨6841080090631866685573313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4560720060421244457048875 6841080090631866685573313)
                ·
                  refine ⟨5130810067973900014179985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6841080090631866685573313 5130810067973900014179985)
                  ·
                    refine ⟨3848107550980425010634989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5130810067973900014179985 3848107550980425010634989)
                    ·
                      refine ⟨1443040331617659378988121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848107550980425010634989 1443040331617659378988121)
                      ·
                        rfl

theorem cell23_2810311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_2810311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810311 prefixEnd_2810311 := by exact prefixLift 2810311
  have htrace : WordTrace (prefixWord ++ tailWord_2810311) baseStart_2810311 baseEnd_2810311 := by
    simpa [prefixWord, tailWord_2810311, baseEnd_2810311] using wordTrace_append hprefix tailTrace_2810311
  have hstable : (prefixWord ++ tailWord_2810311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810311).length < 2 ^ (prefixWord ++ tailWord_2810311).sum := by decide
  have hdescent : baseEnd_2810311 < baseStart_2810311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810358 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2810358 : Nat := 118140960795 + 2810358 * 2 ^ 59
def prefixEnd_2810358 : Nat := 4983230072969 + 3 ^ 40 * 2810358 * 2
def baseEnd_2810358 : Nat := 1443064465208420695100405

theorem tailTrace_2810358 : CollatzResearch.WordTrace tailWord_2810358 prefixEnd_2810358 1443064465208420695100405 := by
  unfold tailWord_2810358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406386072035025736191983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68334784768373607852714485 6406386072035025736191983)
  ·
    refine ⟨9609579108052538604287975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6406386072035025736191983 9609579108052538604287975)
    ·
      refine ⟨14414368662078807906431963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9609579108052538604287975 14414368662078807906431963)
      ·
        refine ⟨21621552993118211859647945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14414368662078807906431963 21621552993118211859647945)
        ·
          refine ⟨16216164744838658894735959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21621552993118211859647945 16216164744838658894735959)
          ·
            refine ⟨24324247117257988342103939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16216164744838658894735959 24324247117257988342103939)
            ·
              refine ⟨36486370675886982513155909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24324247117257988342103939 36486370675886982513155909)
              ·
                refine ⟨6841194501728809221216733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36486370675886982513155909 6841194501728809221216733)
                ·
                  refine ⟨2565447938148303457956275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841194501728809221216733 2565447938148303457956275)
                  ·
                    refine ⟨3848171907222455186934413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565447938148303457956275 3848171907222455186934413)
                    ·
                      refine ⟨1443064465208420695100405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848171907222455186934413 1443064465208420695100405)
                      ·
                        rfl

theorem cell23_2810358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2810358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810358 prefixEnd_2810358 := by exact prefixLift 2810358
  have htrace : WordTrace (prefixWord ++ tailWord_2810358) baseStart_2810358 baseEnd_2810358 := by
    simpa [prefixWord, tailWord_2810358, baseEnd_2810358] using wordTrace_append hprefix tailTrace_2810358
  have hstable : (prefixWord ++ tailWord_2810358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810358).length < 2 ^ (prefixWord ++ tailWord_2810358).sum := by decide
  have hdescent : baseEnd_2810358 < baseStart_2810358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810392 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_2810392 : Nat := 118140960795 + 2810392 * 2 ^ 59
def prefixEnd_2810392 : Nat := 4983230072969 + 3 ^ 40 * 2810392 * 2
def baseEnd_2810392 : Nat := 1443081923550673562075249

theorem tailTrace_2810392 : CollatzResearch.WordTrace tailWord_2810392 prefixEnd_2810392 1443081923550673562075249 := by
  unfold tailWord_2810392
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251708617218617792904715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68335611489624823723872953 51251708617218617792904715)
  ·
    refine ⟨76877562925827926689357073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51251708617218617792904715 76877562925827926689357073)
    ·
      refine ⟨57658172194370945017017805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76877562925827926689357073 57658172194370945017017805)
      ·
        refine ⟨21621814572889104381381677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57658172194370945017017805 21621814572889104381381677)
        ·
          refine ⟨8108180464833414143018129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21621814572889104381381677 8108180464833414143018129)
          ·
            refine ⟨6081135348625060607263597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8108180464833414143018129 6081135348625060607263597)
            ·
              refine ⟨2280425755734397727723849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6081135348625060607263597 2280425755734397727723849)
              ·
                refine ⟨1710319316800798295792887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280425755734397727723849 1710319316800798295792887)
                ·
                  refine ⟨2565478975201197443689331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710319316800798295792887 2565478975201197443689331)
                  ·
                    refine ⟨3848218462801796165533997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565478975201197443689331 3848218462801796165533997)
                    ·
                      refine ⟨1443081923550673562075249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848218462801796165533997 1443081923550673562075249)
                      ·
                        rfl

theorem cell23_2810392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_2810392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810392 prefixEnd_2810392 := by exact prefixLift 2810392
  have htrace : WordTrace (prefixWord ++ tailWord_2810392) baseStart_2810392 baseEnd_2810392 := by
    simpa [prefixWord, tailWord_2810392, baseEnd_2810392] using wordTrace_append hprefix tailTrace_2810392
  have hstable : (prefixWord ++ tailWord_2810392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810392).length < 2 ^ (prefixWord ++ tailWord_2810392).sum := by decide
  have hdescent : baseEnd_2810392 < baseStart_2810392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810394 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_2810394 : Nat := 118140960795 + 2810394 * 2 ^ 59
def prefixEnd_2810394 : Nat := 4983230072969 + 3 ^ 40 * 2810394 * 2
def baseEnd_2810394 : Nat := 1443082950511982554250239

theorem tailTrace_2810394 : CollatzResearch.WordTrace tailWord_2810394 prefixEnd_2810394 1443082950511982554250239 := by
  unfold tailWord_2810394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25625872545107497481845559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68335660120286659951588157 25625872545107497481845559)
  ·
    refine ⟨38438808817661246222768339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25625872545107497481845559 38438808817661246222768339)
    ·
      refine ⟨57658213226491869334152509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38438808817661246222768339 57658213226491869334152509)
      ·
        refine ⟨21621829959934451000307191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57658213226491869334152509 21621829959934451000307191)
        ·
          refine ⟨32432744939901676500460787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21621829959934451000307191 32432744939901676500460787)
          ·
            refine ⟨48649117409852514750691181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32432744939901676500460787 48649117409852514750691181)
            ·
              refine ⟨18243419028694693031509193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48649117409852514750691181 18243419028694693031509193)
              ·
                refine ⟨13682564271521019773631895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18243419028694693031509193 13682564271521019773631895)
                ·
                  refine ⟨20523846407281529660447843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13682564271521019773631895 20523846407281529660447843)
                  ·
                    refine ⟨30785769610922294490671765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20523846407281529660447843 30785769610922294490671765)
                    ·
                      refine ⟨1443082950511982554250239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30785769610922294490671765 1443082950511982554250239)
                      ·
                        rfl

theorem cell23_2810394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_2810394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810394 prefixEnd_2810394 := by exact prefixLift 2810394
  have htrace : WordTrace (prefixWord ++ tailWord_2810394) baseStart_2810394 baseEnd_2810394 := by
    simpa [prefixWord, tailWord_2810394, baseEnd_2810394] using wordTrace_append hprefix tailTrace_2810394
  have hstable : (prefixWord ++ tailWord_2810394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810394).length < 2 ^ (prefixWord ++ tailWord_2810394).sum := by decide
  have hdescent : baseEnd_2810394 < baseStart_2810394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810401 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2810401 : Nat := 118140960795 + 2810401 * 2 ^ 59
def prefixEnd_2810401 : Nat := 4983230072969 + 3 ^ 40 * 2810401 * 2
def baseEnd_2810401 : Nat := 1443086544876564026862707

theorem tailTrace_2810401 : CollatzResearch.WordTrace tailWord_2810401 prefixEnd_2810401 1443086544876564026862707 := by
  unfold tailWord_2810401
  simp only [CollatzResearch.WordTrace]
  refine ⟨102503745491404630122887057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68335830327603086748591371 102503745491404630122887057)
  ·
    refine ⟨76877809118553472592165293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102503745491404630122887057 76877809118553472592165293)
    ·
      refine ⟨28829178419457552222061985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76877809118553472592165293 28829178419457552222061985)
      ·
        refine ⟨21621883814593164166546489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28829178419457552222061985 21621883814593164166546489)
        ·
          refine ⟨16216412860944873124909867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21621883814593164166546489 16216412860944873124909867)
          ·
            refine ⟨24324619291417309687364801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16216412860944873124909867 24324619291417309687364801)
            ·
              refine ⟨18243464468562982265523601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24324619291417309687364801 18243464468562982265523601)
              ·
                refine ⟨13682598351422236699142701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18243464468562982265523601 13682598351422236699142701)
                ·
                  refine ⟨5130974381783338762178513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13682598351422236699142701 5130974381783338762178513)
                  ·
                    refine ⟨3848230786337504071633885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5130974381783338762178513 3848230786337504071633885)
                    ·
                      refine ⟨1443086544876564026862707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848230786337504071633885 1443086544876564026862707)
                      ·
                        rfl

theorem cell23_2810401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2810401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810401 prefixEnd_2810401 := by exact prefixLift 2810401
  have htrace : WordTrace (prefixWord ++ tailWord_2810401) baseStart_2810401 baseEnd_2810401 := by
    simpa [prefixWord, tailWord_2810401, baseEnd_2810401] using wordTrace_append hprefix tailTrace_2810401
  have hstable : (prefixWord ++ tailWord_2810401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810401).length < 2 ^ (prefixWord ++ tailWord_2810401).sum := by decide
  have hdescent : baseEnd_2810401 < baseStart_2810401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810418 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_2810418 : Nat := 118140960795 + 2810418 * 2 ^ 59
def prefixEnd_2810418 : Nat := 4983230072969 + 3 ^ 40 * 2810418 * 2
def baseEnd_2810418 : Nat := 1443095274047690460350129

theorem tailTrace_2810418 : CollatzResearch.WordTrace tailWord_2810418 prefixEnd_2810418 1443095274047690460350129 := by
  unfold tailWord_2810418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626091383085760506563977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68336243688228694684170605 25626091383085760506563977)
  ·
    refine ⟨19219568537314320379922983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25626091383085760506563977 19219568537314320379922983)
    ·
      refine ⟨28829352805971480569884475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19219568537314320379922983 28829352805971480569884475)
      ·
        refine ⟨43244029208957220854826713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28829352805971480569884475 43244029208957220854826713)
        ·
          refine ⟨32433021906717915641120035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43244029208957220854826713 32433021906717915641120035)
          ·
            refine ⟨48649532860076873461680053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32433021906717915641120035 48649532860076873461680053)
            ·
              refine ⟨4560893705632206887032505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48649532860076873461680053 4560893705632206887032505)
              ·
                refine ⟨3420670279224155165274379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560893705632206887032505 3420670279224155165274379)
                ·
                  refine ⟨5131005418836232747911569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420670279224155165274379 5131005418836232747911569)
                  ·
                    refine ⟨3848254064127174560933677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5131005418836232747911569 3848254064127174560933677)
                    ·
                      refine ⟨1443095274047690460350129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848254064127174560933677 1443095274047690460350129)
                      ·
                        rfl

theorem cell23_2810418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_2810418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810418 prefixEnd_2810418 := by exact prefixLift 2810418
  have htrace : WordTrace (prefixWord ++ tailWord_2810418) baseStart_2810418 baseEnd_2810418 := by
    simpa [prefixWord, tailWord_2810418, baseEnd_2810418] using wordTrace_append hprefix tailTrace_2810418
  have hstable : (prefixWord ++ tailWord_2810418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810418).length < 2 ^ (prefixWord ++ tailWord_2810418).sum := by decide
  have hdescent : baseEnd_2810418 < baseStart_2810418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810431 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_2810431 : Nat := 118140960795 + 2810431 * 2 ^ 59
def prefixEnd_2810431 : Nat := 4983230072969 + 3 ^ 40 * 2810431 * 2
def baseEnd_2810431 : Nat := 1443101949296198909487569

theorem tailTrace_2810431 : CollatzResearch.WordTrace tailWord_2810431 prefixEnd_2810431 1443101949296198909487569 := by
  unfold tailWord_2810431
  simp only [CollatzResearch.WordTrace]
  refine ⟨102504839681295945246479147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68336559787530630164319431 102504839681295945246479147)
  ·
    refine ⟨153757259521943917869718721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102504839681295945246479147 153757259521943917869718721)
    ·
      refine ⟨115317944641457938402289041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153757259521943917869718721 115317944641457938402289041)
      ·
        refine ⟨86488458481093453801716781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115317944641457938402289041 86488458481093453801716781)
        ·
          refine ⟨32433171930410045175643793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86488458481093453801716781 32433171930410045175643793)
          ·
            refine ⟨24324878947807533881732845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32433171930410045175643793 24324878947807533881732845)
            ·
              refine ⟨9121829605427825205649817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24324878947807533881732845 9121829605427825205649817)
              ·
                refine ⟨6841372204070868904237363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9121829605427825205649817 6841372204070868904237363)
                ·
                  refine ⟨10262058306106303356356045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841372204070868904237363 10262058306106303356356045)
                  ·
                    refine ⟨3848271864789863758633517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10262058306106303356356045 3848271864789863758633517)
                    ·
                      refine ⟨1443101949296198909487569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848271864789863758633517 1443101949296198909487569)
                      ·
                        rfl

theorem cell23_2810431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_2810431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810431 prefixEnd_2810431 := by exact prefixLift 2810431
  have htrace : WordTrace (prefixWord ++ tailWord_2810431) baseStart_2810431 baseEnd_2810431 := by
    simpa [prefixWord, tailWord_2810431, baseEnd_2810431] using wordTrace_append hprefix tailTrace_2810431
  have hstable : (prefixWord ++ tailWord_2810431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810431).length < 2 ^ (prefixWord ++ tailWord_2810431).sum := by decide
  have hdescent : baseEnd_2810431 < baseStart_2810431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810449 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_2810449 : Nat := 118140960795 + 2810449 * 2 ^ 59
def prefixEnd_2810449 : Nat := 4983230072969 + 3 ^ 40 * 2810449 * 2
def baseEnd_2810449 : Nat := 1443111191947979839062487

theorem tailTrace_2810449 : CollatzResearch.WordTrace tailWord_2810449 prefixEnd_2810449 1443111191947979839062487 := by
  unfold tailWord_2810449
  simp only [CollatzResearch.WordTrace]
  refine ⟨102505496195230734320634401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68336997463487156213756267 102505496195230734320634401)
  ·
    refine ⟨76879122146423050740475801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102505496195230734320634401 76879122146423050740475801)
    ·
      refine ⟨57659341609817288055356851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76879122146423050740475801 57659341609817288055356851)
      ·
        refine ⟨86489012414725932083035277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57659341609817288055356851 86489012414725932083035277)
        ·
          refine ⟨32433379655522224531138229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86489012414725932083035277 32433379655522224531138229)
          ·
            refine ⟨3040629342705208549794209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32433379655522224531138229 3040629342705208549794209)
            ·
              refine ⟨2280472007028906412345657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040629342705208549794209 2280472007028906412345657)
              ·
                refine ⟨1710354005271679809259243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280472007028906412345657 1710354005271679809259243)
                ·
                  refine ⟨2565531007907519713888865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710354005271679809259243 2565531007907519713888865)
                  ·
                    refine ⟨1924148255930639785416649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565531007907519713888865 1924148255930639785416649)
                    ·
                      refine ⟨1443111191947979839062487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924148255930639785416649 1443111191947979839062487)
                      ·
                        rfl

theorem cell23_2810449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_2810449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810449 prefixEnd_2810449 := by exact prefixLift 2810449
  have htrace : WordTrace (prefixWord ++ tailWord_2810449) baseStart_2810449 baseEnd_2810449 := by
    simpa [prefixWord, tailWord_2810449, baseEnd_2810449] using wordTrace_append hprefix tailTrace_2810449
  have hstable : (prefixWord ++ tailWord_2810449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810449).length < 2 ^ (prefixWord ++ tailWord_2810449).sum := by decide
  have hdescent : baseEnd_2810449 < baseStart_2810449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810464 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_2810464 : Nat := 118140960795 + 2810464 * 2 ^ 59
def prefixEnd_2810464 : Nat := 4983230072969 + 3 ^ 40 * 2810464 * 2
def baseEnd_2810464 : Nat := 481039631385932426791639

theorem tailTrace_2810464 : CollatzResearch.WordTrace tailWord_2810464 prefixEnd_2810464 481039631385932426791639 := by
  unfold tailWord_2810464
  simp only [CollatzResearch.WordTrace]
  refine ⟨51253021645088195941215223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68337362193450927921620297 51253021645088195941215223)
  ·
    refine ⟨76879532467632293911822835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51253021645088195941215223 76879532467632293911822835)
    ·
      refine ⟨115319298701448440867734253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76879532467632293911822835 115319298701448440867734253)
      ·
        refine ⟨43244737013043165325400345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115319298701448440867734253 43244737013043165325400345)
        ·
          refine ⟨32433552759782373994050259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43244737013043165325400345 32433552759782373994050259)
          ·
            refine ⟨48650329139673560991075389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32433552759782373994050259 48650329139673560991075389)
            ·
              refine ⟨18243873427377585371653271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48650329139673560991075389 18243873427377585371653271)
              ·
                refine ⟨27365810141066378057479907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18243873427377585371653271 27365810141066378057479907)
                ·
                  refine ⟨41048715211599567086219861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27365810141066378057479907 41048715211599567086219861)
                  ·
                    refine ⟨481039631385932426791639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41048715211599567086219861 481039631385932426791639)
                    ·
                      rfl

theorem cell23_2810464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_2810464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810464 prefixEnd_2810464 := by exact prefixLift 2810464
  have htrace : WordTrace (prefixWord ++ tailWord_2810464) baseStart_2810464 baseEnd_2810464 := by
    simpa [prefixWord, tailWord_2810464, baseEnd_2810464] using wordTrace_append hprefix tailTrace_2810464
  have hstable : (prefixWord ++ tailWord_2810464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810464).length < 2 ^ (prefixWord ++ tailWord_2810464).sum := by decide
  have hdescent : baseEnd_2810464 < baseStart_2810464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810488 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_2810488 : Nat := 118140960795 + 2810488 * 2 ^ 59
def prefixEnd_2810488 : Nat := 4983230072969 + 3 ^ 40 * 2810488 * 2
def baseEnd_2810488 : Nat := 1443131217693505186474807

theorem tailTrace_2810488 : CollatzResearch.WordTrace tailWord_2810488 prefixEnd_2810488 1443131217693505186474807 := by
  unfold tailWord_2810488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51253459321044721990652059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68337945761392962654202745 51253459321044721990652059)
  ·
    refine ⟨76880188981567082985978089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51253459321044721990652059 76880188981567082985978089)
    ·
      refine ⟨57660141736175312239483567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76880188981567082985978089 57660141736175312239483567)
      ·
        refine ⟨86490212604262968359225351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57660141736175312239483567 86490212604262968359225351)
        ·
          refine ⟨129735318906394452538838027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86490212604262968359225351 129735318906394452538838027)
          ·
            refine ⟨194602978359591678808257041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129735318906394452538838027 194602978359591678808257041)
            ·
              refine ⟨145952233769693759106192781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194602978359591678808257041 145952233769693759106192781)
              ·
                refine ⟨54732087663635159664822293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145952233769693759106192781 54732087663635159664822293)
                ·
                  refine ⟨2565566609232898109288545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54732087663635159664822293 2565566609232898109288545)
                  ·
                    refine ⟨1924174956924673581966409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565566609232898109288545 1924174956924673581966409)
                    ·
                      refine ⟨1443131217693505186474807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924174956924673581966409 1443131217693505186474807)
                      ·
                        rfl

theorem cell23_2810488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_2810488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810488 prefixEnd_2810488 := by exact prefixLift 2810488
  have htrace : WordTrace (prefixWord ++ tailWord_2810488) baseStart_2810488 baseEnd_2810488 := by
    simpa [prefixWord, tailWord_2810488, baseEnd_2810488] using wordTrace_append hprefix tailTrace_2810488
  have hstable : (prefixWord ++ tailWord_2810488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810488).length < 2 ^ (prefixWord ++ tailWord_2810488).sum := by decide
  have hdescent : baseEnd_2810488 < baseStart_2810488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810501 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_2810501 : Nat := 118140960795 + 2810501 * 2 ^ 59
def prefixEnd_2810501 : Nat := 4983230072969 + 3 ^ 40 * 2810501 * 2
def baseEnd_2810501 : Nat := 1443137892942013635612247

theorem tailTrace_2810501 : CollatzResearch.WordTrace tailWord_2810501 prefixEnd_2810501 1443137892942013635612247 := by
  unfold tailWord_2810501
  simp only [CollatzResearch.WordTrace]
  refine ⟨102507392791042347201527357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68338261860694898134351571 102507392791042347201527357)
  ·
    refine ⟨38440272296640880200572759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102507392791042347201527357 38440272296640880200572759)
    ·
      refine ⟨57660408444961320300859139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38440272296640880200572759 57660408444961320300859139)
      ·
        refine ⟨86490612667441980451288709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57660408444961320300859139 86490612667441980451288709)
        ·
          refine ⟨16216989875145371334616633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86490612667441980451288709 16216989875145371334616633)
          ·
            refine ⟨12162742406359028500962475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16216989875145371334616633 12162742406359028500962475)
            ·
              refine ⟨18244113609538542751443713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12162742406359028500962475 18244113609538542751443713)
              ·
                refine ⟨13683085207153907063582785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18244113609538542751443713 13683085207153907063582785)
                ·
                  refine ⟨10262313905365430297687089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13683085207153907063582785 10262313905365430297687089)
                  ·
                    refine ⟨7696735429024072723265317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10262313905365430297687089 7696735429024072723265317)
                    ·
                      refine ⟨1443137892942013635612247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7696735429024072723265317 1443137892942013635612247)
                      ·
                        rfl

theorem cell23_2810501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_2810501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810501 prefixEnd_2810501 := by exact prefixLift 2810501
  have htrace : WordTrace (prefixWord ++ tailWord_2810501) baseStart_2810501 baseEnd_2810501 := by
    simpa [prefixWord, tailWord_2810501, baseEnd_2810501] using wordTrace_append hprefix tailTrace_2810501
  have hstable : (prefixWord ++ tailWord_2810501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810501).length < 2 ^ (prefixWord ++ tailWord_2810501).sum := by decide
  have hdescent : baseEnd_2810501 < baseStart_2810501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810521 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2810521 : Nat := 118140960795 + 2810521 * 2 ^ 59
def prefixEnd_2810521 : Nat := 4983230072969 + 3 ^ 40 * 2810521 * 2
def baseEnd_2810521 : Nat := 1443148162555103557362155

theorem tailTrace_2810521 : CollatzResearch.WordTrace tailWord_2810521 prefixEnd_2810521 1443148162555103557362155 := by
  unfold tailWord_2810521
  simp only [CollatzResearch.WordTrace]
  refine ⟨102508122250969890617255417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68338748167313260411503611 102508122250969890617255417)
  ·
    refine ⟨76881091688227417962941563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102508122250969890617255417 76881091688227417962941563)
    ·
      refine ⟨115321637532341126944412345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76881091688227417962941563 115321637532341126944412345)
      ·
        refine ⟨86491228149255845208309259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115321637532341126944412345 86491228149255845208309259)
        ·
          refine ⟨129736842223883767812463889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86491228149255845208309259 129736842223883767812463889)
          ·
            refine ⟨97302631667912825859347917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129736842223883767812463889 97302631667912825859347917)
            ·
              refine ⟨36488486875467309697255469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97302631667912825859347917 36488486875467309697255469)
              ·
                refine ⟨13683182578300241136470801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36488486875467309697255469 13683182578300241136470801)
                ·
                  refine ⟨10262386933725180852353101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13683182578300241136470801 10262386933725180852353101)
                  ·
                    refine ⟨3848395100146942819632413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10262386933725180852353101 3848395100146942819632413)
                    ·
                      refine ⟨1443148162555103557362155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848395100146942819632413 1443148162555103557362155)
                      ·
                        rfl

theorem cell23_2810521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2810521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810521 prefixEnd_2810521 := by exact prefixLift 2810521
  have htrace : WordTrace (prefixWord ++ tailWord_2810521) baseStart_2810521 baseEnd_2810521 := by
    simpa [prefixWord, tailWord_2810521, baseEnd_2810521] using wordTrace_append hprefix tailTrace_2810521
  have hstable : (prefixWord ++ tailWord_2810521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810521).length < 2 ^ (prefixWord ++ tailWord_2810521).sum := by decide
  have hdescent : baseEnd_2810521 < baseStart_2810521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810558 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2810558 : Nat := 118140960795 + 2810558 * 2 ^ 59
def prefixEnd_2810558 : Nat := 4983230072969 + 3 ^ 40 * 2810558 * 2
def baseEnd_2810558 : Nat := 481055720446439970866495

theorem tailTrace_2810558 : CollatzResearch.WordTrace tailWord_2810558 prefixEnd_2810558 481055720446439970866495 := by
  unfold tailWord_2810558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813683968979480742044041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68339647834557230624234885 12813683968979480742044041)
  ·
    refine ⟨9610262976734610556533031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12813683968979480742044041 9610262976734610556533031)
    ·
      refine ⟨14415394465101915834799547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9610262976734610556533031 14415394465101915834799547)
      ·
        refine ⟨21623091697652873752199321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14415394465101915834799547 21623091697652873752199321)
        ·
          refine ⟨16217318773239655314149491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21623091697652873752199321 16217318773239655314149491)
          ·
            refine ⟨24325978159859482971224237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16217318773239655314149491 24325978159859482971224237)
            ·
              refine ⟨9122241809947306114209089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24325978159859482971224237 9122241809947306114209089)
              ·
                refine ⟨6841681357460479585656817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122241809947306114209089 6841681357460479585656817)
                ·
                  refine ⟨5131261018095359689242613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6841681357460479585656817 5131261018095359689242613)
                  ·
                    refine ⟨481055720446439970866495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5131261018095359689242613 481055720446439970866495)
                    ·
                      rfl

theorem cell23_2810558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2810558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810558 prefixEnd_2810558 := by exact prefixLift 2810558
  have htrace : WordTrace (prefixWord ++ tailWord_2810558) baseStart_2810558 baseEnd_2810558 := by
    simpa [prefixWord, tailWord_2810558, baseEnd_2810558] using wordTrace_append hprefix tailTrace_2810558
  have hstable : (prefixWord ++ tailWord_2810558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810558).length < 2 ^ (prefixWord ++ tailWord_2810558).sum := by decide
  have hdescent : baseEnd_2810558 < baseStart_2810558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810573 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2810573 : Nat := 118140960795 + 2810573 * 2 ^ 59
def prefixEnd_2810573 : Nat := 4983230072969 + 3 ^ 40 * 2810573 * 2
def baseEnd_2810573 : Nat := 1443174863549137353911917

theorem tailTrace_2810573 : CollatzResearch.WordTrace tailWord_2810573 prefixEnd_2810573 1443174863549137353911917 := by
  unfold tailWord_2810573
  simp only [CollatzResearch.WordTrace]
  refine ⟨102510018846781503498148373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68340012564521002332098915 102510018846781503498148373)
  ·
    refine ⟨4805157133442882976475705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102510018846781503498148373 4805157133442882976475705)
    ·
      refine ⟨3603867850082162232356779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4805157133442882976475705 3603867850082162232356779)
      ·
        refine ⟨5405801775123243348535169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3603867850082162232356779 5405801775123243348535169)
        ·
          refine ⟨4054351331342432511401377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5405801775123243348535169 4054351331342432511401377)
          ·
            refine ⟨3040763498506824383551033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054351331342432511401377 3040763498506824383551033)
            ·
              refine ⟨2280572623880118287663275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040763498506824383551033 2280572623880118287663275)
              ·
                refine ⟨3420858935820177431494913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280572623880118287663275 3420858935820177431494913)
                ·
                  refine ⟨2565644201865133073621185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420858935820177431494913 2565644201865133073621185)
                  ·
                    refine ⟨1924233151398849805215889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565644201865133073621185 1924233151398849805215889)
                    ·
                      refine ⟨1443174863549137353911917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924233151398849805215889 1443174863549137353911917)
                      ·
                        rfl

theorem cell23_2810573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2810573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810573 prefixEnd_2810573 := by exact prefixLift 2810573
  have htrace : WordTrace (prefixWord ++ tailWord_2810573) baseStart_2810573 baseEnd_2810573 := by
    simpa [prefixWord, tailWord_2810573, baseEnd_2810573] using wordTrace_append hprefix tailTrace_2810573
  have hstable : (prefixWord ++ tailWord_2810573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810573).length < 2 ^ (prefixWord ++ tailWord_2810573).sum := by decide
  have hdescent : baseEnd_2810573 < baseStart_2810573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810595 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2810595 : Nat := 118140960795 + 2810595 * 2 ^ 59
def prefixEnd_2810595 : Nat := 4983230072969 + 3 ^ 40 * 2810595 * 2
def baseEnd_2810595 : Nat := 1443186160123536267836815

theorem tailTrace_2810595 : CollatzResearch.WordTrace tailWord_2810595 prefixEnd_2810595 1443186160123536267836815 := by
  unfold tailWord_2810595
  simp only [CollatzResearch.WordTrace]
  refine ⟨102510821252701801255449239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68340547501801200836966159 102510821252701801255449239)
  ·
    refine ⟨153766231879052701883173859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102510821252701801255449239 153766231879052701883173859)
    ·
      refine ⟨230649347818579052824760789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153766231879052701883173859 230649347818579052824760789)
      ·
        refine ⟨5405844089497946550580331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 230649347818579052824760789 5405844089497946550580331)
        ·
          refine ⟨8108766134246919825870497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405844089497946550580331 8108766134246919825870497)
          ·
            refine ⟨6081574600685189869402873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8108766134246919825870497 6081574600685189869402873)
            ·
              refine ⟨4561180950513892402052155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081574600685189869402873 4561180950513892402052155)
              ·
                refine ⟨6841771425770838603078233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561180950513892402052155 6841771425770838603078233)
                ·
                  refine ⟨5131328569328128952308675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6841771425770838603078233 5131328569328128952308675)
                  ·
                    refine ⟨7696992853992193428463013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5131328569328128952308675 7696992853992193428463013)
                    ·
                      refine ⟨1443186160123536267836815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7696992853992193428463013 1443186160123536267836815)
                      ·
                        rfl

theorem cell23_2810595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2810595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810595 prefixEnd_2810595 := by exact prefixLift 2810595
  have htrace : WordTrace (prefixWord ++ tailWord_2810595) baseStart_2810595 baseEnd_2810595 := by
    simpa [prefixWord, tailWord_2810595, baseEnd_2810595] using wordTrace_append hprefix tailTrace_2810595
  have hstable : (prefixWord ++ tailWord_2810595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810595).length < 2 ^ (prefixWord ++ tailWord_2810595).sum := by decide
  have hdescent : baseEnd_2810595 < baseStart_2810595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810613 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 5]
def baseStart_2810613 : Nat := 118140960795 + 2810613 * 2 ^ 59
def prefixEnd_2810613 : Nat := 4983230072969 + 3 ^ 40 * 2810613 * 2
def baseEnd_2810613 : Nat := 160355044752813021934637

theorem tailTrace_2810613 : CollatzResearch.WordTrace tailWord_2810613 prefixEnd_2810613 160355044752813021934637 := by
  unfold tailWord_2810613
  simp only [CollatzResearch.WordTrace]
  refine ⟨102511477766636590329604493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68340985177757726886402995 102511477766636590329604493)
  ·
    refine ⟨38441804162488721373601685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102511477766636590329604493 38441804162488721373601685)
    ·
      refine ⟨1801959570116658814387579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38441804162488721373601685 1801959570116658814387579)
      ·
        refine ⟨2702939355174988221581369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801959570116658814387579 2702939355174988221581369)
        ·
          refine ⟨2027204516381241166186027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702939355174988221581369 2027204516381241166186027)
          ·
            refine ⟨3040806774571861749279041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027204516381241166186027 3040806774571861749279041)
            ·
              refine ⟨2280605080928896311959281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040806774571861749279041 2280605080928896311959281)
              ·
                refine ⟨1710453810696672233969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280605080928896311959281 1710453810696672233969461)
                ·
                  refine ⟨160355044752813021934637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710453810696672233969461 160355044752813021934637)
                  ·
                    rfl

theorem cell23_2810613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_2810613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810613 prefixEnd_2810613 := by exact prefixLift 2810613
  have htrace : WordTrace (prefixWord ++ tailWord_2810613) baseStart_2810613 baseEnd_2810613 := by
    simpa [prefixWord, tailWord_2810613, baseEnd_2810613] using wordTrace_append hprefix tailTrace_2810613
  have hstable : (prefixWord ++ tailWord_2810613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810613).length < 2 ^ (prefixWord ++ tailWord_2810613).sum := by decide
  have hdescent : baseEnd_2810613 < baseStart_2810613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810621 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2810621 : Nat := 118140960795 + 2810621 * 2 ^ 59
def prefixEnd_2810621 : Nat := 4983230072969 + 3 ^ 40 * 2810621 * 2
def baseEnd_2810621 : Nat := 1443199510620553166111695

theorem tailTrace_2810621 : CollatzResearch.WordTrace tailWord_2810621 prefixEnd_2810621 1443199510620553166111695 := by
  unfold tailWord_2810621
  simp only [CollatzResearch.WordTrace]
  refine ⟨102511769550607607695895717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68341179700405071797263811 102511769550607607695895717)
  ·
    refine ⟨19220956790738926442980447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102511769550607607695895717 19220956790738926442980447)
    ·
      refine ⟨28831435186108389664470671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19220956790738926442980447 28831435186108389664470671)
      ·
        refine ⟨43247152779162584496706007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28831435186108389664470671 43247152779162584496706007)
        ·
          refine ⟨64870729168743876745059011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43247152779162584496706007 64870729168743876745059011)
          ·
            refine ⟨97306093753115815117588517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64870729168743876745059011 97306093753115815117588517)
            ·
              refine ⟨18244892578709215334547847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97306093753115815117588517 18244892578709215334547847)
              ·
                refine ⟨27367338868063823001821771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18244892578709215334547847 27367338868063823001821771)
                ·
                  refine ⟨41051008302095734502732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27367338868063823001821771 41051008302095734502732657)
                  ·
                    refine ⟨30788256226571800877049493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41051008302095734502732657 30788256226571800877049493)
                    ·
                      refine ⟨1443199510620553166111695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30788256226571800877049493 1443199510620553166111695)
                      ·
                        rfl

theorem cell23_2810621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2810621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810621 prefixEnd_2810621 := by exact prefixLift 2810621
  have htrace : WordTrace (prefixWord ++ tailWord_2810621) baseStart_2810621 baseEnd_2810621 := by
    simpa [prefixWord, tailWord_2810621, baseEnd_2810621] using wordTrace_append hprefix tailTrace_2810621
  have hstable : (prefixWord ++ tailWord_2810621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810621).length < 2 ^ (prefixWord ++ tailWord_2810621).sum := by decide
  have hdescent : baseEnd_2810621 < baseStart_2810621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810645 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_2810645 : Nat := 118140960795 + 2810645 * 2 ^ 59
def prefixEnd_2810645 : Nat := 4983230072969 + 3 ^ 40 * 2810645 * 2
def baseEnd_2810645 : Nat := 1443211834156261072211585

theorem tailTrace_2810645 : CollatzResearch.WordTrace tailWord_2810645 prefixEnd_2810645 1443211834156261072211585 := by
  unfold tailWord_2810645
  simp only [CollatzResearch.WordTrace]
  refine ⟨102512644902520659794769389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68341763268347106529846259 102512644902520659794769389)
  ·
    refine ⟨38442241838445247423038521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102512644902520659794769389 38442241838445247423038521)
    ·
      refine ⟨28831681378833935567278891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38442241838445247423038521 28831681378833935567278891)
      ·
        refine ⟨43247522068250903350918337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28831681378833935567278891 43247522068250903350918337)
        ·
          refine ⟨32435641551188177513188753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43247522068250903350918337 32435641551188177513188753)
          ·
            refine ⟨24326731163391133134891565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32435641551188177513188753 24326731163391133134891565)
            ·
              refine ⟨9122524186271674925584337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24326731163391133134891565 9122524186271674925584337)
              ·
                refine ⟨6841893139703756194188253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122524186271674925584337 6841893139703756194188253)
                ·
                  refine ⟨2565709927388908572820595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841893139703756194188253 2565709927388908572820595)
                  ·
                    refine ⟨3848564891083362859230893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565709927388908572820595 3848564891083362859230893)
                    ·
                      refine ⟨1443211834156261072211585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848564891083362859230893 1443211834156261072211585)
                      ·
                        rfl

theorem cell23_2810645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_2810645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810645 prefixEnd_2810645 := by exact prefixLift 2810645
  have htrace : WordTrace (prefixWord ++ tailWord_2810645) baseStart_2810645 baseEnd_2810645 := by
    simpa [prefixWord, tailWord_2810645, baseEnd_2810645] using wordTrace_append hprefix tailTrace_2810645
  have hstable : (prefixWord ++ tailWord_2810645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810645).length < 2 ^ (prefixWord ++ tailWord_2810645).sum := by decide
  have hdescent : baseEnd_2810645 < baseStart_2810645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810648 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_2810648 : Nat := 118140960795 + 2810648 * 2 ^ 59
def prefixEnd_2810648 : Nat := 4983230072969 + 3 ^ 40 * 2810648 * 2
def baseEnd_2810648 : Nat := 481071124866074853491357

theorem tailTrace_2810648 : CollatzResearch.WordTrace tailWord_2810648 prefixEnd_2810648 481071124866074853491357 := by
  unfold tailWord_2810648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51256377160754895653564299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68341836214339860871419065 51256377160754895653564299)
  ·
    refine ⟨76884565741132343480346449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51256377160754895653564299 76884565741132343480346449)
    ·
      refine ⟨57663424305849257610259837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76884565741132343480346449 57663424305849257610259837)
      ·
        refine ⟨21623784114693471603847439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57663424305849257610259837 21623784114693471603847439)
        ·
          refine ⟨32435676172040207405771159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21623784114693471603847439 32435676172040207405771159)
          ·
            refine ⟨48653514258060311108656739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32435676172040207405771159 48653514258060311108656739)
            ·
              refine ⟨72980271387090466662985109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48653514258060311108656739 72980271387090466662985109)
              ·
                refine ⟨3420950221269865624827427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72980271387090466662985109 3420950221269865624827427)
                ·
                  refine ⟨5131425331904798437241141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420950221269865624827427 5131425331904798437241141)
                  ·
                    refine ⟨481071124866074853491357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5131425331904798437241141 481071124866074853491357)
                    ·
                      rfl

theorem cell23_2810648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_2810648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810648 prefixEnd_2810648 := by exact prefixLift 2810648
  have htrace : WordTrace (prefixWord ++ tailWord_2810648) baseStart_2810648 baseEnd_2810648 := by
    simpa [prefixWord, tailWord_2810648, baseEnd_2810648] using wordTrace_append hprefix tailTrace_2810648
  have hstable : (prefixWord ++ tailWord_2810648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810648).length < 2 ^ (prefixWord ++ tailWord_2810648).sum := by decide
  have hdescent : baseEnd_2810648 < baseStart_2810648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810655 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 5, 2]
def baseStart_2810655 : Nat := 118140960795 + 2810655 * 2 ^ 59
def prefixEnd_2810655 : Nat := 4983230072969 + 3 ^ 40 * 2810655 * 2
def baseEnd_2810655 : Nat := 1443216968962806033086539

theorem tailTrace_2810655 : CollatzResearch.WordTrace tailWord_2810655 prefixEnd_2810655 1443216968962806033086539 := by
  unfold tailWord_2810655
  simp only [CollatzResearch.WordTrace]
  refine ⟨102513009632484431502633419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68342006421656287668422279 102513009632484431502633419)
  ·
    refine ⟨153769514448726647253950129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102513009632484431502633419 153769514448726647253950129)
    ·
      refine ⟨115327135836544985440462597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153769514448726647253950129 115327135836544985440462597)
      ·
        refine ⟨21623837969352184770086737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115327135836544985440462597 21623837969352184770086737)
        ·
          refine ⟨16217878477014138577565053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21623837969352184770086737 16217878477014138577565053)
          ·
            refine ⟨6081704428880301966586895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16217878477014138577565053 6081704428880301966586895)
            ·
              refine ⟨9122556643320452949880343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081704428880301966586895 9122556643320452949880343)
              ·
                refine ⟨13683834964980679424820515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9122556643320452949880343 13683834964980679424820515)
                ·
                  refine ⟨20525752447471019137230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13683834964980679424820515 20525752447471019137230773)
                  ·
                    refine ⟨1924289291950408044115385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20525752447471019137230773 1924289291950408044115385)
                    ·
                      refine ⟨1443216968962806033086539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924289291950408044115385 1443216968962806033086539)
                      ·
                        rfl

theorem cell23_2810655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_2810655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810655 prefixEnd_2810655 := by exact prefixLift 2810655
  have htrace : WordTrace (prefixWord ++ tailWord_2810655) baseStart_2810655 baseEnd_2810655 := by
    simpa [prefixWord, tailWord_2810655, baseEnd_2810655] using wordTrace_append hprefix tailTrace_2810655
  have hstable : (prefixWord ++ tailWord_2810655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810655).length < 2 ^ (prefixWord ++ tailWord_2810655).sum := by decide
  have hdescent : baseEnd_2810655 < baseStart_2810655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810669 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2810669 : Nat := 118140960795 + 2810669 * 2 ^ 59
def prefixEnd_2810669 : Nat := 4983230072969 + 3 ^ 40 * 2810669 * 2
def baseEnd_2810669 : Nat := 160358239743552108701275

theorem tailTrace_2810669 : CollatzResearch.WordTrace tailWord_2810669 prefixEnd_2810669 160358239743552108701275 := by
  unfold tailWord_2810669
  simp only [CollatzResearch.WordTrace]
  refine ⟨102513520254433711893643061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68342346836289141262428707 102513520254433711893643061)
  ·
    refine ⟨9610642523853160490029037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102513520254433711893643061 9610642523853160490029037)
    ·
      refine ⟨3603990946444935183760889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9610642523853160490029037 3603990946444935183760889)
      ·
        refine ⟨2702993209833701387820667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3603990946444935183760889 2702993209833701387820667)
        ·
          refine ⟨4054489814750552081731001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702993209833701387820667 4054489814750552081731001)
          ·
            refine ⟨3040867361062914061298251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054489814750552081731001 3040867361062914061298251)
            ·
              refine ⟨4561301041594371091947377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040867361062914061298251 4561301041594371091947377)
              ·
                refine ⟨3420975781195778318960533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4561301041594371091947377 3420975781195778318960533)
                ·
                  refine ⟨160358239743552108701275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3420975781195778318960533 160358239743552108701275)
                  ·
                    rfl

theorem cell23_2810669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2810669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810669 prefixEnd_2810669 := by exact prefixLift 2810669
  have htrace : WordTrace (prefixWord ++ tailWord_2810669) baseStart_2810669 baseEnd_2810669 := by
    simpa [prefixWord, tailWord_2810669, baseEnd_2810669] using wordTrace_append hprefix tailTrace_2810669
  have hstable : (prefixWord ++ tailWord_2810669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810669).length < 2 ^ (prefixWord ++ tailWord_2810669).sum := by decide
  have hdescent : baseEnd_2810669 < baseStart_2810669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810688 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_2810688 : Nat := 118140960795 + 2810688 * 2 ^ 59
def prefixEnd_2810688 : Nat := 4983230072969 + 3 ^ 40 * 2810688 * 2
def baseEnd_2810688 : Nat := 1443233913824404403973887

theorem tailTrace_2810688 : CollatzResearch.WordTrace tailWord_2810688 prefixEnd_2810688 1443233913824404403973887 := by
  unfold tailWord_2810688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51257106620682439069292359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68342808827576585425723145 51257106620682439069292359)
  ·
    refine ⟨76885659931023658603938539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51257106620682439069292359 76885659931023658603938539)
    ·
      refine ⟨115328489896535487905907809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76885659931023658603938539 115328489896535487905907809)
      ·
        refine ⟨86496367422401615929430857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115328489896535487905907809 86496367422401615929430857)
        ·
          refine ⟨64872275566801211947073143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86496367422401615929430857 64872275566801211947073143)
          ·
            refine ⟨97308413350201817920609715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64872275566801211947073143 97308413350201817920609715)
            ·
              refine ⟨145962620025302726880914573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97308413350201817920609715 145962620025302726880914573)
              ·
                refine ⟨54735982509488522580342965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145962620025302726880914573 54735982509488522580342965)
                ·
                  refine ⟨5131498360264548991907153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54735982509488522580342965 5131498360264548991907153)
                  ·
                    refine ⟨3848623770198411743930365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5131498360264548991907153 3848623770198411743930365)
                    ·
                      refine ⟨1443233913824404403973887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848623770198411743930365 1443233913824404403973887)
                      ·
                        rfl

theorem cell23_2810688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_2810688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810688 prefixEnd_2810688 := by exact prefixLift 2810688
  have htrace : WordTrace (prefixWord ++ tailWord_2810688) baseStart_2810688 baseEnd_2810688 := by
    simpa [prefixWord, tailWord_2810688, baseEnd_2810688] using wordTrace_append hprefix tailTrace_2810688
  have hstable : (prefixWord ++ tailWord_2810688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810688).length < 2 ^ (prefixWord ++ tailWord_2810688).sum := by decide
  have hdescent : baseEnd_2810688 < baseStart_2810688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810691 : List Nat := [1, 1, 1, 3, 1, 4, 2, 10]
def baseStart_2810691 : Nat := 118140960795 + 2810691 * 2 ^ 59
def prefixEnd_2810691 : Nat := 4983230072969 + 3 ^ 40 * 2810691 * 2
def baseEnd_2810691 : Nat := 53453164972828440453199

theorem tailTrace_2810691 : CollatzResearch.WordTrace tailWord_2810691 prefixEnd_2810691 53453164972828440453199 := by
  unfold tailWord_2810691
  simp only [CollatzResearch.WordTrace]
  refine ⟨102514322660354009650943927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68342881773569339767295951 102514322660354009650943927)
  ·
    refine ⟨153771483990531014476415891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102514322660354009650943927 153771483990531014476415891)
    ·
      refine ⟨230657225985796521714623837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153771483990531014476415891 230657225985796521714623837)
      ·
        refine ⟨86496459744673695642983939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230657225985796521714623837 86496459744673695642983939)
        ·
          refine ⟨129744689617010543464475909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86496459744673695642983939 129744689617010543464475909)
          ·
            refine ⟨24327129303189476899589233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129744689617010543464475909 24327129303189476899589233)
            ·
              refine ⟨18245346977392107674691925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24327129303189476899589233 18245346977392107674691925)
              ·
                refine ⟨53453164972828440453199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18245346977392107674691925 53453164972828440453199)
                ·
                  rfl

theorem cell23_2810691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 10].length) (baseStart_2810691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810691 prefixEnd_2810691 := by exact prefixLift 2810691
  have htrace : WordTrace (prefixWord ++ tailWord_2810691) baseStart_2810691 baseEnd_2810691 := by
    simpa [prefixWord, tailWord_2810691, baseEnd_2810691] using wordTrace_append hprefix tailTrace_2810691
  have hstable : (prefixWord ++ tailWord_2810691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810691).length < 2 ^ (prefixWord ++ tailWord_2810691).sum := by decide
  have hdescent : baseEnd_2810691 < baseStart_2810691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810698 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_2810698 : Nat := 118140960795 + 2810698 * 2 ^ 59
def prefixEnd_2810698 : Nat := 4983230072969 + 3 ^ 40 * 2810698 * 2
def baseEnd_2810698 : Nat := 1443239048630949364848841

theorem tailTrace_2810698 : CollatzResearch.WordTrace tailWord_2810698 prefixEnd_2810698 1443239048630949364848841 := by
  unfold tailWord_2810698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25628644492832162461612187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68343051980885766564299165 25628644492832162461612187)
  ·
    refine ⟨38442966739248243692418281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25628644492832162461612187 38442966739248243692418281)
    ·
      refine ⟨28832225054436182769313711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38442966739248243692418281 28832225054436182769313711)
      ·
        refine ⟨43248337581654274153970567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28832225054436182769313711 43248337581654274153970567)
        ·
          refine ⟨64872506372481411230955851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43248337581654274153970567 64872506372481411230955851)
          ·
            refine ⟨97308759558722116846433777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64872506372481411230955851 97308759558722116846433777)
            ·
              refine ⟨72981569669041587634825333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97308759558722116846433777 72981569669041587634825333)
              ·
                refine ⟨6842022156472648840764875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72981569669041587634825333 6842022156472648840764875)
                ·
                  refine ⟨10263033234708973261147313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842022156472648840764875 10263033234708973261147313)
                  ·
                    refine ⟨7697274926031729945860485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10263033234708973261147313 7697274926031729945860485)
                    ·
                      refine ⟨1443239048630949364848841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7697274926031729945860485 1443239048630949364848841)
                      ·
                        rfl

theorem cell23_2810698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_2810698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810698 prefixEnd_2810698 := by exact prefixLift 2810698
  have htrace : WordTrace (prefixWord ++ tailWord_2810698) baseStart_2810698 baseEnd_2810698 := by
    simpa [prefixWord, tailWord_2810698, baseEnd_2810698] using wordTrace_append hprefix tailTrace_2810698
  have hstable : (prefixWord ++ tailWord_2810698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810698).length < 2 ^ (prefixWord ++ tailWord_2810698).sum := by decide
  have hdescent : baseEnd_2810698 < baseStart_2810698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810722 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2810722 : Nat := 118140960795 + 2810722 * 2 ^ 59
def prefixEnd_2810722 : Nat := 4983230072969 + 3 ^ 40 * 2810722 * 2
def baseEnd_2810722 : Nat := 1443251372166657270948731

theorem tailTrace_2810722 : CollatzResearch.WordTrace tailWord_2810722 prefixEnd_2810722 1443251372166657270948731 := by
  unfold tailWord_2810722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25628863330810425486330605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68343635548827801296881613 25628863330810425486330605)
  ·
    refine ⟨9610823749053909557373977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25628863330810425486330605 9610823749053909557373977)
    ·
      refine ⟨7208117811790432168030483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9610823749053909557373977 7208117811790432168030483)
      ·
        refine ⟨10812176717685648252045725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208117811790432168030483 10812176717685648252045725)
        ·
          refine ⟨4054566269132118094517147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10812176717685648252045725 4054566269132118094517147)
          ·
            refine ⟨6081849403698177141775721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054566269132118094517147 6081849403698177141775721)
            ·
              refine ⟨4561387052773632856331791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081849403698177141775721 4561387052773632856331791)
              ·
                refine ⟨6842080579160449284497687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561387052773632856331791 6842080579160449284497687)
                ·
                  refine ⟨10263120868740673926746531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842080579160449284497687 10263120868740673926746531)
                  ·
                    refine ⟨15394681303111010890119797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10263120868740673926746531 15394681303111010890119797)
                    ·
                      refine ⟨1443251372166657270948731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15394681303111010890119797 1443251372166657270948731)
                      ·
                        rfl

theorem cell23_2810722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2810722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810722 prefixEnd_2810722 := by exact prefixLift 2810722
  have htrace : WordTrace (prefixWord ++ tailWord_2810722) baseStart_2810722 baseEnd_2810722 := by
    simpa [prefixWord, tailWord_2810722, baseEnd_2810722] using wordTrace_append hprefix tailTrace_2810722
  have hstable : (prefixWord ++ tailWord_2810722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810722).length < 2 ^ (prefixWord ++ tailWord_2810722).sum := by decide
  have hdescent : baseEnd_2810722 < baseStart_2810722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810805 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2810805 : Nat := 118140960795 + 2810805 * 2 ^ 59
def prefixEnd_2810805 : Nat := 4983230072969 + 3 ^ 40 * 2810805 * 2
def baseEnd_2810805 : Nat := 1443293991060980446210849

theorem tailTrace_2810805 : CollatzResearch.WordTrace tailWord_2810805 prefixEnd_2810805 1443293991060980446210849 := by
  unfold tailWord_2810805
  simp only [CollatzResearch.WordTrace]
  refine ⟨102518480581941007120593869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68345653721294004747062579 102518480581941007120593869)
  ·
    refine ⟨38444430218227877670222701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102518480581941007120593869 38444430218227877670222701)
    ·
      refine ⟨14416661331835454126333513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38444430218227877670222701 14416661331835454126333513)
      ·
        refine ⟨10812495998876590594750135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14416661331835454126333513 10812495998876590594750135)
        ·
          refine ⟨16218743998314885892125203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10812495998876590594750135 16218743998314885892125203)
          ·
            refine ⟨24328115997472328838187805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16218743998314885892125203 24328115997472328838187805)
            ·
              refine ⟨9123043499052123314320427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24328115997472328838187805 9123043499052123314320427)
              ·
                refine ⟨13684565248578184971480641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9123043499052123314320427 13684565248578184971480641)
                ·
                  refine ⟨10263423936433638728610481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13684565248578184971480641 10263423936433638728610481)
                  ·
                    refine ⟨7697567952325229046457861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10263423936433638728610481 7697567952325229046457861)
                    ·
                      refine ⟨1443293991060980446210849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7697567952325229046457861 1443293991060980446210849)
                      ·
                        rfl

theorem cell23_2810805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2810805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810805 prefixEnd_2810805 := by exact prefixLift 2810805
  have htrace : WordTrace (prefixWord ++ tailWord_2810805) baseStart_2810805 baseEnd_2810805 := by
    simpa [prefixWord, tailWord_2810805, baseEnd_2810805] using wordTrace_append hprefix tailTrace_2810805
  have hstable : (prefixWord ++ tailWord_2810805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810805).length < 2 ^ (prefixWord ++ tailWord_2810805).sum := by decide
  have hdescent : baseEnd_2810805 < baseStart_2810805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810809 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2810809 : Nat := 118140960795 + 2810809 * 2 ^ 59
def prefixEnd_2810809 : Nat := 4983230072969 + 3 ^ 40 * 2810809 * 2
def baseEnd_2810809 : Nat := 1443296044983598430560831

theorem tailTrace_2810809 : CollatzResearch.WordTrace tailWord_2810809 prefixEnd_2810809 1443296044983598430560831 := by
  unfold tailWord_2810809
  simp only [CollatzResearch.WordTrace]
  refine ⟨102518626473926515803739481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68345750982617677202492987 102518626473926515803739481)
  ·
    refine ⟨76888969855444886852804611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102518626473926515803739481 76888969855444886852804611)
    ·
      refine ⟨115333454783167330279206917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76888969855444886852804611 115333454783167330279206917)
      ·
        refine ⟨21625022771843874427351297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115333454783167330279206917 21625022771843874427351297)
        ·
          refine ⟨16218767078882905820513473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21625022771843874427351297 16218767078882905820513473)
          ·
            refine ⟨12164075309162179365385105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16218767078882905820513473 12164075309162179365385105)
            ·
              refine ⟨9123056481871634524038829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12164075309162179365385105 9123056481871634524038829)
              ·
                refine ⟨3421146180701862946514561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9123056481871634524038829 3421146180701862946514561)
                ·
                  refine ⟨2565859635526397209885921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421146180701862946514561 2565859635526397209885921)
                  ·
                    refine ⟨1924394726644797907414441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2565859635526397209885921 1924394726644797907414441)
                    ·
                      refine ⟨1443296044983598430560831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924394726644797907414441 1443296044983598430560831)
                      ·
                        rfl

theorem cell23_2810809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2810809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810809 prefixEnd_2810809 := by exact prefixLift 2810809
  have htrace : WordTrace (prefixWord ++ tailWord_2810809) baseStart_2810809 baseEnd_2810809 := by
    simpa [prefixWord, tailWord_2810809, baseEnd_2810809] using wordTrace_append hprefix tailTrace_2810809
  have hstable : (prefixWord ++ tailWord_2810809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810809).length < 2 ^ (prefixWord ++ tailWord_2810809).sum := by decide
  have hdescent : baseEnd_2810809 < baseStart_2810809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810865 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2810865 : Nat := 118140960795 + 2810865 * 2 ^ 59
def prefixEnd_2810865 : Nat := 4983230072969 + 3 ^ 40 * 2810865 * 2
def baseEnd_2810865 : Nat := 1443324799900250211460573

theorem tailTrace_2810865 : CollatzResearch.WordTrace tailWord_2810865 prefixEnd_2810865 1443324799900250211460573 := by
  unfold tailWord_2810865
  simp only [CollatzResearch.WordTrace]
  refine ⟨102520668961723637367778049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68347112641149091578518699 102520668961723637367778049)
  ·
    refine ⟨76890501721292728025833537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102520668961723637367778049 76890501721292728025833537)
    ·
      refine ⟨57667876290969546019375153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76890501721292728025833537 57667876290969546019375153)
      ·
        refine ⟨43250907218227159514531365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57667876290969546019375153 43250907218227159514531365)
        ·
          refine ⟨8109545103417592408974631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43250907218227159514531365 8109545103417592408974631)
          ·
            refine ⟨12164317655126388613461947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8109545103417592408974631 12164317655126388613461947)
            ·
              refine ⟨18246476482689582920192921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12164317655126388613461947 18246476482689582920192921)
              ·
                refine ⟨13684857362017187190144691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18246476482689582920192921 13684857362017187190144691)
                ·
                  refine ⟨20527286043025780785217037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13684857362017187190144691 20527286043025780785217037)
                  ·
                    refine ⟨7697732266134667794456389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20527286043025780785217037 7697732266134667794456389)
                    ·
                      refine ⟨1443324799900250211460573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7697732266134667794456389 1443324799900250211460573)
                      ·
                        rfl

theorem cell23_2810865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2810865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810865 prefixEnd_2810865 := by exact prefixLift 2810865
  have htrace : WordTrace (prefixWord ++ tailWord_2810865) baseStart_2810865 baseEnd_2810865 := by
    simpa [prefixWord, tailWord_2810865, baseEnd_2810865] using wordTrace_append hprefix tailTrace_2810865
  have hstable : (prefixWord ++ tailWord_2810865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810865).length < 2 ^ (prefixWord ++ tailWord_2810865).sum := by decide
  have hdescent : baseEnd_2810865 < baseStart_2810865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810885 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_2810885 : Nat := 118140960795 + 2810885 * 2 ^ 59
def prefixEnd_2810885 : Nat := 4983230072969 + 3 ^ 40 * 2810885 * 2
def baseEnd_2810885 : Nat := 1443335069513340133210481

theorem tailTrace_2810885 : CollatzResearch.WordTrace tailWord_2810885 prefixEnd_2810885 1443335069513340133210481 := by
  unfold tailWord_2810885
  simp only [CollatzResearch.WordTrace]
  refine ⟨102521398421651180783506109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68347598947767453855670739 102521398421651180783506109)
  ·
    refine ⟨38445524408119192793814791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102521398421651180783506109 38445524408119192793814791)
    ·
      refine ⟨57668286612178789190722187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38445524408119192793814791 57668286612178789190722187)
      ·
        refine ⟨86502429918268183786083281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57668286612178789190722187 86502429918268183786083281)
        ·
          refine ⟨64876822438701137839562461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86502429918268183786083281 64876822438701137839562461)
          ·
            refine ⟨24328808414512926689835923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64876822438701137839562461 24328808414512926689835923)
            ·
              refine ⟨36493212621769390034753885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24328808414512926689835923 36493212621769390034753885)
              ·
                refine ⟨13684954733163521263032707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36493212621769390034753885 13684954733163521263032707)
                ·
                  refine ⟨20527432099745281894549061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13684954733163521263032707 20527432099745281894549061)
                  ·
                    refine ⟨3848893518702240355227949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20527432099745281894549061 3848893518702240355227949)
                    ·
                      refine ⟨1443335069513340133210481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3848893518702240355227949 1443335069513340133210481)
                      ·
                        rfl

theorem cell23_2810885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_2810885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810885 prefixEnd_2810885 := by exact prefixLift 2810885
  have htrace : WordTrace (prefixWord ++ tailWord_2810885) baseStart_2810885 baseEnd_2810885 := by
    simpa [prefixWord, tailWord_2810885, baseEnd_2810885] using wordTrace_append hprefix tailTrace_2810885
  have hstable : (prefixWord ++ tailWord_2810885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810885).length < 2 ^ (prefixWord ++ tailWord_2810885).sum := by decide
  have hdescent : baseEnd_2810885 < baseStart_2810885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810955 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4]
def baseStart_2810955 : Nat := 118140960795 + 2810955 * 2 ^ 59
def prefixEnd_2810955 : Nat := 4983230072969 + 3 ^ 40 * 2810955 * 2
def baseEnd_2810955 : Nat := 1443371013159154859335159

theorem tailTrace_2810955 : CollatzResearch.WordTrace tailWord_2810955 prefixEnd_2810955 1443371013159154859335159 := by
  unfold tailWord_2810955
  simp only [CollatzResearch.WordTrace]
  refine ⟨102523951531397582738554319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68349301020931721825702879 102523951531397582738554319)
  ·
    refine ⟨153785927297096374107831479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102523951531397582738554319 153785927297096374107831479)
    ·
      refine ⟨230678890945644561161747219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153785927297096374107831479 230678890945644561161747219)
      ·
        refine ⟨346018336418466841742620829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230678890945644561161747219 346018336418466841742620829)
        ·
          refine ⟨129756876156925065653482811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346018336418466841742620829 129756876156925065653482811)
          ·
            refine ⟨194635314235387598480224217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129756876156925065653482811 194635314235387598480224217)
            ·
              refine ⟨145976485676540698860168163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194635314235387598480224217 145976485676540698860168163)
              ·
                refine ⟨218964728514811048290252245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145976485676540698860168163 218964728514811048290252245)
                ·
                  refine ⟨5131985824565883944302787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 218964728514811048290252245 5131985824565883944302787)
                  ·
                    refine ⟨7697978736848825916454181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5131985824565883944302787 7697978736848825916454181)
                    ·
                      refine ⟨1443371013159154859335159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7697978736848825916454181 1443371013159154859335159)
                      ·
                        rfl

theorem cell23_2810955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_2810955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810955 prefixEnd_2810955 := by exact prefixLift 2810955
  have htrace : WordTrace (prefixWord ++ tailWord_2810955) baseStart_2810955 baseEnd_2810955 := by
    simpa [prefixWord, tailWord_2810955, baseEnd_2810955] using wordTrace_append hprefix tailTrace_2810955
  have hstable : (prefixWord ++ tailWord_2810955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810955).length < 2 ^ (prefixWord ++ tailWord_2810955).sum := by decide
  have hdescent : baseEnd_2810955 < baseStart_2810955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810965 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2810965 : Nat := 118140960795 + 2810965 * 2 ^ 59
def prefixEnd_2810965 : Nat := 4983230072969 + 3 ^ 40 * 2810965 * 2
def baseEnd_2810965 : Nat := 481125382655233273403371

theorem tailTrace_2810965 : CollatzResearch.WordTrace tailWord_2810965 prefixEnd_2810965 481125382655233273403371 := by
  unfold tailWord_2810965
  simp only [CollatzResearch.WordTrace]
  refine ⟨102524316261361354446418349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68349544174240902964278899 102524316261361354446418349)
  ·
    refine ⟨38446618598010507917406881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102524316261361354446418349 38446618598010507917406881)
    ·
      refine ⟨28834963948507880938055161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38446618598010507917406881 28834963948507880938055161)
      ·
        refine ⟨21626222961380910703541371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28834963948507880938055161 21626222961380910703541371)
        ·
          refine ⟨32439334442071366055312057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21626222961380910703541371 32439334442071366055312057)
          ·
            refine ⟨24329500831553524541484043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32439334442071366055312057 24329500831553524541484043)
            ·
              refine ⟨36494251247330286812226065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24329500831553524541484043 36494251247330286812226065)
              ·
                refine ⟨27370688435497715109169549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36494251247330286812226065 27370688435497715109169549)
                ·
                  refine ⟨10264008163311643165938581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27370688435497715109169549 10264008163311643165938581)
                  ·
                    refine ⟨481125382655233273403371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10264008163311643165938581 481125382655233273403371)
                    ·
                      rfl

theorem cell23_2810965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2810965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810965 prefixEnd_2810965 := by exact prefixLift 2810965
  have htrace : WordTrace (prefixWord ++ tailWord_2810965) baseStart_2810965 baseEnd_2810965 := by
    simpa [prefixWord, tailWord_2810965, baseEnd_2810965] using wordTrace_append hprefix tailTrace_2810965
  have hstable : (prefixWord ++ tailWord_2810965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810965).length < 2 ^ (prefixWord ++ tailWord_2810965).sum := by decide
  have hdescent : baseEnd_2810965 < baseStart_2810965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810972 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_2810972 : Nat := 118140960795 + 2810972 * 2 ^ 59
def prefixEnd_2810972 : Nat := 4983230072969 + 3 ^ 40 * 2810972 * 2
def baseEnd_2810972 : Nat := 1443379742330281292822581

theorem tailTrace_2810972 : CollatzResearch.WordTrace tailWord_2810972 prefixEnd_2810972 1443379742330281292822581 := by
  unfold tailWord_2810972
  simp only [CollatzResearch.WordTrace]
  refine ⟨51262285786167997320961585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68349714381557329761282113 51262285786167997320961585)
  ·
    refine ⟨38446714339625997990721189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51262285786167997320961585 38446714339625997990721189)
    ·
      refine ⟨7208758938679874623260223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38446714339625997990721189 7208758938679874623260223)
      ·
        refine ⟨10813138408019811934890335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208758938679874623260223 10813138408019811934890335)
        ·
          refine ⟨16219707612029717902335503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10813138408019811934890335 16219707612029717902335503)
          ·
            refine ⟨24329561418044576853503255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219707612029717902335503 24329561418044576853503255)
            ·
              refine ⟨36494342127066865280254883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24329561418044576853503255 36494342127066865280254883)
              ·
                refine ⟨54741513190600297920382325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36494342127066865280254883 54741513190600297920382325)
                ·
                  refine ⟨5132016861618777930035843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54741513190600297920382325 5132016861618777930035843)
                  ·
                    refine ⟨7698025292428166895053765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132016861618777930035843 7698025292428166895053765)
                    ·
                      refine ⟨1443379742330281292822581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7698025292428166895053765 1443379742330281292822581)
                      ·
                        rfl

theorem cell23_2810972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_2810972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810972 prefixEnd_2810972 := by exact prefixLift 2810972
  have htrace : WordTrace (prefixWord ++ tailWord_2810972) baseStart_2810972 baseEnd_2810972 := by
    simpa [prefixWord, tailWord_2810972, baseEnd_2810972] using wordTrace_append hprefix tailTrace_2810972
  have hstable : (prefixWord ++ tailWord_2810972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810972).length < 2 ^ (prefixWord ++ tailWord_2810972).sum := by decide
  have hdescent : baseEnd_2810972 < baseStart_2810972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810975 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2810975 : Nat := 118140960795 + 2810975 * 2 ^ 59
def prefixEnd_2810975 : Nat := 4983230072969 + 3 ^ 40 * 2810975 * 2
def baseEnd_2810975 : Nat := 1443381282772244781085067

theorem tailTrace_2810975 : CollatzResearch.WordTrace tailWord_2810975 prefixEnd_2810975 1443381282772244781085067 := by
  unfold tailWord_2810975
  simp only [CollatzResearch.WordTrace]
  refine ⟨102524680991325126154282379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68349787327550084102854919 102524680991325126154282379)
  ·
    refine ⟨153787021486987689231423569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102524680991325126154282379 153787021486987689231423569)
    ·
      refine ⟨115340266115240766923567677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153787021486987689231423569 115340266115240766923567677)
      ·
        refine ⟨43252599793215287596337879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115340266115240766923567677 43252599793215287596337879)
        ·
          refine ⟨64878899689822931394506819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43252599793215287596337879 64878899689822931394506819)
          ·
            refine ⟨97318349534734397091760229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64878899689822931394506819 97318349534734397091760229)
            ·
              refine ⟨18247190537762699454705043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97318349534734397091760229 18247190537762699454705043)
              ·
                refine ⟨27370785806644049182057565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18247190537762699454705043 27370785806644049182057565)
                ·
                  refine ⟨10264044677491518443271587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27370785806644049182057565 10264044677491518443271587)
                  ·
                    refine ⟨15396067016237277664907381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10264044677491518443271587 15396067016237277664907381)
                    ·
                      refine ⟨1443381282772244781085067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15396067016237277664907381 1443381282772244781085067)
                      ·
                        rfl

theorem cell23_2810975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2810975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810975 prefixEnd_2810975 := by exact prefixLift 2810975
  have htrace : WordTrace (prefixWord ++ tailWord_2810975) baseStart_2810975 baseEnd_2810975 := by
    simpa [prefixWord, tailWord_2810975, baseEnd_2810975] using wordTrace_append hprefix tailTrace_2810975
  have hstable : (prefixWord ++ tailWord_2810975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810975).length < 2 ^ (prefixWord ++ tailWord_2810975).sum := by decide
  have hdescent : baseEnd_2810975 < baseStart_2810975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810992 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_2810992 : Nat := 118140960795 + 2810992 * 2 ^ 59
def prefixEnd_2810992 : Nat := 4983230072969 + 3 ^ 40 * 2810992 * 2
def baseEnd_2810992 : Nat := 1443390011943371214572489

theorem tailTrace_2810992 : CollatzResearch.WordTrace tailWord_2810992 prefixEnd_2810992 1443390011943371214572489 := by
  unfold tailWord_2810992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51262650516131769028825615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68350200688175692038434153 51262650516131769028825615)
  ·
    refine ⟨76893975774197653543238423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51262650516131769028825615 76893975774197653543238423)
    ·
      refine ⟨115340963661296480314857635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76893975774197653543238423 115340963661296480314857635)
      ·
        refine ⟨173011445491944720472286453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115340963661296480314857635 173011445491944720472286453)
        ·
          refine ⟨16219823014869817544276855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173011445491944720472286453 16219823014869817544276855)
          ·
            refine ⟨24329734522304726316415283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219823014869817544276855 24329734522304726316415283)
            ·
              refine ⟨36494601783457089474622925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24329734522304726316415283 36494601783457089474622925)
              ·
                refine ⟨13685475668796408552983597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36494601783457089474622925 13685475668796408552983597)
                ·
                  refine ⟨5132053375798653207368849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13685475668796408552983597 5132053375798653207368849)
                  ·
                    refine ⟨3849040031848989905526637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5132053375798653207368849 3849040031848989905526637)
                    ·
                      refine ⟨1443390011943371214572489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3849040031848989905526637 1443390011943371214572489)
                      ·
                        rfl

theorem cell23_2810992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_2810992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2810992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2810992 prefixEnd_2810992 := by exact prefixLift 2810992
  have htrace : WordTrace (prefixWord ++ tailWord_2810992) baseStart_2810992 baseEnd_2810992 := by
    simpa [prefixWord, tailWord_2810992, baseEnd_2810992] using wordTrace_append hprefix tailTrace_2810992
  have hstable : (prefixWord ++ tailWord_2810992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810992).length < 2 ^ (prefixWord ++ tailWord_2810992).sum := by decide
  have hdescent : baseEnd_2810992 < baseStart_2810992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811015 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2811015 : Nat := 118140960795 + 2811015 * 2 ^ 59
def prefixEnd_2811015 : Nat := 4983230072969 + 3 ^ 40 * 2811015 * 2
def baseEnd_2811015 : Nat := 1443401821998424624584883

theorem tailTrace_2811015 : CollatzResearch.WordTrace tailWord_2811015 prefixEnd_2811015 1443401821998424624584883 := by
  unfold tailWord_2811015
  simp only [CollatzResearch.WordTrace]
  refine ⟨102526139911180212985738499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68350759940786808657158999 102526139911180212985738499)
  ·
    refine ⟨153789209866770319478607749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102526139911180212985738499 153789209866770319478607749)
    ·
      refine ⟨28835476850019434902238953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153789209866770319478607749 28835476850019434902238953)
      ·
        refine ⟨21626607637514576176679215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28835476850019434902238953 21626607637514576176679215)
        ·
          refine ⟨32439911456271864265018823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21626607637514576176679215 32439911456271864265018823)
          ·
            refine ⟨48659867184407796397528235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32439911456271864265018823 48659867184407796397528235)
            ·
              refine ⟨72989800776611694596292353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48659867184407796397528235 72989800776611694596292353)
              ·
                refine ⟨54742350582458770947219265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72989800776611694596292353 54742350582458770947219265)
                ·
                  refine ⟨41056762936844078210414449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54742350582458770947219265 41056762936844078210414449)
                  ·
                    refine ⟨30792572202633058657810837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41056762936844078210414449 30792572202633058657810837)
                    ·
                      refine ⟨1443401821998424624584883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30792572202633058657810837 1443401821998424624584883)
                      ·
                        rfl

theorem cell23_2811015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2811015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811015 prefixEnd_2811015 := by exact prefixLift 2811015
  have htrace : WordTrace (prefixWord ++ tailWord_2811015) baseStart_2811015 baseEnd_2811015 := by
    simpa [prefixWord, tailWord_2811015, baseEnd_2811015] using wordTrace_append hprefix tailTrace_2811015
  have hstable : (prefixWord ++ tailWord_2811015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811015).length < 2 ^ (prefixWord ++ tailWord_2811015).sum := by decide
  have hdescent : baseEnd_2811015 < baseStart_2811015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811055 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 8]
def baseStart_2811055 : Nat := 118140960795 + 2811055 * 2 ^ 59
def prefixEnd_2811055 : Nat := 4983230072969 + 3 ^ 40 * 2811055 * 2
def baseEnd_2811055 : Nat := 481140787074868156028233

theorem tailTrace_2811055 : CollatzResearch.WordTrace tailWord_2811055 prefixEnd_2811055 481140787074868156028233 := by
  unfold tailWord_2811055
  simp only [CollatzResearch.WordTrace]
  refine ⟨102527598831035299817194619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68351732554023533211463079 102527598831035299817194619)
  ·
    refine ⟨153791398246552949725791929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102527598831035299817194619 153791398246552949725791929)
    ·
      refine ⟨115343548684914712294343947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153791398246552949725791929 115343548684914712294343947)
      ·
        refine ⟨173015323027372068441515921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115343548684914712294343947 173015323027372068441515921)
        ·
          refine ⟨129761492270529051331136941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173015323027372068441515921 129761492270529051331136941)
          ·
            refine ⟨48660559601448394249176353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129761492270529051331136941 48660559601448394249176353)
            ·
              refine ⟨36495419701086295686882265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48660559601448394249176353 36495419701086295686882265)
              ·
                refine ⟨27371564775814721765161699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36495419701086295686882265 27371564775814721765161699)
                ·
                  refine ⟨41057347163722082647742549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27371564775814721765161699 41057347163722082647742549)
                  ·
                    refine ⟨481140787074868156028233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41057347163722082647742549 481140787074868156028233)
                    ·
                      rfl

theorem cell23_2811055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_2811055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811055 prefixEnd_2811055 := by exact prefixLift 2811055
  have htrace : WordTrace (prefixWord ++ tailWord_2811055) baseStart_2811055 baseEnd_2811055 := by
    simpa [prefixWord, tailWord_2811055, baseEnd_2811055] using wordTrace_append hprefix tailTrace_2811055
  have hstable : (prefixWord ++ tailWord_2811055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811055).length < 2 ^ (prefixWord ++ tailWord_2811055).sum := by decide
  have hdescent : baseEnd_2811055 < baseStart_2811055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811074 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_2811074 : Nat := 118140960795 + 2811074 * 2 ^ 59
def prefixEnd_2811074 : Nat := 4983230072969 + 3 ^ 40 * 2811074 * 2
def baseEnd_2811074 : Nat := 1443432117357039893747113

theorem tailTrace_2811074 : CollatzResearch.WordTrace tailWord_2811074 prefixEnd_2811074 1443432117357039893747113 := by
  unfold tailWord_2811074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632072954491616515534069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68352194545310977374757517 25632072954491616515534069)
  ·
    refine ⟨2403006839483589048331319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25632072954491616515534069 2403006839483589048331319)
    ·
      refine ⟨3604510259225383572496979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403006839483589048331319 3604510259225383572496979)
      ·
        refine ⟨5406765388838075358745469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604510259225383572496979 5406765388838075358745469)
        ·
          refine ⟨2027537020814278259529551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406765388838075358745469 2027537020814278259529551)
          ·
            refine ⟨3041305531221417389294327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027537020814278259529551 3041305531221417389294327)
            ·
              refine ⟨4561958296832126083941491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041305531221417389294327 4561958296832126083941491)
              ·
                refine ⟨6842937445248189125912237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561958296832126083941491 6842937445248189125912237)
                ·
                  refine ⟨2566101541968070922217089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6842937445248189125912237 2566101541968070922217089)
                  ·
                    refine ⟨1924576156476053191662817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566101541968070922217089 1924576156476053191662817)
                    ·
                      refine ⟨1443432117357039893747113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924576156476053191662817 1443432117357039893747113)
                      ·
                        rfl

theorem cell23_2811074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_2811074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811074 prefixEnd_2811074 := by exact prefixLift 2811074
  have htrace : WordTrace (prefixWord ++ tailWord_2811074) baseStart_2811074 baseEnd_2811074 := by
    simpa [prefixWord, tailWord_2811074, baseEnd_2811074] using wordTrace_append hprefix tailTrace_2811074
  have hstable : (prefixWord ++ tailWord_2811074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811074).length < 2 ^ (prefixWord ++ tailWord_2811074).sum := by decide
  have hdescent : baseEnd_2811074 < baseStart_2811074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811075 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_2811075 : Nat := 118140960795 + 2811075 * 2 ^ 59
def prefixEnd_2811075 : Nat := 4983230072969 + 3 ^ 40 * 2811075 * 2
def baseEnd_2811075 : Nat := 1443432630837694389834607

theorem tailTrace_2811075 : CollatzResearch.WordTrace tailWord_2811075 prefixEnd_2811075 1443432630837694389834607 := by
  unfold tailWord_2811075
  simp only [CollatzResearch.WordTrace]
  refine ⟨102528328290962843232922679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68352218860641895488615119 102528328290962843232922679)
  ·
    refine ⟨153792492436444264849384019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102528328290962843232922679 153792492436444264849384019)
    ·
      refine ⟨230688738654666397274076029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153792492436444264849384019 230688738654666397274076029)
      ·
        refine ⟨86508276995499898977778511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230688738654666397274076029 86508276995499898977778511)
        ·
          refine ⟨129762415493249848466667767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86508276995499898977778511 129762415493249848466667767)
          ·
            refine ⟨194643623239874772700001651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129762415493249848466667767 194643623239874772700001651)
            ·
              refine ⟨291965434859812159050002477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194643623239874772700001651 291965434859812159050002477)
              ·
                refine ⟨109487038072429559643750929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291965434859812159050002477 109487038072429559643750929)
                ·
                  refine ⟨82115278554322169732813197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109487038072429559643750929 82115278554322169732813197)
                  ·
                    refine ⟨30793229457870813649804949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82115278554322169732813197 30793229457870813649804949)
                    ·
                      refine ⟨1443432630837694389834607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30793229457870813649804949 1443432630837694389834607)
                      ·
                        rfl

theorem cell23_2811075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_2811075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811075 prefixEnd_2811075 := by exact prefixLift 2811075
  have htrace : WordTrace (prefixWord ++ tailWord_2811075) baseStart_2811075 baseEnd_2811075 := by
    simpa [prefixWord, tailWord_2811075, baseEnd_2811075] using wordTrace_append hprefix tailTrace_2811075
  have hstable : (prefixWord ++ tailWord_2811075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811075).length < 2 ^ (prefixWord ++ tailWord_2811075).sum := by decide
  have hdescent : baseEnd_2811075 < baseStart_2811075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811139 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 5, 2]
def baseStart_2811139 : Nat := 118140960795 + 2811139 * 2 ^ 59
def prefixEnd_2811139 : Nat := 4983230072969 + 3 ^ 40 * 2811139 * 2
def baseEnd_2811139 : Nat := 1443465493599582139434313

theorem tailTrace_2811139 : CollatzResearch.WordTrace tailWord_2811139 prefixEnd_2811139 1443465493599582139434313 := by
  unfold tailWord_2811139
  simp only [CollatzResearch.WordTrace]
  refine ⟨102530662562730982163252471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68353775041820654775501647 102530662562730982163252471)
  ·
    refine ⟨153795993844096473244878707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102530662562730982163252471 153795993844096473244878707)
    ·
      refine ⟨230693990766144709867318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153795993844096473244878707 230693990766144709867318061)
      ·
        refine ⟨86510246537304266200244273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230693990766144709867318061 86510246537304266200244273)
        ·
          refine ⟨64882684902978199650183205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86510246537304266200244273 64882684902978199650183205)
          ·
            refine ⟨12165503419308412434409351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64882684902978199650183205 12165503419308412434409351)
            ·
              refine ⟨18248255128962618651614027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165503419308412434409351 18248255128962618651614027)
              ·
                refine ⟨27372382693443927977421041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18248255128962618651614027 27372382693443927977421041)
                ·
                  refine ⟨20529287020082945983065781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27372382693443927977421041 20529287020082945983065781)
                  ·
                    refine ⟨1924620658132776185912417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20529287020082945983065781 1924620658132776185912417)
                    ·
                      refine ⟨1443465493599582139434313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924620658132776185912417 1443465493599582139434313)
                      ·
                        rfl

theorem cell23_2811139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_2811139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811139 prefixEnd_2811139 := by exact prefixLift 2811139
  have htrace : WordTrace (prefixWord ++ tailWord_2811139) baseStart_2811139 baseEnd_2811139 := by
    simpa [prefixWord, tailWord_2811139, baseEnd_2811139] using wordTrace_append hprefix tailTrace_2811139
  have hstable : (prefixWord ++ tailWord_2811139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811139).length < 2 ^ (prefixWord ++ tailWord_2811139).sum := by decide
  have hdescent : baseEnd_2811139 < baseStart_2811139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811169 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2811169 : Nat := 118140960795 + 2811169 * 2 ^ 59
def prefixEnd_2811169 : Nat := 4983230072969 + 3 ^ 40 * 2811169 * 2
def baseEnd_2811169 : Nat := 1443480898019217022059175

theorem tailTrace_2811169 : CollatzResearch.WordTrace tailWord_2811169 prefixEnd_2811169 1443480898019217022059175 := by
  unfold tailWord_2811169
  simp only [CollatzResearch.WordTrace]
  refine ⟨102531756752622297286844561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68354504501748198191229707 102531756752622297286844561)
  ·
    refine ⟨76898817564466722965133421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102531756752622297286844561 76898817564466722965133421)
    ·
      refine ⟨28837056586675021111925033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76898817564466722965133421 28837056586675021111925033)
      ·
        refine ⟨21627792440006265833943775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28837056586675021111925033 21627792440006265833943775)
        ·
          refine ⟨32441688660009398750915663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21627792440006265833943775 32441688660009398750915663)
          ·
            refine ⟨48662532990014098126373495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32441688660009398750915663 48662532990014098126373495)
            ·
              refine ⟨72993799485021147189560243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48662532990014098126373495 72993799485021147189560243)
              ·
                refine ⟨109490699227531720784340365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72993799485021147189560243 109490699227531720784340365)
                ·
                  refine ⟨41059012210324395294127637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109490699227531720784340365 41059012210324395294127637)
                  ·
                    refine ⟨1924641197358956029412233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41059012210324395294127637 1924641197358956029412233)
                    ·
                      refine ⟨1443480898019217022059175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924641197358956029412233 1443480898019217022059175)
                      ·
                        rfl

theorem cell23_2811169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2811169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811169 prefixEnd_2811169 := by exact prefixLift 2811169
  have htrace : WordTrace (prefixWord ++ tailWord_2811169) baseStart_2811169 baseEnd_2811169 := by
    simpa [prefixWord, tailWord_2811169, baseEnd_2811169] using wordTrace_append hprefix tailTrace_2811169
  have hstable : (prefixWord ++ tailWord_2811169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811169).length < 2 ^ (prefixWord ++ tailWord_2811169).sum := by decide
  have hdescent : baseEnd_2811169 < baseStart_2811169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811186 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_2811186 : Nat := 118140960795 + 2811186 * 2 ^ 59
def prefixEnd_2811186 : Nat := 4983230072969 + 3 ^ 40 * 2811186 * 2
def baseEnd_2811186 : Nat := 1443489627190343455546597

theorem tailTrace_2811186 : CollatzResearch.WordTrace tailWord_2811186 prefixEnd_2811186 1443489627190343455546597 := by
  unfold tailWord_2811186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633094198390177297553353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68354917862373806126808941 25633094198390177297553353)
  ·
    refine ⟨19224820648792632973165015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25633094198390177297553353 19224820648792632973165015)
    ·
      refine ⟨28837230973188949459747523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19224820648792632973165015 28837230973188949459747523)
      ·
        refine ⟨43255846459783424189621285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28837230973188949459747523 43255846459783424189621285)
        ·
          refine ⟨8110471211209392035553991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43255846459783424189621285 8110471211209392035553991)
          ·
            refine ⟨12165706816814088053330987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110471211209392035553991 12165706816814088053330987)
            ·
              refine ⟨18248560225221132079996481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165706816814088053330987 18248560225221132079996481)
              ·
                refine ⟨13686420168915849059997361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18248560225221132079996481 13686420168915849059997361)
                ·
                  refine ⟨10264815126686886794998021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13686420168915849059997361 10264815126686886794998021)
                  ·
                    refine ⟨1924652836253791274062129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10264815126686886794998021 1924652836253791274062129)
                    ·
                      refine ⟨1443489627190343455546597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924652836253791274062129 1443489627190343455546597)
                      ·
                        rfl

theorem cell23_2811186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_2811186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811186 prefixEnd_2811186 := by exact prefixLift 2811186
  have htrace : WordTrace (prefixWord ++ tailWord_2811186) baseStart_2811186 baseEnd_2811186 := by
    simpa [prefixWord, tailWord_2811186, baseEnd_2811186] using wordTrace_append hprefix tailTrace_2811186
  have hstable : (prefixWord ++ tailWord_2811186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811186).length < 2 ^ (prefixWord ++ tailWord_2811186).sum := by decide
  have hdescent : baseEnd_2811186 < baseStart_2811186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811196 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_2811196 : Nat := 118140960795 + 2811196 * 2 ^ 59
def prefixEnd_2811196 : Nat := 4983230072969 + 3 ^ 40 * 2811196 * 2
def baseEnd_2811196 : Nat := 481164920665629472140517

theorem tailTrace_2811196 : CollatzResearch.WordTrace tailWord_2811196 prefixEnd_2811196 481164920665629472140517 := by
  unfold tailWord_2811196
  simp only [CollatzResearch.WordTrace]
  refine ⟨51266370761762240449038721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68355161015682987265384961 51266370761762240449038721)
  ·
    refine ⟨38449778071321680336779041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51266370761762240449038721 38449778071321680336779041)
    ·
      refine ⟨28837333553491260252584281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38449778071321680336779041 28837333553491260252584281)
      ·
        refine ⟨21628000165118445189438211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28837333553491260252584281 21628000165118445189438211)
        ·
          refine ⟨32442000247677667784157317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21628000165118445189438211 32442000247677667784157317)
          ·
            refine ⟨6082875046439562709529497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32442000247677667784157317 6082875046439562709529497)
            ·
              refine ⟨4562156284829672032147123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082875046439562709529497 4562156284829672032147123)
              ·
                refine ⟨6843234427244508048220685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562156284829672032147123 6843234427244508048220685)
                ·
                  refine ⟨2566212910216690518082757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6843234427244508048220685 2566212910216690518082757)
                  ·
                    refine ⟨481164920665629472140517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566212910216690518082757 481164920665629472140517)
                    ·
                      rfl

theorem cell23_2811196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_2811196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811196 prefixEnd_2811196 := by exact prefixLift 2811196
  have htrace : WordTrace (prefixWord ++ tailWord_2811196) baseStart_2811196 baseEnd_2811196 := by
    simpa [prefixWord, tailWord_2811196, baseEnd_2811196] using wordTrace_append hprefix tailTrace_2811196
  have hstable : (prefixWord ++ tailWord_2811196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811196).length < 2 ^ (prefixWord ++ tailWord_2811196).sum := by decide
  have hdescent : baseEnd_2811196 < baseStart_2811196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811259 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4]
def baseStart_2811259 : Nat := 118140960795 + 2811259 * 2 ^ 59
def prefixEnd_2811259 : Nat := 4983230072969 + 3 ^ 40 * 2811259 * 2
def baseEnd_2811259 : Nat := 1443527111278121669933761

theorem tailTrace_2811259 : CollatzResearch.WordTrace tailWord_2811259 prefixEnd_2811259 1443527111278121669933761 := by
  unfold tailWord_2811259
  simp only [CollatzResearch.WordTrace]
  refine ⟨102535039322296242657620831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68356692881530828438413887 102535039322296242657620831)
  ·
    refine ⟨153802558983444363986431247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102535039322296242657620831 153802558983444363986431247)
    ·
      refine ⟨230703838475166545979646871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153802558983444363986431247 230703838475166545979646871)
      ·
        refine ⟨346055757712749818969470307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230703838475166545979646871 346055757712749818969470307)
        ·
          refine ⟨519083636569124728454205461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346055757712749818969470307 519083636569124728454205461)
          ·
            refine ⟨24332045464177721646290881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 519083636569124728454205461 24332045464177721646290881)
            ·
              refine ⟨18249034098133291234718161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24332045464177721646290881 18249034098133291234718161)
              ·
                refine ⟨13686775573599968426038621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18249034098133291234718161 13686775573599968426038621)
                ·
                  refine ⟨5132540840099988159764483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13686775573599968426038621 5132540840099988159764483)
                  ·
                    refine ⟨7698811260149982239646725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132540840099988159764483 7698811260149982239646725)
                    ·
                      refine ⟨1443527111278121669933761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7698811260149982239646725 1443527111278121669933761)
                      ·
                        rfl

theorem cell23_2811259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_2811259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811259 prefixEnd_2811259 := by exact prefixLift 2811259
  have htrace : WordTrace (prefixWord ++ tailWord_2811259) baseStart_2811259 baseEnd_2811259 := by
    simpa [prefixWord, tailWord_2811259, baseEnd_2811259] using wordTrace_append hprefix tailTrace_2811259
  have hstable : (prefixWord ++ tailWord_2811259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811259).length < 2 ^ (prefixWord ++ tailWord_2811259).sum := by decide
  have hdescent : baseEnd_2811259 < baseStart_2811259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811273 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_2811273 : Nat := 118140960795 + 2811273 * 2 ^ 59
def prefixEnd_2811273 : Nat := 4983230072969 + 3 ^ 40 * 2811273 * 2
def baseEnd_2811273 : Nat := 481178100002428205052899

theorem tailTrace_2811273 : CollatzResearch.WordTrace tailWord_2811273 prefixEnd_2811273 481178100002428205052899 := by
  unfold tailWord_2811273
  simp only [CollatzResearch.WordTrace]
  refine ⟨102535549944245523048630473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68357033296163682032420315 102535549944245523048630473)
  ·
    refine ⟨76901662458184142286472855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102535549944245523048630473 76901662458184142286472855)
    ·
      refine ⟨115352493687276213429709283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76901662458184142286472855 115352493687276213429709283)
      ·
        refine ⟨173028740530914320144563925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115352493687276213429709283 173028740530914320144563925)
        ·
          refine ⟨4055361106193304378388217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173028740530914320144563925 4055361106193304378388217)
          ·
            refine ⟨3041520829644978283791163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055361106193304378388217 3041520829644978283791163)
            ·
              refine ⟨4562281244467467425686745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041520829644978283791163 4562281244467467425686745)
              ·
                refine ⟨3421710933350600569265059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562281244467467425686745 3421710933350600569265059)
                ·
                  refine ⟨5132566400025900853897589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421710933350600569265059 5132566400025900853897589)
                  ·
                    refine ⟨481178100002428205052899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5132566400025900853897589 481178100002428205052899)
                    ·
                      rfl

theorem cell23_2811273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_2811273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811273 prefixEnd_2811273 := by exact prefixLift 2811273
  have htrace : WordTrace (prefixWord ++ tailWord_2811273) baseStart_2811273 baseEnd_2811273 := by
    simpa [prefixWord, tailWord_2811273, baseEnd_2811273] using wordTrace_append hprefix tailTrace_2811273
  have hstable : (prefixWord ++ tailWord_2811273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811273).length < 2 ^ (prefixWord ++ tailWord_2811273).sum := by decide
  have hdescent : baseEnd_2811273 < baseStart_2811273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811289 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2811289 : Nat := 118140960795 + 2811289 * 2 ^ 59
def prefixEnd_2811289 : Nat := 4983230072969 + 3 ^ 40 * 2811289 * 2
def baseEnd_2811289 : Nat := 1443542515697756552558623

theorem tailTrace_2811289 : CollatzResearch.WordTrace tailWord_2811289 prefixEnd_2811289 1443542515697756552558623 := by
  unfold tailWord_2811289
  simp only [CollatzResearch.WordTrace]
  refine ⟨102536133512187557781212921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68357422341458371854141947 102536133512187557781212921)
  ·
    refine ⟨76902100134140668335909691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102536133512187557781212921 76902100134140668335909691)
    ·
      refine ⟨115353150201211002503864537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76902100134140668335909691 115353150201211002503864537)
      ·
        refine ⟨86514862650908251877898403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115353150201211002503864537 86514862650908251877898403)
        ·
          refine ⟨129772293976362377816847605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86514862650908251877898403 129772293976362377816847605)
          ·
            refine ⟨12166152560283972920329463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129772293976362377816847605 12166152560283972920329463)
            ·
              refine ⟨18249228840425959380494195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12166152560283972920329463 18249228840425959380494195)
              ·
                refine ⟨27373843260638939070741293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18249228840425959380494195 27373843260638939070741293)
                ·
                  refine ⟨10265191222739602151527985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27373843260638939070741293 10265191222739602151527985)
                  ·
                    refine ⟨7698893417054701613645989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10265191222739602151527985 7698893417054701613645989)
                    ·
                      refine ⟨1443542515697756552558623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7698893417054701613645989 1443542515697756552558623)
                      ·
                        rfl

theorem cell23_2811289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2811289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811289 prefixEnd_2811289 := by exact prefixLift 2811289
  have htrace : WordTrace (prefixWord ++ tailWord_2811289) baseStart_2811289 baseEnd_2811289 := by
    simpa [prefixWord, tailWord_2811289, baseEnd_2811289] using wordTrace_append hprefix tailTrace_2811289
  have hstable : (prefixWord ++ tailWord_2811289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811289).length < 2 ^ (prefixWord ++ tailWord_2811289).sum := by decide
  have hdescent : baseEnd_2811289 < baseStart_2811289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811303 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2811303 : Nat := 118140960795 + 2811303 * 2 ^ 59
def prefixEnd_2811303 : Nat := 4983230072969 + 3 ^ 40 * 2811303 * 2
def baseEnd_2811303 : Nat := 481183234808973165927853

theorem tailTrace_2811303 : CollatzResearch.WordTrace tailWord_2811303 prefixEnd_2811303 481183234808973165927853 := by
  unfold tailWord_2811303
  simp only [CollatzResearch.WordTrace]
  refine ⟨102536644134136838172222563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68357762756091225448148375 102536644134136838172222563)
  ·
    refine ⟨153804966201205257258333845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102536644134136838172222563 153804966201205257258333845)
    ·
      refine ⟨7209607790681496433984399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153804966201205257258333845 7209607790681496433984399)
      ·
        refine ⟨10814411686022244650976599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7209607790681496433984399 10814411686022244650976599)
        ·
          refine ⟨16221617529033366976464899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10814411686022244650976599 16221617529033366976464899)
          ·
            refine ⟨24332426293550050464697349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16221617529033366976464899 24332426293550050464697349)
            ·
              refine ⟨4562329930040634462130753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24332426293550050464697349 4562329930040634462130753)
              ·
                refine ⟨3421747447530475846598065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562329930040634462130753 3421747447530475846598065)
                ·
                  refine ⟨2566310585647856884948549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421747447530475846598065 2566310585647856884948549)
                  ·
                    refine ⟨481183234808973165927853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566310585647856884948549 481183234808973165927853)
                    ·
                      rfl

theorem cell23_2811303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2811303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811303 prefixEnd_2811303 := by exact prefixLift 2811303
  have htrace : WordTrace (prefixWord ++ tailWord_2811303) baseStart_2811303 baseEnd_2811303 := by
    simpa [prefixWord, tailWord_2811303, baseEnd_2811303] using wordTrace_append hprefix tailTrace_2811303
  have hstable : (prefixWord ++ tailWord_2811303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811303).length < 2 ^ (prefixWord ++ tailWord_2811303).sum := by decide
  have hdescent : baseEnd_2811303 < baseStart_2811303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811359 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 6]
def baseStart_2811359 : Nat := 118140960795 + 2811359 * 2 ^ 59
def prefixEnd_2811359 : Nat := 4983230072969 + 3 ^ 40 * 2811359 * 2
def baseEnd_2811359 : Nat := 481192819781190426227767

theorem tailTrace_2811359 : CollatzResearch.WordTrace tailWord_2811359 prefixEnd_2811359 481192819781190426227767 := by
  unfold tailWord_2811359
  simp only [CollatzResearch.WordTrace]
  refine ⟨102538686621933959736261131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68359124414622639824174087 102538686621933959736261131)
  ·
    refine ⟨153808029932900939604391697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102538686621933959736261131 153808029932900939604391697)
    ·
      refine ⟨115356022449675704703293773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153808029932900939604391697 115356022449675704703293773)
      ·
        refine ⟨43258508418628389263735165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115356022449675704703293773 43258508418628389263735165)
        ·
          refine ⟨16221940656985645973900687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43258508418628389263735165 16221940656985645973900687)
          ·
            refine ⟨24332910985478468960851031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16221940656985645973900687 24332910985478468960851031)
            ·
              refine ⟨36499366478217703441276547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24332910985478468960851031 36499366478217703441276547)
              ·
                refine ⟨54749049717326555161914821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36499366478217703441276547 54749049717326555161914821)
                ·
                  refine ⟨10265446821998729092859029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54749049717326555161914821 10265446821998729092859029)
                  ·
                    refine ⟨481192819781190426227767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10265446821998729092859029 481192819781190426227767)
                    ·
                      rfl

theorem cell23_2811359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_2811359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811359 prefixEnd_2811359 := by exact prefixLift 2811359
  have htrace : WordTrace (prefixWord ++ tailWord_2811359) baseStart_2811359 baseEnd_2811359 := by
    simpa [prefixWord, tailWord_2811359, baseEnd_2811359] using wordTrace_append hprefix tailTrace_2811359
  have hstable : (prefixWord ++ tailWord_2811359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811359).length < 2 ^ (prefixWord ++ tailWord_2811359).sum := by decide
  have hdescent : baseEnd_2811359 < baseStart_2811359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811379 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_2811379 : Nat := 118140960795 + 2811379 * 2 ^ 59
def prefixEnd_2811379 : Nat := 4983230072969 + 3 ^ 40 * 2811379 * 2
def baseEnd_2811379 : Nat := 1443588728956661200433209

theorem tailTrace_2811379 : CollatzResearch.WordTrace tailWord_2811379 prefixEnd_2811379 1443588728956661200433209 := by
  unfold tailWord_2811379
  simp only [CollatzResearch.WordTrace]
  refine ⟨102539416081861503151989191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68359610721241002101326127 102539416081861503151989191)
  ·
    refine ⟨153809124122792254727983787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102539416081861503151989191 153809124122792254727983787)
    ·
      refine ⟨230713686184188382091975681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153809124122792254727983787 230713686184188382091975681)
      ·
        refine ⟨173035264638141286568981761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230713686184188382091975681 173035264638141286568981761)
        ·
          refine ⟨129776448478605964926736321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173035264638141286568981761 129776448478605964926736321)
          ·
            refine ⟨97332336358954473695052241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129776448478605964926736321 97332336358954473695052241)
            ·
              refine ⟨72999252269215855271289181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97332336358954473695052241 72999252269215855271289181)
              ·
                refine ⟨27374719600955945726733443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72999252269215855271289181 27374719600955945726733443)
                ·
                  refine ⟨41062079401433918590100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27374719600955945726733443 41062079401433918590100165)
                  ·
                    refine ⟨7699139887768859735643781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41062079401433918590100165 7699139887768859735643781)
                    ·
                      refine ⟨1443588728956661200433209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7699139887768859735643781 1443588728956661200433209)
                      ·
                        rfl

theorem cell23_2811379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_2811379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811379 prefixEnd_2811379 := by exact prefixLift 2811379
  have htrace : WordTrace (prefixWord ++ tailWord_2811379) baseStart_2811379 baseEnd_2811379 := by
    simpa [prefixWord, tailWord_2811379, baseEnd_2811379] using wordTrace_append hprefix tailTrace_2811379
  have hstable : (prefixWord ++ tailWord_2811379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811379).length < 2 ^ (prefixWord ++ tailWord_2811379).sum := by decide
  have hdescent : baseEnd_2811379 < baseStart_2811379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811459 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_2811459 : Nat := 118140960795 + 2811459 * 2 ^ 59
def prefixEnd_2811459 : Nat := 4983230072969 + 3 ^ 40 * 2811459 * 2
def baseEnd_2811459 : Nat := 1443629807409020887432841

theorem tailTrace_2811459 : CollatzResearch.WordTrace tailWord_2811459 prefixEnd_2811459 1443629807409020887432841 := by
  unfold tailWord_2811459
  simp only [CollatzResearch.WordTrace]
  refine ⟨102542333921571676814901431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68361555947714451209934287 102542333921571676814901431)
  ·
    refine ⟨153813500882357515222352147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102542333921571676814901431 153813500882357515222352147)
    ·
      refine ⟨230720251323536272833528221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153813500882357515222352147 230720251323536272833528221)
      ·
        refine ⟨86520094246326102312573083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230720251323536272833528221 86520094246326102312573083)
        ·
          refine ⟨129780141369489153468859625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86520094246326102312573083 129780141369489153468859625)
          ·
            refine ⟨97335106027116865101644719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129780141369489153468859625 97335106027116865101644719)
            ·
              refine ⟨146002659040675297652467079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97335106027116865101644719 146002659040675297652467079)
              ·
                refine ⟨219003988561012946478700619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146002659040675297652467079 219003988561012946478700619)
                ·
                  refine ⟨328505982841519419718050929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219003988561012946478700619 328505982841519419718050929)
                  ·
                    refine ⟨246379487131139564788538197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328505982841519419718050929 246379487131139564788538197)
                    ·
                      refine ⟨1443629807409020887432841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 246379487131139564788538197 1443629807409020887432841)
                      ·
                        rfl

theorem cell23_2811459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_2811459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811459 prefixEnd_2811459 := by exact prefixLift 2811459
  have htrace : WordTrace (prefixWord ++ tailWord_2811459) baseStart_2811459 baseEnd_2811459 := by
    simpa [prefixWord, tailWord_2811459, baseEnd_2811459] using wordTrace_append hprefix tailTrace_2811459
  have hstable : (prefixWord ++ tailWord_2811459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811459).length < 2 ^ (prefixWord ++ tailWord_2811459).sum := by decide
  have hdescent : baseEnd_2811459 < baseStart_2811459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811473 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_2811473 : Nat := 118140960795 + 2811473 * 2 ^ 59
def prefixEnd_2811473 : Nat := 4983230072969 + 3 ^ 40 * 2811473 * 2
def baseEnd_2811473 : Nat := 1443636996138183832657777

theorem tailTrace_2811473 : CollatzResearch.WordTrace tailWord_2811473 prefixEnd_2811473 1443636996138183832657777 := by
  unfold tailWord_2811473
  simp only [CollatzResearch.WordTrace]
  refine ⟨102542844543520957205911073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68361896362347304803940715 102542844543520957205911073)
  ·
    refine ⟨76907133407640717904433305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102542844543520957205911073 76907133407640717904433305)
    ·
      refine ⟨57680350055730538428324979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76907133407640717904433305 57680350055730538428324979)
      ·
        refine ⟨86520525083595807642487469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57680350055730538428324979 86520525083595807642487469)
        ·
          refine ⟨32445196906348427865932801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86520525083595807642487469 32445196906348427865932801)
          ·
            refine ⟨24333897679761320899449601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32445196906348427865932801 24333897679761320899449601)
            ·
              refine ⟨18250423259820990674587201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24333897679761320899449601 18250423259820990674587201)
              ·
                refine ⟨13687817444865743005940401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18250423259820990674587201 13687817444865743005940401)
                ·
                  refine ⟨10265863083649307254455301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13687817444865743005940401 10265863083649307254455301)
                  ·
                    refine ⟨1924849328184245110210369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10265863083649307254455301 1924849328184245110210369)
                    ·
                      refine ⟨1443636996138183832657777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1924849328184245110210369 1443636996138183832657777)
                      ·
                        rfl

theorem cell23_2811473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_2811473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811473 prefixEnd_2811473 := by exact prefixLift 2811473
  have htrace : WordTrace (prefixWord ++ tailWord_2811473) baseStart_2811473 baseEnd_2811473 := by
    simpa [prefixWord, tailWord_2811473, baseEnd_2811473] using wordTrace_append hprefix tailTrace_2811473
  have hstable : (prefixWord ++ tailWord_2811473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811473).length < 2 ^ (prefixWord ++ tailWord_2811473).sum := by decide
  have hdescent : baseEnd_2811473 < baseStart_2811473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811476 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2811476 : Nat := 118140960795 + 2811476 * 2 ^ 59
def prefixEnd_2811476 : Nat := 4983230072969 + 3 ^ 40 * 2811476 * 2
def baseEnd_2811476 : Nat := 1443638536580147320920263

theorem tailTrace_2811476 : CollatzResearch.WordTrace tailWord_2811476 prefixEnd_2811476 1443638536580147320920263 := by
  unfold tailWord_2811476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51271476981255044359135141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68361969308340059145513521 51271476981255044359135141)
  ·
    refine ⟨9613401933985320817337839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51271476981255044359135141 9613401933985320817337839)
    ·
      refine ⟨14420102900977981226006759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613401933985320817337839 14420102900977981226006759)
      ·
        refine ⟨21630154351466971839010139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14420102900977981226006759 21630154351466971839010139)
        ·
          refine ⟨32445231527200457758515209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21630154351466971839010139 32445231527200457758515209)
          ·
            refine ⟨24333923645400343318886407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32445231527200457758515209 24333923645400343318886407)
            ·
              refine ⟨36500885468100514978329611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24333923645400343318886407 36500885468100514978329611)
              ·
                refine ⟨54751328202150772467494417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36500885468100514978329611 54751328202150772467494417)
                ·
                  refine ⟨41063496151613079350620813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54751328202150772467494417 41063496151613079350620813)
                  ·
                    refine ⟨15398811056854904756482805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41063496151613079350620813 15398811056854904756482805)
                    ·
                      refine ⟨1443638536580147320920263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15398811056854904756482805 1443638536580147320920263)
                      ·
                        rfl

theorem cell23_2811476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2811476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811476 prefixEnd_2811476 := by exact prefixLift 2811476
  have htrace : WordTrace (prefixWord ++ tailWord_2811476) baseStart_2811476 baseEnd_2811476 := by
    simpa [prefixWord, tailWord_2811476, baseEnd_2811476] using wordTrace_append hprefix tailTrace_2811476
  have hstable : (prefixWord ++ tailWord_2811476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811476).length < 2 ^ (prefixWord ++ tailWord_2811476).sum := by decide
  have hdescent : baseEnd_2811476 < baseStart_2811476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811510 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2811510 : Nat := 118140960795 + 2811510 * 2 ^ 59
def prefixEnd_2811510 : Nat := 4983230072969 + 3 ^ 40 * 2811510 * 2
def baseEnd_2811510 : Nat := 1443655994922400187895107

theorem tailTrace_2811510 : CollatzResearch.WordTrace tailWord_2811510 prefixEnd_2811510 1443655994922400187895107 := by
  unfold tailWord_2811510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409012127774182032812999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68362796029591275016671989 6409012127774182032812999)
  ·
    refine ⟨9613518191661273049219499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6409012127774182032812999 9613518191661273049219499)
    ·
      refine ⟨14420277287491909573829249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613518191661273049219499 14420277287491909573829249)
      ·
        refine ⟨10815207965618932180371937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14420277287491909573829249 10815207965618932180371937)
        ·
          refine ⟨8111405974214199135278953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815207965618932180371937 8111405974214199135278953)
          ·
            refine ⟨6083554480660649351459215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111405974214199135278953 6083554480660649351459215)
            ·
              refine ⟨9125331720990974027188823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083554480660649351459215 9125331720990974027188823)
              ·
                refine ⟨13687997581486461040783235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9125331720990974027188823 13687997581486461040783235)
                ·
                  refine ⟨20531996372229691561174853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13687997581486461040783235 20531996372229691561174853)
                  ·
                    refine ⟨3849749319793067167720285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20531996372229691561174853 3849749319793067167720285)
                    ·
                      refine ⟨1443655994922400187895107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3849749319793067167720285 1443655994922400187895107)
                      ·
                        rfl

theorem cell23_2811510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2811510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811510 prefixEnd_2811510 := by exact prefixLift 2811510
  have htrace : WordTrace (prefixWord ++ tailWord_2811510) baseStart_2811510 baseEnd_2811510 := by
    simpa [prefixWord, tailWord_2811510, baseEnd_2811510] using wordTrace_append hprefix tailTrace_2811510
  have hstable : (prefixWord ++ tailWord_2811510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811510).length < 2 ^ (prefixWord ++ tailWord_2811510).sum := by decide
  have hdescent : baseEnd_2811510 < baseStart_2811510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811517 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_2811517 : Nat := 118140960795 + 2811517 * 2 ^ 59
def prefixEnd_2811517 : Nat := 4983230072969 + 3 ^ 40 * 2811517 * 2
def baseEnd_2811517 : Nat := 481219863095660553502525

theorem tailTrace_2811517 : CollatzResearch.WordTrace tailWord_2811517 prefixEnd_2811517 481219863095660553502525 := by
  unfold tailWord_2811517
  simp only [CollatzResearch.WordTrace]
  refine ⟨102544449355361552720512805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68362966236907701813675203 102544449355361552720512805)
  ·
    refine ⟨19227084254130291135096151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102544449355361552720512805 19227084254130291135096151)
    ·
      refine ⟨28840626381195436702644227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227084254130291135096151 28840626381195436702644227)
      ·
        refine ⟨43260939571793155053966341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28840626381195436702644227 43260939571793155053966341)
        ·
          refine ⟨8111426169711216572618689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43260939571793155053966341 8111426169711216572618689)
          ·
            refine ⟨6083569627283412429464017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111426169711216572618689 6083569627283412429464017)
            ·
              refine ⟨4562677220462559322098013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6083569627283412429464017 4562677220462559322098013)
              ·
                refine ⟨1711003957673459745786755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4562677220462559322098013 1711003957673459745786755)
                ·
                  refine ⟨2566505936510189618680133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711003957673459745786755 2566505936510189618680133)
                  ·
                    refine ⟨481219863095660553502525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2566505936510189618680133 481219863095660553502525)
                    ·
                      rfl

theorem cell23_2811517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_2811517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811517 prefixEnd_2811517 := by exact prefixLift 2811517
  have htrace : WordTrace (prefixWord ++ tailWord_2811517) baseStart_2811517 baseEnd_2811517 := by
    simpa [prefixWord, tailWord_2811517, baseEnd_2811517] using wordTrace_append hprefix tailTrace_2811517
  have hstable : (prefixWord ++ tailWord_2811517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811517).length < 2 ^ (prefixWord ++ tailWord_2811517).sum := by decide
  have hdescent : baseEnd_2811517 < baseStart_2811517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811523 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 3]
def baseStart_2811523 : Nat := 118140960795 + 2811523 * 2 ^ 59
def prefixEnd_2811523 : Nat := 4983230072969 + 3 ^ 40 * 2811523 * 2
def baseEnd_2811523 : Nat := 1443662670170908637032547

theorem tailTrace_2811523 : CollatzResearch.WordTrace tailWord_2811523 prefixEnd_2811523 1443662670170908637032547 := by
  unfold tailWord_2811523
  simp only [CollatzResearch.WordTrace]
  refine ⟨102544668193339815745231223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68363112128893210496820815 102544668193339815745231223)
  ·
    refine ⟨153817002290009723617846835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102544668193339815745231223 153817002290009723617846835)
    ·
      refine ⟨230725503435014585426770253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153817002290009723617846835 230725503435014585426770253)
      ·
        refine ⟨86522063788130469535038845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230725503435014585426770253 86522063788130469535038845)
        ·
          refine ⟨32445773920548926075639567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86522063788130469535038845 32445773920548926075639567)
          ·
            refine ⟨48668660880823389113459351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32445773920548926075639567 48668660880823389113459351)
            ·
              refine ⟨73002991321235083670189027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48668660880823389113459351 73002991321235083670189027)
              ·
                refine ⟨109504486981852625505283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73002991321235083670189027 109504486981852625505283541)
                ·
                  refine ⟨2566511413637170910280083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 109504486981852625505283541 2566511413637170910280083)
                  ·
                    refine ⟨3849767120455756365420125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2566511413637170910280083 3849767120455756365420125)
                    ·
                      refine ⟨1443662670170908637032547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3849767120455756365420125 1443662670170908637032547)
                      ·
                        rfl

theorem cell23_2811523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_2811523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811523 prefixEnd_2811523 := by exact prefixLift 2811523
  have htrace : WordTrace (prefixWord ++ tailWord_2811523) baseStart_2811523 baseEnd_2811523 := by
    simpa [prefixWord, tailWord_2811523, baseEnd_2811523] using wordTrace_append hprefix tailTrace_2811523
  have hstable : (prefixWord ++ tailWord_2811523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811523).length < 2 ^ (prefixWord ++ tailWord_2811523).sum := by decide
  have hdescent : baseEnd_2811523 < baseStart_2811523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811530 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_2811530 : Nat := 118140960795 + 2811530 * 2 ^ 59
def prefixEnd_2811530 : Nat := 4983230072969 + 3 ^ 40 * 2811530 * 2
def baseEnd_2811530 : Nat := 160407362726165567738335

theorem tailTrace_2811530 : CollatzResearch.WordTrace tailWord_2811530 prefixEnd_2811530 160407362726165567738335 := by
  unfold tailWord_2811530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636230876078613985184011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68363282336209637293824029 25636230876078613985184011)
  ·
    refine ⟨38454346314117920977776017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25636230876078613985184011 38454346314117920977776017)
    ·
      refine ⟨28840759735588440733332013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38454346314117920977776017 28840759735588440733332013)
      ·
        refine ⟨10815284900845665274999505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28840759735588440733332013 10815284900845665274999505)
        ·
          refine ⟨8111463675634248956249629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815284900845665274999505 8111463675634248956249629)
          ·
            refine ⟨3041798878362843358593611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8111463675634248956249629 3041798878362843358593611)
            ·
              refine ⟨4562698317544265037890417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041798878362843358593611 4562698317544265037890417)
              ·
                refine ⟨3422023738158198778417813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562698317544265037890417 3422023738158198778417813)
                ·
                  refine ⟨160407362726165567738335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3422023738158198778417813 160407362726165567738335)
                  ·
                    rfl

theorem cell23_2811530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_2811530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811530 prefixEnd_2811530 := by exact prefixLift 2811530
  have htrace : WordTrace (prefixWord ++ tailWord_2811530) baseStart_2811530 baseEnd_2811530 := by
    simpa [prefixWord, tailWord_2811530, baseEnd_2811530] using wordTrace_append hprefix tailTrace_2811530
  have hstable : (prefixWord ++ tailWord_2811530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811530).length < 2 ^ (prefixWord ++ tailWord_2811530).sum := by decide
  have hdescent : baseEnd_2811530 < baseStart_2811530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811580 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2811580 : Nat := 118140960795 + 2811580 * 2 ^ 59
def prefixEnd_2811580 : Nat := 4983230072969 + 3 ^ 40 * 2811580 * 2
def baseEnd_2811580 : Nat := 1443691938568214914019785

theorem tailTrace_2811580 : CollatzResearch.WordTrace tailWord_2811580 prefixEnd_2811580 1443691938568214914019785 := by
  unfold tailWord_2811580
  simp only [CollatzResearch.WordTrace]
  refine ⟨51273373577066657240028097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68364498102755542986704129 51273373577066657240028097)
  ·
    refine ⟨38455030182799992930021073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51273373577066657240028097 38455030182799992930021073)
    ·
      refine ⟨28841272637099994697515805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38455030182799992930021073 28841272637099994697515805)
      ·
        refine ⟨10815477238912498011568427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28841272637099994697515805 10815477238912498011568427)
        ·
          refine ⟨16223215858368747017352641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815477238912498011568427 16223215858368747017352641)
          ·
            refine ⟨12167411893776560263014481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16223215858368747017352641 12167411893776560263014481)
            ·
              refine ⟨9125558920332420197260861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12167411893776560263014481 9125558920332420197260861)
              ·
                refine ⟨3422084595124657573972823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9125558920332420197260861 3422084595124657573972823)
                ·
                  refine ⟨5133126892686986360959235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422084595124657573972823 5133126892686986360959235)
                  ·
                    refine ⟨7699690339030479541438853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133126892686986360959235 7699690339030479541438853)
                    ·
                      refine ⟨1443691938568214914019785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7699690339030479541438853 1443691938568214914019785)
                      ·
                        rfl

theorem cell23_2811580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2811580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811580 prefixEnd_2811580 := by exact prefixLift 2811580
  have htrace : WordTrace (prefixWord ++ tailWord_2811580) baseStart_2811580 baseEnd_2811580 := by
    simpa [prefixWord, tailWord_2811580, baseEnd_2811580] using wordTrace_append hprefix tailTrace_2811580
  have hstable : (prefixWord ++ tailWord_2811580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811580).length < 2 ^ (prefixWord ++ tailWord_2811580).sum := by decide
  have hdescent : baseEnd_2811580 < baseStart_2811580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811583 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_2811583 : Nat := 118140960795 + 2811583 * 2 ^ 59
def prefixEnd_2811583 : Nat := 4983230072969 + 3 ^ 40 * 2811583 * 2
def baseEnd_2811583 : Nat := 1443693479010178402282271

theorem tailTrace_2811583 : CollatzResearch.WordTrace tailWord_2811583 prefixEnd_2811583 1443693479010178402282271 := by
  unfold tailWord_2811583
  simp only [CollatzResearch.WordTrace]
  refine ⟨102546856573122445992415403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68364571048748297328276935 102546856573122445992415403)
  ·
    refine ⟨153820284859683668988623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102546856573122445992415403 153820284859683668988623105)
    ·
      refine ⟨115365213644762751741467329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153820284859683668988623105 115365213644762751741467329)
      ·
        refine ⟨86523910233572063806100497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115365213644762751741467329 86523910233572063806100497)
        ·
          refine ⟨64892932675179047854575373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86523910233572063806100497 64892932675179047854575373)
          ·
            refine ⟨24334849753192142945465765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64892932675179047854575373 24334849753192142945465765)
            ·
              refine ⟨4562784328723526802274831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24334849753192142945465765 4562784328723526802274831)
              ·
                refine ⟨6844176493085290203412247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562784328723526802274831 6844176493085290203412247)
                ·
                  refine ⟨10266264739627935305118371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844176493085290203412247 10266264739627935305118371)
                  ·
                    refine ⟨15399397109441902957677557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10266264739627935305118371 15399397109441902957677557)
                    ·
                      refine ⟨1443693479010178402282271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15399397109441902957677557 1443693479010178402282271)
                      ·
                        rfl

theorem cell23_2811583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_2811583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811583 prefixEnd_2811583 := by exact prefixLift 2811583
  have htrace : WordTrace (prefixWord ++ tailWord_2811583) baseStart_2811583 baseEnd_2811583 := by
    simpa [prefixWord, tailWord_2811583, baseEnd_2811583] using wordTrace_append hprefix tailTrace_2811583
  have hstable : (prefixWord ++ tailWord_2811583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811583).length < 2 ^ (prefixWord ++ tailWord_2811583).sum := by decide
  have hdescent : baseEnd_2811583 < baseStart_2811583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811630 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_2811630 : Nat := 118140960795 + 2811630 * 2 ^ 59
def prefixEnd_2811630 : Nat := 4983230072969 + 3 ^ 40 * 2811630 * 2
def baseEnd_2811630 : Nat := 1443717612600939718394555

theorem tailTrace_2811630 : CollatzResearch.WordTrace tailWord_2811630 prefixEnd_2811630 1443717612600939718394555 := by
  unfold tailWord_2811630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818571350494021627422043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68365713869301448679584229 12818571350494021627422043)
  ·
    refine ⟨19227857025741032441133065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12818571350494021627422043 19227857025741032441133065)
    ·
      refine ⟨14420892769305774330849799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19227857025741032441133065 14420892769305774330849799)
      ·
        refine ⟨21631339153958661496274699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14420892769305774330849799 21631339153958661496274699)
        ·
          refine ⟨32447008730937992244412049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21631339153958661496274699 32447008730937992244412049)
          ·
            refine ⟨24335256548203494183309037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32447008730937992244412049 24335256548203494183309037)
            ·
              refine ⟨9125721205576310318740889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24335256548203494183309037 9125721205576310318740889)
              ·
                refine ⟨6844290904182232739055667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9125721205576310318740889 6844290904182232739055667)
                ·
                  refine ⟨10266436356273349108583501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844290904182232739055667 10266436356273349108583501)
                  ·
                    refine ⟨3849913633602505915718813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10266436356273349108583501 3849913633602505915718813)
                    ·
                      refine ⟨1443717612600939718394555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3849913633602505915718813 1443717612600939718394555)
                      ·
                        rfl

theorem cell23_2811630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_2811630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811630 prefixEnd_2811630 := by exact prefixLift 2811630
  have htrace : WordTrace (prefixWord ++ tailWord_2811630) baseStart_2811630 baseEnd_2811630 := by
    simpa [prefixWord, tailWord_2811630, baseEnd_2811630] using wordTrace_append hprefix tailTrace_2811630
  have hstable : (prefixWord ++ tailWord_2811630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811630).length < 2 ^ (prefixWord ++ tailWord_2811630).sum := by decide
  have hdescent : baseEnd_2811630 < baseStart_2811630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811704 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_2811704 : Nat := 118140960795 + 2811704 * 2 ^ 59
def prefixEnd_2811704 : Nat := 4983230072969 + 3 ^ 40 * 2811704 * 2
def baseEnd_2811704 : Nat := 1443755610169372428869215

theorem tailTrace_2811704 : CollatzResearch.WordTrace tailWord_2811704 prefixEnd_2811704 1443755610169372428869215 := by
  unfold tailWord_2811704
  simp only [CollatzResearch.WordTrace]
  refine ⟨51275634902842041828785083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68367513203789389105046777 51275634902842041828785083)
  ·
    refine ⟨76913452354263062743177625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51275634902842041828785083 76913452354263062743177625)
    ·
      refine ⟨57685089265697297057383219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76913452354263062743177625 57685089265697297057383219)
      ·
        refine ⟨86527633898545945586074829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57685089265697297057383219 86527633898545945586074829)
        ·
          refine ⟨32447862711954729594778061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86527633898545945586074829 32447862711954729594778061)
          ·
            refine ⟨12167948516983023598041773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32447862711954729594778061 12167948516983023598041773)
            ·
              refine ⟨4562980693868633849265665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12167948516983023598041773 4562980693868633849265665)
              ·
                refine ⟨3422235520401475386949249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562980693868633849265665 3422235520401475386949249)
                ·
                  refine ⟨2566676640301106540211937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422235520401475386949249 2566676640301106540211937)
                  ·
                    refine ⟨1925007480225829905158953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566676640301106540211937 1925007480225829905158953)
                    ·
                      refine ⟨1443755610169372428869215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925007480225829905158953 1443755610169372428869215)
                      ·
                        rfl

theorem cell23_2811704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_2811704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811704 prefixEnd_2811704 := by exact prefixLift 2811704
  have htrace : WordTrace (prefixWord ++ tailWord_2811704) baseStart_2811704 baseEnd_2811704 := by
    simpa [prefixWord, tailWord_2811704, baseEnd_2811704] using wordTrace_append hprefix tailTrace_2811704
  have hstable : (prefixWord ++ tailWord_2811704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811704).length < 2 ^ (prefixWord ++ tailWord_2811704).sum := by decide
  have hdescent : baseEnd_2811704 < baseStart_2811704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811710 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_2811710 : Nat := 118140960795 + 2811710 * 2 ^ 59
def prefixEnd_2811710 : Nat := 4983230072969 + 3 ^ 40 * 2811710 * 2
def baseEnd_2811710 : Nat := 160417632339255489488243

theorem tailTrace_2811710 : CollatzResearch.WordTrace tailWord_2811710 prefixEnd_2811710 160417632339255489488243 := by
  unfold tailWord_2811710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818936080457793335286073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68367659095774897788192389 12818936080457793335286073)
  ·
    refine ⟨9614202060343345001464555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12818936080457793335286073 9614202060343345001464555)
    ·
      refine ⟨14421303090515017502196833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614202060343345001464555 14421303090515017502196833)
      ·
        refine ⟨10815977317886263126647625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14421303090515017502196833 10815977317886263126647625)
        ·
          refine ⟨8111982988414697344985719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815977317886263126647625 8111982988414697344985719)
          ·
            refine ⟨12167974482622046017478579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111982988414697344985719 12167974482622046017478579)
            ·
              refine ⟨18251961723933069026217869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167974482622046017478579 18251961723933069026217869)
              ·
                refine ⟨6844485646474900884831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251961723933069026217869 6844485646474900884831701)
                ·
                  refine ⟨160417632339255489488243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6844485646474900884831701 160417632339255489488243)
                  ·
                    rfl

theorem cell23_2811710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_2811710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811710 prefixEnd_2811710 := by exact prefixLift 2811710
  have htrace : WordTrace (prefixWord ++ tailWord_2811710) baseStart_2811710 baseEnd_2811710 := by
    simpa [prefixWord, tailWord_2811710, baseEnd_2811710] using wordTrace_append hprefix tailTrace_2811710
  have hstable : (prefixWord ++ tailWord_2811710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811710).length < 2 ^ (prefixWord ++ tailWord_2811710).sum := by decide
  have hdescent : baseEnd_2811710 < baseStart_2811710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811720 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2811720 : Nat := 118140960795 + 2811720 * 2 ^ 59
def prefixEnd_2811720 : Nat := 4983230072969 + 3 ^ 40 * 2811720 * 2
def baseEnd_2811720 : Nat := 1443763825859844366269141

theorem tailTrace_2811720 : CollatzResearch.WordTrace tailWord_2811720 prefixEnd_2811720 1443763825859844366269141 := by
  unfold tailWord_2811720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51275926686813059195076307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68367902249084078926768409 51275926686813059195076307)
  ·
    refine ⟨76913890030219588792614461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51275926686813059195076307 76913890030219588792614461)
    ·
      refine ⟨28842708761332345797230423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76913890030219588792614461 28842708761332345797230423)
      ·
        refine ⟨43264063141998518695845635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28842708761332345797230423 43264063141998518695845635)
        ·
          refine ⟨64896094712997778043768453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43264063141998518695845635 64896094712997778043768453)
          ·
            refine ⟨12168017758687083383206585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64896094712997778043768453 12168017758687083383206585)
            ·
              refine ⟨9126013319015312537404939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12168017758687083383206585 9126013319015312537404939)
              ·
                refine ⟨13689019978522968806107409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126013319015312537404939 13689019978522968806107409)
                ·
                  refine ⟨10266764983892226604580557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13689019978522968806107409 10266764983892226604580557)
                  ·
                    refine ⟨3850036868959584976717709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10266764983892226604580557 3850036868959584976717709)
                    ·
                      refine ⟨1443763825859844366269141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850036868959584976717709 1443763825859844366269141)
                      ·
                        rfl

theorem cell23_2811720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2811720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811720 prefixEnd_2811720 := by exact prefixLift 2811720
  have htrace : WordTrace (prefixWord ++ tailWord_2811720) baseStart_2811720 baseEnd_2811720 := by
    simpa [prefixWord, tailWord_2811720, baseEnd_2811720] using wordTrace_append hprefix tailTrace_2811720
  have hstable : (prefixWord ++ tailWord_2811720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811720).length < 2 ^ (prefixWord ++ tailWord_2811720).sum := by decide
  have hdescent : baseEnd_2811720 < baseStart_2811720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811780 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2811780 : Nat := 118140960795 + 2811780 * 2 ^ 59
def prefixEnd_2811780 : Nat := 4983230072969 + 3 ^ 40 * 2811780 * 2
def baseEnd_2811780 : Nat := 1443794634699114131518865

theorem tailTrace_2811780 : CollatzResearch.WordTrace tailWord_2811780 prefixEnd_2811780 1443794634699114131518865 := by
  unfold tailWord_2811780
  simp only [CollatzResearch.WordTrace]
  refine ⟨51277020876704374318668397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68369361168939165758224529 51277020876704374318668397)
  ·
    refine ⟨19228882828764140369500649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51277020876704374318668397 19228882828764140369500649)
    ·
      refine ⟨14421662121573105277125487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19228882828764140369500649 14421662121573105277125487)
      ·
        refine ⟨21632493182359657915688231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14421662121573105277125487 21632493182359657915688231)
        ·
          refine ⟨32448739773539486873532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21632493182359657915688231 32448739773539486873532347)
          ·
            refine ⟨48673109660309230310298521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448739773539486873532347 48673109660309230310298521)
            ·
              refine ⟨36504832245231922732723891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48673109660309230310298521 36504832245231922732723891)
              ·
                refine ⟨54757248367847884099085837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36504832245231922732723891 54757248367847884099085837)
                ·
                  refine ⟨20533968137942956537157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54757248367847884099085837 20533968137942956537157189)
                  ·
                    refine ⟨3850119025864304350716973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20533968137942956537157189 3850119025864304350716973)
                    ·
                      refine ⟨1443794634699114131518865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850119025864304350716973 1443794634699114131518865)
                      ·
                        rfl

theorem cell23_2811780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2811780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811780 prefixEnd_2811780 := by exact prefixLift 2811780
  have htrace : WordTrace (prefixWord ++ tailWord_2811780) baseStart_2811780 baseEnd_2811780 := by
    simpa [prefixWord, tailWord_2811780, baseEnd_2811780] using wordTrace_append hprefix tailTrace_2811780
  have hstable : (prefixWord ++ tailWord_2811780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811780).length < 2 ^ (prefixWord ++ tailWord_2811780).sum := by decide
  have hdescent : baseEnd_2811780 < baseStart_2811780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811794 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2811794 : Nat := 118140960795 + 2811794 * 2 ^ 59
def prefixEnd_2811794 : Nat := 4983230072969 + 3 ^ 40 * 2811794 * 2
def baseEnd_2811794 : Nat := 1443801823428277076743801

theorem tailTrace_2811794 : CollatzResearch.WordTrace tailWord_2811794 prefixEnd_2811794 1443801823428277076743801 := by
  unfold tailWord_2811794
  simp only [CollatzResearch.WordTrace]
  refine ⟨25638638093839507257086609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68369701583572019352230957 25638638093839507257086609)
  ·
    refine ⟨19228978570379630442814957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25638638093839507257086609 19228978570379630442814957)
    ·
      refine ⟨7210866963892361416055609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19228978570379630442814957 7210866963892361416055609)
      ·
        refine ⟨5408150222919271062041707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7210866963892361416055609 5408150222919271062041707)
        ·
          refine ⟨8112225334378906593062561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408150222919271062041707 8112225334378906593062561)
          ·
            refine ⟨6084169000784179944796921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8112225334378906593062561 6084169000784179944796921)
            ·
              refine ⟨4563126750588134958597691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6084169000784179944796921 4563126750588134958597691)
              ·
                refine ⟨6844690125882202437896537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563126750588134958597691 6844690125882202437896537)
                ·
                  refine ⟨5133517594411651828422403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844690125882202437896537 5133517594411651828422403)
                  ·
                    refine ⟨7700276391617477742633605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133517594411651828422403 7700276391617477742633605)
                    ·
                      refine ⟨1443801823428277076743801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7700276391617477742633605 1443801823428277076743801)
                      ·
                        rfl

theorem cell23_2811794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2811794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811794 prefixEnd_2811794 := by exact prefixLift 2811794
  have htrace : WordTrace (prefixWord ++ tailWord_2811794) baseStart_2811794 baseEnd_2811794 := by
    simpa [prefixWord, tailWord_2811794, baseEnd_2811794] using wordTrace_append hprefix tailTrace_2811794
  have hstable : (prefixWord ++ tailWord_2811794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811794).length < 2 ^ (prefixWord ++ tailWord_2811794).sum := by decide
  have hdescent : baseEnd_2811794 < baseStart_2811794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811797 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_2811797 : Nat := 118140960795 + 2811797 * 2 ^ 59
def prefixEnd_2811797 : Nat := 4983230072969 + 3 ^ 40 * 2811797 * 2
def baseEnd_2811797 : Nat := 1443803363870240565006287

theorem tailTrace_2811797 : CollatzResearch.WordTrace tailWord_2811797 prefixEnd_2811797 1443803363870240565006287 := by
  unfold tailWord_2811797
  simp only [CollatzResearch.WordTrace]
  refine ⟨102554661794347160540705645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68369774529564773693803763 102554661794347160540705645)
  ·
    refine ⟨38457998172880185202764617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102554661794347160540705645 38457998172880185202764617)
    ·
      refine ⟨28843498629660138902073463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38457998172880185202764617 28843498629660138902073463)
      ·
        refine ⟨43265247944490208353110195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28843498629660138902073463 43265247944490208353110195)
        ·
          refine ⟨64897871916735312529665293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43265247944490208353110195 64897871916735312529665293)
          ·
            refine ⟨24336701968775742198624485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64897871916735312529665293 24336701968775742198624485)
            ·
              refine ⟨4563131619145451662242091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24336701968775742198624485 4563131619145451662242091)
              ·
                refine ⟨6844697428718177493363137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563131619145451662242091 6844697428718177493363137)
                ·
                  refine ⟨5133523071538633120022353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844697428718177493363137 5133523071538633120022353)
                  ·
                    refine ⟨3850142303653974840016765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133523071538633120022353 3850142303653974840016765)
                    ·
                      refine ⟨1443803363870240565006287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850142303653974840016765 1443803363870240565006287)
                      ·
                        rfl

theorem cell23_2811797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_2811797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811797 prefixEnd_2811797 := by exact prefixLift 2811797
  have htrace : WordTrace (prefixWord ++ tailWord_2811797) baseStart_2811797 baseEnd_2811797 := by
    simpa [prefixWord, tailWord_2811797, baseEnd_2811797] using wordTrace_append hprefix tailTrace_2811797
  have hstable : (prefixWord ++ tailWord_2811797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811797).length < 2 ^ (prefixWord ++ tailWord_2811797).sum := by decide
  have hdescent : baseEnd_2811797 < baseStart_2811797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811827 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 3]
def baseStart_2811827 : Nat := 118140960795 + 2811827 * 2 ^ 59
def prefixEnd_2811827 : Nat := 4983230072969 + 3 ^ 40 * 2811827 * 2
def baseEnd_2811827 : Nat := 1443818768289875447631149

theorem tailTrace_2811827 : CollatzResearch.WordTrace tailWord_2811827 prefixEnd_2811827 1443818768289875447631149 := by
  unfold tailWord_2811827
  simp only [CollatzResearch.WordTrace]
  refine ⟨102555755984238475664297735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68370503989492317109531823 102555755984238475664297735)
  ·
    refine ⟨153833633976357713496446603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102555755984238475664297735 153833633976357713496446603)
    ·
      refine ⟨230750450964536570244669905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153833633976357713496446603 230750450964536570244669905)
      ·
        refine ⟨173062838223402427683502429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230750450964536570244669905 173062838223402427683502429)
        ·
          refine ⟨64898564333775910381313411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173062838223402427683502429 64898564333775910381313411)
          ·
            refine ⟨97347846500663865571970117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64898564333775910381313411 97347846500663865571970117)
            ·
              refine ⟨18252721218874474794744397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97347846500663865571970117 18252721218874474794744397)
              ·
                refine ⟨6844770457077928048029149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18252721218874474794744397 6844770457077928048029149)
                ·
                  refine ⟨2566788921404223018010931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6844770457077928048029149 2566788921404223018010931)
                  ·
                    refine ⟨3850183382106334527016397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2566788921404223018010931 3850183382106334527016397)
                    ·
                      refine ⟨1443818768289875447631149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850183382106334527016397 1443818768289875447631149)
                      ·
                        rfl

theorem cell23_2811827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_2811827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811827 prefixEnd_2811827 := by exact prefixLift 2811827
  have htrace : WordTrace (prefixWord ++ tailWord_2811827) baseStart_2811827 baseEnd_2811827 := by
    simpa [prefixWord, tailWord_2811827, baseEnd_2811827] using wordTrace_append hprefix tailTrace_2811827
  have hstable : (prefixWord ++ tailWord_2811827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811827).length < 2 ^ (prefixWord ++ tailWord_2811827).sum := by decide
  have hdescent : baseEnd_2811827 < baseStart_2811827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811861 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2811861 : Nat := 118140960795 + 2811861 * 2 ^ 59
def prefixEnd_2811861 : Nat := 4983230072969 + 3 ^ 40 * 2811861 * 2
def baseEnd_2811861 : Nat := 1443836226632128314605993

theorem tailTrace_2811861 : CollatzResearch.WordTrace tailWord_2811861 prefixEnd_2811861 1443836226632128314605993 := by
  unfold tailWord_2811861
  simp only [CollatzResearch.WordTrace]
  refine ⟨102556996066115299471035437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68371330710743532980690291 102556996066115299471035437)
  ·
    refine ⟨38458873524793237301638289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102556996066115299471035437 38458873524793237301638289)
    ·
      refine ⟨28844155143594927976228717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38458873524793237301638289 28844155143594927976228717)
      ·
        refine ⟨10816558178848097991085769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28844155143594927976228717 10816558178848097991085769)
        ·
          refine ⟨8112418634136073493314327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10816558178848097991085769 8112418634136073493314327)
          ·
            refine ⟨12168627951204110239971491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8112418634136073493314327 12168627951204110239971491)
            ·
              refine ⟨18252941926806165359957237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12168627951204110239971491 18252941926806165359957237)
              ·
                refine ⟨1711213305638078002495991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18252941926806165359957237 1711213305638078002495991)
                ·
                  refine ⟨2566819958457117003743987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711213305638078002495991 2566819958457117003743987)
                  ·
                    refine ⟨3850229937685675505615981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2566819958457117003743987 3850229937685675505615981)
                    ·
                      refine ⟨1443836226632128314605993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850229937685675505615981 1443836226632128314605993)
                      ·
                        rfl

theorem cell23_2811861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2811861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811861 prefixEnd_2811861 := by exact prefixLift 2811861
  have htrace : WordTrace (prefixWord ++ tailWord_2811861) baseStart_2811861 baseEnd_2811861 := by
    simpa [prefixWord, tailWord_2811861, baseEnd_2811861] using wordTrace_append hprefix tailTrace_2811861
  have hstable : (prefixWord ++ tailWord_2811861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811861).length < 2 ^ (prefixWord ++ tailWord_2811861).sum := by decide
  have hdescent : baseEnd_2811861 < baseStart_2811861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811868 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 6]
def baseStart_2811868 : Nat := 118140960795 + 2811868 * 2 ^ 59
def prefixEnd_2811868 : Nat := 4983230072969 + 3 ^ 40 * 2811868 * 2
def baseEnd_2811868 : Nat := 160426646777412198579829

theorem tailTrace_2811868 : CollatzResearch.WordTrace tailWord_2811868 prefixEnd_2811868 160426646777412198579829 := by
  unfold tailWord_2811868
  simp only [CollatzResearch.WordTrace]
  refine ⟨51278625688544969833270129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68371500918059959777693505 51278625688544969833270129)
  ·
    refine ⟨38458969266408727374952597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51278625688544969833270129 38458969266408727374952597)
    ·
      refine ⟨1802764184362909095700903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38458969266408727374952597 1802764184362909095700903)
      ·
        refine ⟨2704146276544363643551355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802764184362909095700903 2704146276544363643551355)
        ·
          refine ⟨4056219414816545465327033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704146276544363643551355 4056219414816545465327033)
          ·
            refine ⟨3042164561112409098995275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056219414816545465327033 3042164561112409098995275)
            ·
              refine ⟨4563246841668613648492913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042164561112409098995275 4563246841668613648492913)
              ·
                refine ⟨3422435131251460236369685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563246841668613648492913 3422435131251460236369685)
                ·
                  refine ⟨160426646777412198579829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3422435131251460236369685 160426646777412198579829)
                  ·
                    rfl

theorem cell23_2811868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_2811868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811868 prefixEnd_2811868 := by exact prefixLift 2811868
  have htrace : WordTrace (prefixWord ++ tailWord_2811868) baseStart_2811868 baseEnd_2811868 := by
    simpa [prefixWord, tailWord_2811868, baseEnd_2811868] using wordTrace_append hprefix tailTrace_2811868
  have hstable : (prefixWord ++ tailWord_2811868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811868).length < 2 ^ (prefixWord ++ tailWord_2811868).sum := by decide
  have hdescent : baseEnd_2811868 < baseStart_2811868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811880 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2811880 : Nat := 118140960795 + 2811880 * 2 ^ 59
def prefixEnd_2811880 : Nat := 4983230072969 + 3 ^ 40 * 2811880 * 2
def baseEnd_2811880 : Nat := 1443845982764563740268405

theorem tailTrace_2811880 : CollatzResearch.WordTrace tailWord_2811880 prefixEnd_2811880 1443845982764563740268405 := by
  unfold tailWord_2811880
  simp only [CollatzResearch.WordTrace]
  refine ⟨51278844526523232857988547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68371792702030977143984729 51278844526523232857988547)
  ·
    refine ⟨76918266789784849286982821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51278844526523232857988547 76918266789784849286982821)
    ·
      refine ⟨14422175023084659241309279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76918266789784849286982821 14422175023084659241309279)
      ·
        refine ⟨21633262534626988861963919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422175023084659241309279 21633262534626988861963919)
        ·
          refine ⟨32449893801940483292945879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21633262534626988861963919 32449893801940483292945879)
          ·
            refine ⟨48674840702910724939418819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32449893801940483292945879 48674840702910724939418819)
            ·
              refine ⟨73012261054366087409128229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48674840702910724939418819 73012261054366087409128229)
              ·
                refine ⟨13689798947693641389211543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73012261054366087409128229 13689798947693641389211543)
                ·
                  refine ⟨20534698421540462083817315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13689798947693641389211543 20534698421540462083817315)
                  ·
                    refine ⟨30802047632310693125725973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20534698421540462083817315 30802047632310693125725973)
                    ·
                      refine ⟨1443845982764563740268405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30802047632310693125725973 1443845982764563740268405)
                      ·
                        rfl

theorem cell23_2811880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2811880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811880 prefixEnd_2811880 := by exact prefixLift 2811880
  have htrace : WordTrace (prefixWord ++ tailWord_2811880) baseStart_2811880 baseEnd_2811880 := by
    simpa [prefixWord, tailWord_2811880, baseEnd_2811880] using wordTrace_append hprefix tailTrace_2811880
  have hstable : (prefixWord ++ tailWord_2811880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811880).length < 2 ^ (prefixWord ++ tailWord_2811880).sum := by decide
  have hdescent : baseEnd_2811880 < baseStart_2811880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811897 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2811897 : Nat := 118140960795 + 2811897 * 2 ^ 59
def prefixEnd_2811897 : Nat := 4983230072969 + 3 ^ 40 * 2811897 * 2
def baseEnd_2811897 : Nat := 1443854711935690173755827

theorem tailTrace_2811897 : CollatzResearch.WordTrace tailWord_2811897 prefixEnd_2811897 1443854711935690173755827 := by
  unfold tailWord_2811897
  simp only [CollatzResearch.WordTrace]
  refine ⟨102558309093984877619345945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68372206062656585079563963 102558309093984877619345945)
  ·
    refine ⟨76918731820488658214509459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102558309093984877619345945 76918731820488658214509459)
    ·
      refine ⟨115378097730732987321764189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76918731820488658214509459 115378097730732987321764189)
      ·
        refine ⟨43266786649024870245661571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115378097730732987321764189 43266786649024870245661571)
        ·
          refine ⟨64900179973537305368492357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43266786649024870245661571 64900179973537305368492357)
          ·
            refine ⟨12168783745038244756592317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64900179973537305368492357 12168783745038244756592317)
            ·
              refine ⟨4563293904389341783722119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12168783745038244756592317 4563293904389341783722119)
              ·
                refine ⟨6844940856584012675583179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563293904389341783722119 6844940856584012675583179)
                ·
                  refine ⟨10267411284876019013374769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844940856584012675583179 10267411284876019013374769)
                  ·
                    refine ⟨7700558463657014260031077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10267411284876019013374769 7700558463657014260031077)
                    ·
                      refine ⟨1443854711935690173755827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7700558463657014260031077 1443854711935690173755827)
                      ·
                        rfl

theorem cell23_2811897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2811897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811897 prefixEnd_2811897 := by exact prefixLift 2811897
  have htrace : WordTrace (prefixWord ++ tailWord_2811897) baseStart_2811897 baseEnd_2811897 := by
    simpa [prefixWord, tailWord_2811897, baseEnd_2811897] using wordTrace_append hprefix tailTrace_2811897
  have hstable : (prefixWord ++ tailWord_2811897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811897).length < 2 ^ (prefixWord ++ tailWord_2811897).sum := by decide
  have hdescent : baseEnd_2811897 < baseStart_2811897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811961 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2811961 : Nat := 118140960795 + 2811961 * 2 ^ 59
def prefixEnd_2811961 : Nat := 4983230072969 + 3 ^ 40 * 2811961 * 2
def baseEnd_2811961 : Nat := 1443887574697577923355533

theorem tailTrace_2811961 : CollatzResearch.WordTrace tailWord_2811961 prefixEnd_2811961 1443887574697577923355533 := by
  unfold tailWord_2811961
  simp only [CollatzResearch.WordTrace]
  refine ⟨102560643365753016549675737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68373762243835344366450491 102560643365753016549675737)
  ·
    refine ⟨76920482524314762412256803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102560643365753016549675737 76920482524314762412256803)
    ·
      refine ⟨115380723786472143618385205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76920482524314762412256803 115380723786472143618385205)
      ·
        refine ⟨10816942854981763464223613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115380723786472143618385205 10816942854981763464223613)
        ·
          refine ⟨4056353570618161299083855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10816942854981763464223613 4056353570618161299083855)
          ·
            refine ⟨6084530355927241948625783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056353570618161299083855 6084530355927241948625783)
            ·
              refine ⟨9126795533890862922938675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6084530355927241948625783 9126795533890862922938675)
              ·
                refine ⟨13690193300836294384408013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126795533890862922938675 13690193300836294384408013)
                ·
                  refine ⟨5133822487813610394153005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13690193300836294384408013 5133822487813610394153005)
                  ·
                    refine ⟨1925183432930103897807377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5133822487813610394153005 1925183432930103897807377)
                    ·
                      refine ⟨1443887574697577923355533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925183432930103897807377 1443887574697577923355533)
                      ·
                        rfl

theorem cell23_2811961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2811961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811961 prefixEnd_2811961 := by exact prefixLift 2811961
  have htrace : WordTrace (prefixWord ++ tailWord_2811961) baseStart_2811961 baseEnd_2811961 := by
    simpa [prefixWord, tailWord_2811961, baseEnd_2811961] using wordTrace_append hprefix tailTrace_2811961
  have hstable : (prefixWord ++ tailWord_2811961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811961).length < 2 ^ (prefixWord ++ tailWord_2811961).sum := by decide
  have hdescent : baseEnd_2811961 < baseStart_2811961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811991 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_2811991 : Nat := 118140960795 + 2811991 * 2 ^ 59
def prefixEnd_2811991 : Nat := 4983230072969 + 3 ^ 40 * 2811991 * 2
def baseEnd_2811991 : Nat := 1443902979117212805980395

theorem tailTrace_2811991 : CollatzResearch.WordTrace tailWord_2811991 prefixEnd_2811991 1443902979117212805980395 := by
  unfold tailWord_2811991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102561737555644331673267827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68374491703762887782178551 102561737555644331673267827)
  ·
    refine ⟨153842606333466497509901741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102561737555644331673267827 153842606333466497509901741)
    ·
      refine ⟨57690977375049936566213153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153842606333466497509901741 57690977375049936566213153)
      ·
        refine ⟨43268233031287452424659865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57690977375049936566213153 43268233031287452424659865)
        ·
          refine ⟨32451174773465589318494899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43268233031287452424659865 32451174773465589318494899)
          ·
            refine ⟨48676762160198383977742349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32451174773465589318494899 48676762160198383977742349)
            ·
              refine ⟨18253785810074393991653381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48676762160198383977742349 18253785810074393991653381)
              ·
                refine ⟨3422584839388948873435009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18253785810074393991653381 3422584839388948873435009)
                ·
                  refine ⟨2566938629541711655076257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422584839388948873435009 2566938629541711655076257)
                  ·
                    refine ⟨1925203972156283741307193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566938629541711655076257 1925203972156283741307193)
                    ·
                      refine ⟨1443902979117212805980395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925203972156283741307193 1443902979117212805980395)
                      ·
                        rfl

theorem cell23_2811991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_2811991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2811991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2811991 prefixEnd_2811991 := by exact prefixLift 2811991
  have htrace : WordTrace (prefixWord ++ tailWord_2811991) baseStart_2811991 baseEnd_2811991 := by
    simpa [prefixWord, tailWord_2811991, baseEnd_2811991] using wordTrace_append hprefix tailTrace_2811991
  have hstable : (prefixWord ++ tailWord_2811991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811991).length < 2 ^ (prefixWord ++ tailWord_2811991).sum := by decide
  have hdescent : baseEnd_2811991 < baseStart_2811991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812087 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 8]
def baseStart_2812087 : Nat := 118140960795 + 2812087 * 2 ^ 59
def prefixEnd_2812087 : Nat := 4983230072969 + 3 ^ 40 * 2812087 * 2
def baseEnd_2812087 : Nat := 160439141473338270042217

theorem tailTrace_2812087 : CollatzResearch.WordTrace tailWord_2812087 prefixEnd_2812087 160439141473338270042217 := by
  unfold tailWord_2812087
  simp only [CollatzResearch.WordTrace]
  refine ⟨102565238963296540068762515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68376825975531026712508343 102565238963296540068762515)
  ·
    refine ⟨153847858444944810103143773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102565238963296540068762515 153847858444944810103143773)
    ·
      refine ⟨57692946916854303788678915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153847858444944810103143773 57692946916854303788678915)
      ·
        refine ⟨86539420375281455683018373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57692946916854303788678915 86539420375281455683018373)
        ·
          refine ⟨16226141320365272940565945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86539420375281455683018373 16226141320365272940565945)
          ·
            refine ⟨12169605990273954705424459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16226141320365272940565945 12169605990273954705424459)
            ·
              refine ⟨18254408985410932058136689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12169605990273954705424459 18254408985410932058136689)
              ·
                refine ⟨13690806739058199043602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18254408985410932058136689 13690806739058199043602517)
                ·
                  refine ⟨160439141473338270042217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13690806739058199043602517 160439141473338270042217)
                  ·
                    rfl

theorem cell23_2812087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 8].length) (baseStart_2812087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812087 prefixEnd_2812087 := by exact prefixLift 2812087
  have htrace : WordTrace (prefixWord ++ tailWord_2812087) baseStart_2812087 baseEnd_2812087 := by
    simpa [prefixWord, tailWord_2812087, baseEnd_2812087] using wordTrace_append hprefix tailTrace_2812087
  have hstable : (prefixWord ++ tailWord_2812087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812087).length < 2 ^ (prefixWord ++ tailWord_2812087).sum := by decide
  have hdescent : baseEnd_2812087 < baseStart_2812087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812098 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2812098 : Nat := 118140960795 + 2812098 * 2 ^ 59
def prefixEnd_2812098 : Nat := 4983230072969 + 3 ^ 40 * 2812098 * 2
def baseEnd_2812098 : Nat := 1443957921547243887342403

theorem tailTrace_2812098 : CollatzResearch.WordTrace tailWord_2812098 prefixEnd_2812098 1443957921547243887342403 := by
  unfold tailWord_2812098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25641410041564172236853237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68377093444171125964941965 25641410041564172236853237)
  ·
    refine ⟨2403882191396641147204991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25641410041564172236853237 2403882191396641147204991)
    ·
      refine ⟨3605823287094961720807487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403882191396641147204991 3605823287094961720807487)
      ·
        refine ⟨5408734930642442581211231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605823287094961720807487 5408734930642442581211231)
        ·
          refine ⟨8113102395963663871816847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408734930642442581211231 8113102395963663871816847)
          ·
            refine ⟨12169653593945495807725271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113102395963663871816847 12169653593945495807725271)
            ·
              refine ⟨18254480390918243711587907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12169653593945495807725271 18254480390918243711587907)
              ·
                refine ⟨27381720586377365567381861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18254480390918243711587907 27381720586377365567381861)
                ·
                  refine ⟨5134072609945756043884099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27381720586377365567381861 5134072609945756043884099)
                  ·
                    refine ⟨7701108914918634065826149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134072609945756043884099 7701108914918634065826149)
                    ·
                      refine ⟨1443957921547243887342403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7701108914918634065826149 1443957921547243887342403)
                      ·
                        rfl

theorem cell23_2812098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2812098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812098 prefixEnd_2812098 := by exact prefixLift 2812098
  have htrace : WordTrace (prefixWord ++ tailWord_2812098) baseStart_2812098 baseEnd_2812098 := by
    simpa [prefixWord, tailWord_2812098, baseEnd_2812098] using wordTrace_append hprefix tailTrace_2812098
  have hstable : (prefixWord ++ tailWord_2812098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812098).length < 2 ^ (prefixWord ++ tailWord_2812098).sum := by decide
  have hdescent : baseEnd_2812098 < baseStart_2812098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812137 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_2812137 : Nat := 118140960795 + 2812137 * 2 ^ 59
def prefixEnd_2812137 : Nat := 4983230072969 + 3 ^ 40 * 2812137 * 2
def baseEnd_2812137 : Nat := 1443977947292769234754723

theorem tailTrace_2812137 : CollatzResearch.WordTrace tailWord_2812137 prefixEnd_2812137 1443977947292769234754723 := by
  unfold tailWord_2812137
  simp only [CollatzResearch.WordTrace]
  refine ⟨102567062613115398608082665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68378041742076932405388443 102567062613115398608082665)
  ·
    refine ⟨76925296959836548956061999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102567062613115398608082665 76925296959836548956061999)
    ·
      refine ⟨115387945439754823434092999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76925296959836548956061999 115387945439754823434092999)
      ·
        refine ⟨173081918159632235151139499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115387945439754823434092999 173081918159632235151139499)
        ·
          refine ⟨259622877239448352726709249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173081918159632235151139499 259622877239448352726709249)
          ·
            refine ⟨194717157929586264545031937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259622877239448352726709249 194717157929586264545031937)
            ·
              refine ⟨146037868447189698408773953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194717157929586264545031937 146037868447189698408773953)
              ·
                refine ⟨109528401335392273806580465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146037868447189698408773953 109528401335392273806580465)
                ·
                  refine ⟨82146301001544205354935349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109528401335392273806580465 82146301001544205354935349)
                  ·
                    refine ⟨7701215718894769252025189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82146301001544205354935349 7701215718894769252025189)
                    ·
                      refine ⟨1443977947292769234754723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7701215718894769252025189 1443977947292769234754723)
                      ·
                        rfl

theorem cell23_2812137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_2812137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812137 prefixEnd_2812137 := by exact prefixLift 2812137
  have htrace : WordTrace (prefixWord ++ tailWord_2812137) baseStart_2812137 baseEnd_2812137 := by
    simpa [prefixWord, tailWord_2812137, baseEnd_2812137] using wordTrace_append hprefix tailTrace_2812137
  have hstable : (prefixWord ++ tailWord_2812137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812137).length < 2 ^ (prefixWord ++ tailWord_2812137).sum := by decide
  have hdescent : baseEnd_2812137 < baseStart_2812137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812158 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2812158 : Nat := 118140960795 + 2812158 * 2 ^ 59
def prefixEnd_2812158 : Nat := 4983230072969 + 3 ^ 40 * 2812158 * 2
def baseEnd_2812158 : Nat := 1443988730386513652592127

theorem tailTrace_2812158 : CollatzResearch.WordTrace tailWord_2812158 prefixEnd_2812158 1443988730386513652592127 := by
  unfold tailWord_2812158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820978568254914899324641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68378552364026212796398085 12820978568254914899324641)
  ·
    refine ⟨9615733926191186174493481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12820978568254914899324641 9615733926191186174493481)
    ·
      refine ⟨7211800444643389630870111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9615733926191186174493481 7211800444643389630870111)
      ·
        refine ⟨10817700666965084446305167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7211800444643389630870111 10817700666965084446305167)
        ·
          refine ⟨16226551000447626669457751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817700666965084446305167 16226551000447626669457751)
          ·
            refine ⟨24339826500671440004186627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16226551000447626669457751 24339826500671440004186627)
            ·
              refine ⟨36509739751007160006279941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24339826500671440004186627 36509739751007160006279941)
              ·
                refine ⟨6845576203313842501177489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36509739751007160006279941 6845576203313842501177489)
                ·
                  refine ⟨5134182152485381875883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6845576203313842501177489 5134182152485381875883117)
                  ·
                    refine ⟨1925318307182018203456169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5134182152485381875883117 1925318307182018203456169)
                    ·
                      refine ⟨1443988730386513652592127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925318307182018203456169 1443988730386513652592127)
                      ·
                        rfl

theorem cell23_2812158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2812158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812158 prefixEnd_2812158 := by exact prefixLift 2812158
  have htrace : WordTrace (prefixWord ++ tailWord_2812158) baseStart_2812158 baseEnd_2812158 := by
    simpa [prefixWord, tailWord_2812158, baseEnd_2812158] using wordTrace_append hprefix tailTrace_2812158
  have hstable : (prefixWord ++ tailWord_2812158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812158).length < 2 ^ (prefixWord ++ tailWord_2812158).sum := by decide
  have hdescent : baseEnd_2812158 < baseStart_2812158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812174 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2812174 : Nat := 118140960795 + 2812174 * 2 ^ 59
def prefixEnd_2812174 : Nat := 4983230072969 + 3 ^ 40 * 2812174 * 2
def baseEnd_2812174 : Nat := 1443996946076985589992053

theorem tailTrace_2812174 : CollatzResearch.WordTrace tailWord_2812174 prefixEnd_2812174 1443996946076985589992053 := by
  unfold tailWord_2812174
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821051514247669240897447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68378941409320902618119717 12821051514247669240897447)
  ·
    refine ⟨19231577271371503861346171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12821051514247669240897447 19231577271371503861346171)
    ·
      refine ⟨28847365907057255792019257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19231577271371503861346171 28847365907057255792019257)
      ·
        refine ⟨21635524430292941844014443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28847365907057255792019257 21635524430292941844014443)
        ·
          refine ⟨32453286645439412766021665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21635524430292941844014443 32453286645439412766021665)
          ·
            refine ⟨24339964984079559574516249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32453286645439412766021665 24339964984079559574516249)
            ·
              refine ⟨18254973738059669680887187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24339964984079559574516249 18254973738059669680887187)
              ·
                refine ⟨27382460607089504521330781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18254973738059669680887187 27382460607089504521330781)
                ·
                  refine ⟨10268422727658564195499043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27382460607089504521330781 10268422727658564195499043)
                  ·
                    refine ⟨15402634091487846293248565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10268422727658564195499043 15402634091487846293248565)
                    ·
                      refine ⟨1443996946076985589992053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15402634091487846293248565 1443996946076985589992053)
                      ·
                        rfl

theorem cell23_2812174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2812174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812174 prefixEnd_2812174 := by exact prefixLift 2812174
  have htrace : WordTrace (prefixWord ++ tailWord_2812174) baseStart_2812174 baseEnd_2812174 := by
    simpa [prefixWord, tailWord_2812174, baseEnd_2812174] using wordTrace_append hprefix tailTrace_2812174
  have hstable : (prefixWord ++ tailWord_2812174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812174).length < 2 ^ (prefixWord ++ tailWord_2812174).sum := by decide
  have hdescent : baseEnd_2812174 < baseStart_2812174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812181 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2812181 : Nat := 118140960795 + 2812181 * 2 ^ 59
def prefixEnd_2812181 : Nat := 4983230072969 + 3 ^ 40 * 2812181 * 2
def baseEnd_2812181 : Nat := 481333513480522354201507

theorem tailTrace_2812181 : CollatzResearch.WordTrace tailWord_2812181 prefixEnd_2812181 481333513480522354201507 := by
  unfold tailWord_2812181
  simp only [CollatzResearch.WordTrace]
  refine ⟨102568667424955994122684397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68379111616637329415122931 102568667424955994122684397)
  ·
    refine ⟨38463250284358497796006649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102568667424955994122684397 38463250284358497796006649)
    ·
      refine ⟨28847437713268873347004987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38463250284358497796006649 28847437713268873347004987)
      ·
        refine ⟨43271156569903310020507481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28847437713268873347004987 43271156569903310020507481)
        ·
          refine ⟨32453367427427482515380611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43271156569903310020507481 32453367427427482515380611)
          ·
            refine ⟨48680051141141223773070917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32453367427427482515380611 48680051141141223773070917)
            ·
              refine ⟨9127509588963979457450797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48680051141141223773070917 9127509588963979457450797)
              ·
                refine ⟨3422816095861492296544049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9127509588963979457450797 3422816095861492296544049)
                ·
                  refine ⟨2567112071896119222408037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422816095861492296544049 2567112071896119222408037)
                  ·
                    refine ⟨481333513480522354201507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567112071896119222408037 481333513480522354201507)
                    ·
                      rfl

theorem cell23_2812181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2812181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812181 prefixEnd_2812181 := by exact prefixLift 2812181
  have htrace : WordTrace (prefixWord ++ tailWord_2812181) baseStart_2812181 baseEnd_2812181 := by
    simpa [prefixWord, tailWord_2812181, baseEnd_2812181] using wordTrace_append hprefix tailTrace_2812181
  have hstable : (prefixWord ++ tailWord_2812181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812181).length < 2 ^ (prefixWord ++ tailWord_2812181).sum := by decide
  have hdescent : baseEnd_2812181 < baseStart_2812181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812191 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_2812191 : Nat := 118140960795 + 2812191 * 2 ^ 59
def prefixEnd_2812191 : Nat := 4983230072969 + 3 ^ 40 * 2812191 * 2
def baseEnd_2812191 : Nat := 1444005675248112023479475

theorem tailTrace_2812191 : CollatzResearch.WordTrace tailWord_2812191 prefixEnd_2812191 1444005675248112023479475 := by
  unfold tailWord_2812191
  simp only [CollatzResearch.WordTrace]
  refine ⟨102569032154919765830548427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68379354769946510553698951 102569032154919765830548427)
  ·
    refine ⟨153853548232379648745822641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102569032154919765830548427 153853548232379648745822641)
    ·
      refine ⟨115390161174284736559366981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153853548232379648745822641 115390161174284736559366981)
      ·
        refine ⟨21635655220178388104881309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115390161174284736559366981 21635655220178388104881309)
        ·
          refine ⟨8113370707566895539330491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21635655220178388104881309 8113370707566895539330491)
          ·
            refine ⟨12170056061350343308995737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113370707566895539330491 12170056061350343308995737)
            ·
              refine ⟨9127542046012757481746803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12170056061350343308995737 9127542046012757481746803)
              ·
                refine ⟨13691313069019136222620205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9127542046012757481746803 13691313069019136222620205)
                ·
                  refine ⟨5134242400882176083482577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13691313069019136222620205 5134242400882176083482577)
                  ·
                    refine ⟨3850681800661632062611933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5134242400882176083482577 3850681800661632062611933)
                    ·
                      refine ⟨1444005675248112023479475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3850681800661632062611933 1444005675248112023479475)
                      ·
                        rfl

theorem cell23_2812191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_2812191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812191 prefixEnd_2812191 := by exact prefixLift 2812191
  have htrace : WordTrace (prefixWord ++ tailWord_2812191) baseStart_2812191 baseEnd_2812191 := by
    simpa [prefixWord, tailWord_2812191, baseEnd_2812191] using wordTrace_append hprefix tailTrace_2812191
  have hstable : (prefixWord ++ tailWord_2812191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812191).length < 2 ^ (prefixWord ++ tailWord_2812191).sum := by decide
  have hdescent : baseEnd_2812191 < baseStart_2812191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812202 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_2812202 : Nat := 118140960795 + 2812202 * 2 ^ 59
def prefixEnd_2812202 : Nat := 4983230072969 + 3 ^ 40 * 2812202 * 2
def baseEnd_2812202 : Nat := 481337107845103826813975

theorem tailTrace_2812202 : CollatzResearch.WordTrace tailWord_2812202 prefixEnd_2812202 481337107845103826813975 := by
  unfold tailWord_2812202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25642358339469978677299715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68379622238586609806132573 25642358339469978677299715)
  ·
    refine ⟨38463537509204968015949573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25642358339469978677299715 38463537509204968015949573)
    ·
      refine ⟨7211913282975931502990545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38463537509204968015949573 7211913282975931502990545)
      ·
        refine ⟨5408934962231948627242909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7211913282975931502990545 5408934962231948627242909)
        ·
          refine ⟨2028350610836980735216091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5408934962231948627242909 2028350610836980735216091)
          ·
            refine ⟨3042525916255471102824137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028350610836980735216091 3042525916255471102824137)
            ·
              refine ⟨2281894437191603327118103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042525916255471102824137 2281894437191603327118103)
              ·
                refine ⟨3422841655787404990677155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281894437191603327118103 3422841655787404990677155)
                ·
                  refine ⟨5134262483681107486015733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422841655787404990677155 5134262483681107486015733)
                  ·
                    refine ⟨481337107845103826813975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5134262483681107486015733 481337107845103826813975)
                    ·
                      rfl

theorem cell23_2812202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_2812202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812202 prefixEnd_2812202 := by exact prefixLift 2812202
  have htrace : WordTrace (prefixWord ++ tailWord_2812202) baseStart_2812202 baseEnd_2812202 := by
    simpa [prefixWord, tailWord_2812202, baseEnd_2812202] using wordTrace_append hprefix tailTrace_2812202
  have hstable : (prefixWord ++ tailWord_2812202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812202).length < 2 ^ (prefixWord ++ tailWord_2812202).sum := by decide
  have hdescent : baseEnd_2812202 < baseStart_2812202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812205 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2812205 : Nat := 118140960795 + 2812205 * 2 ^ 59
def prefixEnd_2812205 : Nat := 4983230072969 + 3 ^ 40 * 2812205 * 2
def baseEnd_2812205 : Nat := 1444012863977274968704411

theorem tailTrace_2812205 : CollatzResearch.WordTrace tailWord_2812205 prefixEnd_2812205 1444012863977274968704411 := by
  unfold tailWord_2812205
  simp only [CollatzResearch.WordTrace]
  refine ⟨102569542776869046221558069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68379695184579364147705379 102569542776869046221558069)
  ·
    refine ⟨9615894635331473083271069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102569542776869046221558069 9615894635331473083271069)
    ·
      refine ⟨3605960488249302406226651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9615894635331473083271069 3605960488249302406226651)
      ·
        refine ⟨5408940732373953609339977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605960488249302406226651 5408940732373953609339977)
        ·
          refine ⟨4056705549280465207004983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5408940732373953609339977 4056705549280465207004983)
          ·
            refine ⟨6085058323920697810507475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056705549280465207004983 6085058323920697810507475)
            ·
              refine ⟨9127587485881046715761213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085058323920697810507475 9127587485881046715761213)
              ·
                refine ⟨3422845307205392518410455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9127587485881046715761213 3422845307205392518410455)
                ·
                  refine ⟨5134267960808088777615683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422845307205392518410455 5134267960808088777615683)
                  ·
                    refine ⟨7701401941212133166423525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134267960808088777615683 7701401941212133166423525)
                    ·
                      refine ⟨1444012863977274968704411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7701401941212133166423525 1444012863977274968704411)
                      ·
                        rfl

theorem cell23_2812205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2812205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812205 prefixEnd_2812205 := by exact prefixLift 2812205
  have htrace : WordTrace (prefixWord ++ tailWord_2812205) baseStart_2812205 baseEnd_2812205 := by
    simpa [prefixWord, tailWord_2812205, baseEnd_2812205] using wordTrace_append hprefix tailTrace_2812205
  have hstable : (prefixWord ++ tailWord_2812205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812205).length < 2 ^ (prefixWord ++ tailWord_2812205).sum := by decide
  have hdescent : baseEnd_2812205 < baseStart_2812205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812222 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_2812222 : Nat := 118140960795 + 2812222 * 2 ^ 59
def prefixEnd_2812222 : Nat := 4983230072969 + 3 ^ 40 * 2812222 * 2
def baseEnd_2812222 : Nat := 1444021593148401402191833

theorem tailTrace_2812222 : CollatzResearch.WordTrace tailWord_2812222 prefixEnd_2812222 1444021593148401402191833 := by
  unfold tailWord_2812222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821270352225932265615865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68380108545204972083284613 12821270352225932265615865)
  ·
    refine ⟨9615952764169449199211899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12821270352225932265615865 9615952764169449199211899)
    ·
      refine ⟨14423929146254173798817849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9615952764169449199211899 14423929146254173798817849)
      ·
        refine ⟨10817946859690630349113387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14423929146254173798817849 10817946859690630349113387)
        ·
          refine ⟨16226920289535945523670081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817946859690630349113387 16226920289535945523670081)
          ·
            refine ⟨12170190217151959142752561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16226920289535945523670081 12170190217151959142752561)
            ·
              refine ⟨9127642662863969357064421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12170190217151959142752561 9127642662863969357064421)
              ·
                refine ⟨1711432999286994254449579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9127642662863969357064421 1711432999286994254449579)
                ·
                  refine ⟨2567149498930491381674369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711432999286994254449579 2567149498930491381674369)
                  ·
                    refine ⟨1925362124197868536255777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567149498930491381674369 1925362124197868536255777)
                    ·
                      refine ⟨1444021593148401402191833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925362124197868536255777 1444021593148401402191833)
                      ·
                        rfl

theorem cell23_2812222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_2812222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812222 prefixEnd_2812222 := by exact prefixLift 2812222
  have htrace : WordTrace (prefixWord ++ tailWord_2812222) baseStart_2812222 baseEnd_2812222 := by
    simpa [prefixWord, tailWord_2812222, baseEnd_2812222] using wordTrace_append hprefix tailTrace_2812222
  have hstable : (prefixWord ++ tailWord_2812222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812222).length < 2 ^ (prefixWord ++ tailWord_2812222).sum := by decide
  have hdescent : baseEnd_2812222 < baseStart_2812222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812284 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 7]
def baseStart_2812284 : Nat := 118140960795 + 2812284 * 2 ^ 59
def prefixEnd_2812284 : Nat := 4983230072969 + 3 ^ 40 * 2812284 * 2
def baseEnd_2812284 : Nat := 160450380994331128846283

theorem tailTrace_2812284 : CollatzResearch.WordTrace tailWord_2812284 prefixEnd_2812284 160450380994331128846283 := by
  unfold tailWord_2812284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51286212071791421356841953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68381616095721895142455937 51286212071791421356841953)
  ·
    refine ⟨38464659053843566017631465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51286212071791421356841953 38464659053843566017631465)
    ·
      refine ⟨28848494290382674513223599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38464659053843566017631465 28848494290382674513223599)
      ·
        refine ⟨43272741435574011769835399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28848494290382674513223599 43272741435574011769835399)
        ·
          refine ⟨64909112153361017654753099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43272741435574011769835399 64909112153361017654753099)
          ·
            refine ⟨97363668230041526482129649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64909112153361017654753099 97363668230041526482129649)
            ·
              refine ⟨73022751172531144861597237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97363668230041526482129649 73022751172531144861597237)
              ·
                refine ⟨6845882922424794830774741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73022751172531144861597237 6845882922424794830774741)
                ·
                  refine ⟨160450380994331128846283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6845882922424794830774741 160450380994331128846283)
                  ·
                    rfl

theorem cell23_2812284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_2812284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812284 prefixEnd_2812284 := by exact prefixLift 2812284
  have htrace : WordTrace (prefixWord ++ tailWord_2812284) baseStart_2812284 baseEnd_2812284 := by
    simpa [prefixWord, tailWord_2812284, baseEnd_2812284] using wordTrace_append hprefix tailTrace_2812284
  have hstable : (prefixWord ++ tailWord_2812284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812284).length < 2 ^ (prefixWord ++ tailWord_2812284).sum := by decide
  have hdescent : baseEnd_2812284 < baseStart_2812284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812295 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_2812295 : Nat := 118140960795 + 2812295 * 2 ^ 59
def prefixEnd_2812295 : Nat := 4983230072969 + 3 ^ 40 * 2812295 * 2
def baseEnd_2812295 : Nat := 1444059077236179616578997

theorem tailTrace_2812295 : CollatzResearch.WordTrace tailWord_2812295 prefixEnd_2812295 1444059077236179616578997 := by
  unfold tailWord_2812295
  simp only [CollatzResearch.WordTrace]
  refine ⟨102572825346542991592334339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68381883564361994394889559 102572825346542991592334339)
  ·
    refine ⟨153859238019814487388501509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102572825346542991592334339 153859238019814487388501509)
    ·
      refine ⟨28848607128715216385344033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153859238019814487388501509 28848607128715216385344033)
      ·
        refine ⟨21636455346536412289008025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28848607128715216385344033 21636455346536412289008025)
        ·
          refine ⟨16227341509902309216756019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21636455346536412289008025 16227341509902309216756019)
          ·
            refine ⟨24341012264853463825134029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16227341509902309216756019 24341012264853463825134029)
            ·
              refine ⟨9127879599320048934425261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24341012264853463825134029 9127879599320048934425261)
              ·
                refine ⟨3422954849745018350409473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9127879599320048934425261 3422954849745018350409473)
                ·
                  refine ⟨2567216137308763762807105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422954849745018350409473 2567216137308763762807105)
                  ·
                    refine ⟨1925412102981572822105329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567216137308763762807105 1925412102981572822105329)
                    ·
                      refine ⟨1444059077236179616578997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925412102981572822105329 1444059077236179616578997)
                      ·
                        rfl

theorem cell23_2812295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_2812295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812295 prefixEnd_2812295 := by exact prefixLift 2812295
  have htrace : WordTrace (prefixWord ++ tailWord_2812295) baseStart_2812295 baseEnd_2812295 := by
    simpa [prefixWord, tailWord_2812295, baseEnd_2812295] using wordTrace_append hprefix tailTrace_2812295
  have hstable : (prefixWord ++ tailWord_2812295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812295).length < 2 ^ (prefixWord ++ tailWord_2812295).sum := by decide
  have hdescent : baseEnd_2812295 < baseStart_2812295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812344 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_2812344 : Nat := 118140960795 + 2812344 * 2 ^ 59
def prefixEnd_2812344 : Nat := 4983230072969 + 3 ^ 40 * 2812344 * 2
def baseEnd_2812344 : Nat := 481361412596083308288757

theorem tailTrace_2812344 : CollatzResearch.WordTrace tailWord_2812344 prefixEnd_2812344 481361412596083308288757 := by
  unfold tailWord_2812344
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287306261682736480434043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68383075015576981973912057 51287306261682736480434043)
  ·
    refine ⟨76930959392524104720651065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51287306261682736480434043 76930959392524104720651065)
    ·
      refine ⟨57698219544393078540488299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76930959392524104720651065 57698219544393078540488299)
      ·
        refine ⟨86547329316589617810732449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57698219544393078540488299 86547329316589617810732449)
        ·
          refine ⟨64910496987442213358049337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86547329316589617810732449 64910496987442213358049337)
          ·
            refine ⟨48682872740581660018537003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64910496987442213358049337 48682872740581660018537003)
            ·
              refine ⟨73024309110872490027805505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48682872740581660018537003 73024309110872490027805505)
              ·
                refine ⟨54768231833154367520854129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73024309110872490027805505 54768231833154367520854129)
                ·
                  refine ⟨41076173874865775640640597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54768231833154367520854129 41076173874865775640640597)
                  ·
                    refine ⟨481361412596083308288757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41076173874865775640640597 481361412596083308288757)
                    ·
                      rfl

theorem cell23_2812344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_2812344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812344 prefixEnd_2812344 := by exact prefixLift 2812344
  have htrace : WordTrace (prefixWord ++ tailWord_2812344) baseStart_2812344 baseEnd_2812344 := by
    simpa [prefixWord, tailWord_2812344, baseEnd_2812344] using wordTrace_append hprefix tailTrace_2812344
  have hstable : (prefixWord ++ tailWord_2812344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812344).length < 2 ^ (prefixWord ++ tailWord_2812344).sum := by decide
  have hdescent : baseEnd_2812344 < baseStart_2812344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812361 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_2812361 : Nat := 118140960795 + 2812361 * 2 ^ 59
def prefixEnd_2812361 : Nat := 4983230072969 + 3 ^ 40 * 2812361 * 2
def baseEnd_2812361 : Nat := 481364322319792119451231

theorem tailTrace_2812361 : CollatzResearch.WordTrace tailWord_2812361 prefixEnd_2812361 481364322319792119451231 := by
  unfold tailWord_2812361
  simp only [CollatzResearch.WordTrace]
  refine ⟨102575232564303884864236937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68383488376202589909491291 102575232564303884864236937)
  ·
    refine ⟨76931424423227913648177703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102575232564303884864236937 76931424423227913648177703)
    ·
      refine ⟨115397136634841870472266555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76931424423227913648177703 115397136634841870472266555)
      ·
        refine ⟨173095704952262805708399833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115397136634841870472266555 173095704952262805708399833)
        ·
          refine ⟨129821778714197104281299875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173095704952262805708399833 129821778714197104281299875)
          ·
            refine ⟨194732668071295656421949813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129821778714197104281299875 194732668071295656421949813)
            ·
              refine ⟨18256187631683967789557795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194732668071295656421949813 18256187631683967789557795)
              ·
                refine ⟨27384281447525951684336693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18256187631683967789557795 27384281447525951684336693)
                ·
                  refine ⟨2567276385705557970406565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27384281447525951684336693 2567276385705557970406565)
                  ·
                    refine ⟨481364322319792119451231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567276385705557970406565 481364322319792119451231)
                    ·
                      rfl

theorem cell23_2812361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_2812361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812361 prefixEnd_2812361 := by exact prefixLift 2812361
  have htrace : WordTrace (prefixWord ++ tailWord_2812361) baseStart_2812361 baseEnd_2812361 := by
    simpa [prefixWord, tailWord_2812361, baseEnd_2812361] using wordTrace_append hprefix tailTrace_2812361
  have hstable : (prefixWord ++ tailWord_2812361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812361).length < 2 ^ (prefixWord ++ tailWord_2812361).sum := by decide
  have hdescent : baseEnd_2812361 < baseStart_2812361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812381 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2812381 : Nat := 118140960795 + 2812381 * 2 ^ 59
def prefixEnd_2812381 : Nat := 4983230072969 + 3 ^ 40 * 2812381 * 2
def baseEnd_2812381 : Nat := 1444103236572466280103601

theorem tailTrace_2812381 : CollatzResearch.WordTrace tailWord_2812381 prefixEnd_2812381 1444103236572466280103601 := by
  unfold tailWord_2812381
  simp only [CollatzResearch.WordTrace]
  refine ⟨102575962024231428279964997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68383974682820952186643331 102575962024231428279964997)
  ·
    refine ⟨19232992879543392802493437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102575962024231428279964997 19232992879543392802493437)
    ·
      refine ⟨7212372329828772300935039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19232992879543392802493437 7212372329828772300935039)
      ·
        refine ⟨10818558494743158451402559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212372329828772300935039 10818558494743158451402559)
        ·
          refine ⟨16227837742114737677103839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818558494743158451402559 16227837742114737677103839)
          ·
            refine ⟨24341756613172106515655759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16227837742114737677103839 24341756613172106515655759)
            ·
              refine ⟨36512634919758159773483639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24341756613172106515655759 36512634919758159773483639)
              ·
                refine ⟨54768952379637239660225459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36512634919758159773483639 54768952379637239660225459)
                ·
                  refine ⟨82153428569455859490338189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54768952379637239660225459 82153428569455859490338189)
                  ·
                    refine ⟨30807535713545947308876821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82153428569455859490338189 30807535713545947308876821)
                    ·
                      refine ⟨1444103236572466280103601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30807535713545947308876821 1444103236572466280103601)
                      ·
                        rfl

theorem cell23_2812381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2812381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812381 prefixEnd_2812381 := by exact prefixLift 2812381
  have htrace : WordTrace (prefixWord ++ tailWord_2812381) baseStart_2812381 baseEnd_2812381 := by
    simpa [prefixWord, tailWord_2812381, baseEnd_2812381] using wordTrace_append hprefix tailTrace_2812381
  have hstable : (prefixWord ++ tailWord_2812381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812381).length < 2 ^ (prefixWord ++ tailWord_2812381).sum := by decide
  have hdescent : baseEnd_2812381 < baseStart_2812381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812391 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 8]
def baseStart_2812391 : Nat := 118140960795 + 2812391 * 2 ^ 59
def prefixEnd_2812391 : Nat := 4983230072969 + 3 ^ 40 * 2812391 * 2
def baseEnd_2812391 : Nat := 160456485708779026775395

theorem tailTrace_2812391 : CollatzResearch.WordTrace tailWord_2812391 prefixEnd_2812391 160456485708779026775395 := by
  unfold tailWord_2812391
  simp only [CollatzResearch.WordTrace]
  refine ⟨102576326754195199987829027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68384217836130133325219351 102576326754195199987829027)
  ·
    refine ⟨153864490131292799981743541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102576326754195199987829027 153864490131292799981743541)
    ·
      refine ⟨14424795949808699998288457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153864490131292799981743541 14424795949808699998288457)
      ·
        refine ⟨10818596962356524998716343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14424795949808699998288457 10818596962356524998716343)
        ·
          refine ⟨16227895443534787498074515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818596962356524998716343 16227895443534787498074515)
          ·
            refine ⟨24341843165302181247111773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16227895443534787498074515 24341843165302181247111773)
            ·
              refine ⟨9128191186988317967666915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24341843165302181247111773 9128191186988317967666915)
              ·
                refine ⟨13692286780482476951500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9128191186988317967666915 13692286780482476951500373)
                ·
                  refine ⟨160456485708779026775395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13692286780482476951500373 160456485708779026775395)
                  ·
                    rfl

theorem cell23_2812391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 8].length) (baseStart_2812391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812391 prefixEnd_2812391 := by exact prefixLift 2812391
  have htrace : WordTrace (prefixWord ++ tailWord_2812391) baseStart_2812391 baseEnd_2812391 := by
    simpa [prefixWord, tailWord_2812391, baseEnd_2812391] using wordTrace_append hprefix tailTrace_2812391
  have hstable : (prefixWord ++ tailWord_2812391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812391).length < 2 ^ (prefixWord ++ tailWord_2812391).sum := by decide
  have hdescent : baseEnd_2812391 < baseStart_2812391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812408 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 6]
def baseStart_2812408 : Nat := 118140960795 + 2812408 * 2 ^ 59
def prefixEnd_2812408 : Nat := 4983230072969 + 3 ^ 40 * 2812408 * 2
def baseEnd_2812408 : Nat := 160457455616681963829553

theorem tailTrace_2812408 : CollatzResearch.WordTrace tailWord_2812408 prefixEnd_2812408 160457455616681963829553 := by
  unfold tailWord_2812408
  simp only [CollatzResearch.WordTrace]
  refine ⟨51288473397566805945598939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68384631196755741260798585 51288473397566805945598939)
  ·
    refine ⟨76932710096350208918398409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51288473397566805945598939 76932710096350208918398409)
    ·
      refine ⟨57699532572262656688798807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76932710096350208918398409 57699532572262656688798807)
      ·
        refine ⟨86549298858393985033198211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57699532572262656688798807 86549298858393985033198211)
        ·
          refine ⟨129823948287590977549797317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86549298858393985033198211 129823948287590977549797317)
          ·
            refine ⟨24341990303923308290586997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129823948287590977549797317 24341990303923308290586997)
            ·
              refine ⟨2282061590992810152242531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24341990303923308290586997 2282061590992810152242531)
              ·
                refine ⟨3423092386489215228363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282061590992810152242531 3423092386489215228363797)
                ·
                  refine ⟨160457455616681963829553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3423092386489215228363797 160457455616681963829553)
                  ·
                    rfl

theorem cell23_2812408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 6].length) (baseStart_2812408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812408 prefixEnd_2812408 := by exact prefixLift 2812408
  have htrace : WordTrace (prefixWord ++ tailWord_2812408) baseStart_2812408 baseEnd_2812408 := by
    simpa [prefixWord, tailWord_2812408, baseEnd_2812408] using wordTrace_append hprefix tailTrace_2812408
  have hstable : (prefixWord ++ tailWord_2812408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812408).length < 2 ^ (prefixWord ++ tailWord_2812408).sum := by decide
  have hdescent : baseEnd_2812408 < baseStart_2812408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812421 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_2812421 : Nat := 118140960795 + 2812421 * 2 ^ 59
def prefixEnd_2812421 : Nat := 4983230072969 + 3 ^ 40 * 2812421 * 2
def baseEnd_2812421 : Nat := 481374591932882041201139

theorem tailTrace_2812421 : CollatzResearch.WordTrace tailWord_2812421 prefixEnd_2812421 481374591932882041201139 := by
  unfold tailWord_2812421
  simp only [CollatzResearch.WordTrace]
  refine ⟨102577420944086515111421117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68384947296057676740947411 102577420944086515111421117)
  ·
    refine ⟨38466532854032443166782919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102577420944086515111421117 38466532854032443166782919)
    ·
      refine ⟨57699799281048664750174379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38466532854032443166782919 57699799281048664750174379)
      ·
        refine ⟨86549698921572997125261569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57699799281048664750174379 86549698921572997125261569)
        ·
          refine ⟨64912274191179747843946177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86549698921572997125261569 64912274191179747843946177)
          ·
            refine ⟨48684205643384810882959633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64912274191179747843946177 48684205643384810882959633)
            ·
              refine ⟨36513154232538608162219725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48684205643384810882959633 36513154232538608162219725)
              ·
                refine ⟨13692432837201978060832397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36513154232538608162219725 13692432837201978060832397)
                ·
                  refine ⟨5134662313950741772812149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13692432837201978060832397 5134662313950741772812149)
                  ·
                    refine ⟨481374591932882041201139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5134662313950741772812149 481374591932882041201139)
                    ·
                      rfl

theorem cell23_2812421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_2812421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812421 prefixEnd_2812421 := by exact prefixLift 2812421
  have htrace : WordTrace (prefixWord ++ tailWord_2812421) baseStart_2812421 baseEnd_2812421 := by
    simpa [prefixWord, tailWord_2812421, baseEnd_2812421] using wordTrace_append hprefix tailTrace_2812421
  have hstable : (prefixWord ++ tailWord_2812421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812421).length < 2 ^ (prefixWord ++ tailWord_2812421).sum := by decide
  have hdescent : baseEnd_2812421 < baseStart_2812421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812445 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2812445 : Nat := 118140960795 + 2812445 * 2 ^ 59
def prefixEnd_2812445 : Nat := 4983230072969 + 3 ^ 40 * 2812445 * 2
def baseEnd_2812445 : Nat := 1444136099334354029703307

theorem tailTrace_2812445 : CollatzResearch.WordTrace tailWord_2812445 prefixEnd_2812445 1444136099334354029703307 := by
  unfold tailWord_2812445
  simp only [CollatzResearch.WordTrace]
  refine ⟨102578296295999567210294789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68385530863999711473529859 102578296295999567210294789)
  ·
    refine ⟨19233430555499918851930273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102578296295999567210294789 19233430555499918851930273)
    ·
      refine ⟨14425072916624939138947705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19233430555499918851930273 14425072916624939138947705)
      ·
        refine ⟨10818804687468704354210779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14425072916624939138947705 10818804687468704354210779)
        ·
          refine ⟨16228207031203056531316169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818804687468704354210779 16228207031203056531316169)
          ·
            refine ⟨12171155273402292398487127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16228207031203056531316169 12171155273402292398487127)
            ·
              refine ⟨18256732910103438597730691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12171155273402292398487127 18256732910103438597730691)
              ·
                refine ⟨27385099365155157896596037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18256732910103438597730691 27385099365155157896596037)
                ·
                  refine ⟨5134706130966592105611757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27385099365155157896596037 5134706130966592105611757)
                  ·
                    refine ⟨1925514799112472039604409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5134706130966592105611757 1925514799112472039604409)
                    ·
                      refine ⟨1444136099334354029703307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925514799112472039604409 1444136099334354029703307)
                      ·
                        rfl

theorem cell23_2812445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2812445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812445 prefixEnd_2812445 := by exact prefixLift 2812445
  have htrace : WordTrace (prefixWord ++ tailWord_2812445) baseStart_2812445 baseEnd_2812445 := by
    simpa [prefixWord, tailWord_2812445, baseEnd_2812445] using wordTrace_append hprefix tailTrace_2812445
  have hstable : (prefixWord ++ tailWord_2812445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812445).length < 2 ^ (prefixWord ++ tailWord_2812445).sum := by decide
  have hdescent : baseEnd_2812445 < baseStart_2812445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812471 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2812471 : Nat := 118140960795 + 2812471 * 2 ^ 59
def prefixEnd_2812471 : Nat := 4983230072969 + 3 ^ 40 * 2812471 * 2
def baseEnd_2812471 : Nat := 1444149449831370927978187

theorem tailTrace_2812471 : CollatzResearch.WordTrace tailWord_2812471 prefixEnd_2812471 1444149449831370927978187 := by
  unfold tailWord_2812471
  simp only [CollatzResearch.WordTrace]
  refine ⟨102579244593905373650741267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68386163062603582433827511 102579244593905373650741267)
  ·
    refine ⟨153868866890858060476111901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102579244593905373650741267 153868866890858060476111901)
    ·
      refine ⟨57700825084071772678541963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153868866890858060476111901 57700825084071772678541963)
      ·
        refine ⟨86551237626107659017812945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57700825084071772678541963 86551237626107659017812945)
        ·
          refine ⟨64913428219580744263359709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86551237626107659017812945 64913428219580744263359709)
          ·
            refine ⟨24342535582342779098759891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64913428219580744263359709 24342535582342779098759891)
            ·
              refine ⟨36513803373514168648139837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24342535582342779098759891 36513803373514168648139837)
              ·
                refine ⟨13692676265067813243052439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36513803373514168648139837 13692676265067813243052439)
                ·
                  refine ⟨20539014397601719864578659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13692676265067813243052439 20539014397601719864578659)
                  ·
                    refine ⟨30808521596402579796867989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20539014397601719864578659 30808521596402579796867989)
                    ·
                      refine ⟨1444149449831370927978187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30808521596402579796867989 1444149449831370927978187)
                      ·
                        rfl

theorem cell23_2812471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2812471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812471 prefixEnd_2812471 := by exact prefixLift 2812471
  have htrace : WordTrace (prefixWord ++ tailWord_2812471) baseStart_2812471 baseEnd_2812471 := by
    simpa [prefixWord, tailWord_2812471, baseEnd_2812471] using wordTrace_append hprefix tailTrace_2812471
  have hstable : (prefixWord ++ tailWord_2812471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812471).length < 2 ^ (prefixWord ++ tailWord_2812471).sum := by decide
  have hdescent : baseEnd_2812471 < baseStart_2812471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812521 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_2812521 : Nat := 118140960795 + 2812521 * 2 ^ 59
def prefixEnd_2812521 : Nat := 4983230072969 + 3 ^ 40 * 2812521 * 2
def baseEnd_2812521 : Nat := 1444175123864095732352957

theorem tailTrace_2812521 : CollatzResearch.WordTrace tailWord_2812521 prefixEnd_2812521 1444175123864095732352957 := by
  unfold tailWord_2812521
  simp only [CollatzResearch.WordTrace]
  refine ⟨102581068243724232190061417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68387378829149488126707611 102581068243724232190061417)
  ·
    refine ⟨76935801182793174142546063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102581068243724232190061417 76935801182793174142546063)
    ·
      refine ⟨115403701774189761213819095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76935801182793174142546063 115403701774189761213819095)
      ·
        refine ⟨173105552661284641820728643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115403701774189761213819095 173105552661284641820728643)
        ·
          refine ⟨259658328991926962731092965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173105552661284641820728643 259658328991926962731092965)
          ·
            refine ⟨48685936685986305512079931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259658328991926962731092965 48685936685986305512079931)
            ·
              refine ⟨73028905028979458268119897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48685936685986305512079931 73028905028979458268119897)
              ·
                refine ⟨54771678771734593701089923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73028905028979458268119897 54771678771734593701089923)
                ·
                  refine ⟨82157518157601890551634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54771678771734593701089923 82157518157601890551634885)
                  ·
                    refine ⟨15404534654550354478431541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82157518157601890551634885 15404534654550354478431541)
                    ·
                      refine ⟨1444175123864095732352957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15404534654550354478431541 1444175123864095732352957)
                      ·
                        rfl

theorem cell23_2812521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_2812521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812521 prefixEnd_2812521 := by exact prefixLift 2812521
  have htrace : WordTrace (prefixWord ++ tailWord_2812521) baseStart_2812521 baseEnd_2812521 := by
    simpa [prefixWord, tailWord_2812521, baseEnd_2812521] using wordTrace_append hprefix tailTrace_2812521
  have hstable : (prefixWord ++ tailWord_2812521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812521).length < 2 ^ (prefixWord ++ tailWord_2812521).sum := by decide
  have hdescent : baseEnd_2812521 < baseStart_2812521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812525 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2812525 : Nat := 118140960795 + 2812525 * 2 ^ 59
def prefixEnd_2812525 : Nat := 4983230072969 + 3 ^ 40 * 2812525 * 2
def baseEnd_2812525 : Nat := 1444177177786713716702939

theorem tailTrace_2812525 : CollatzResearch.WordTrace tailWord_2812525 prefixEnd_2812525 1444177177786713716702939 := by
  unfold tailWord_2812525
  simp only [CollatzResearch.WordTrace]
  refine ⟨102581214135709740873207029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68387476090473160582138019 102581214135709740873207029)
  ·
    refine ⟨9616988825222788206863159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102581214135709740873207029 9616988825222788206863159)
    ·
      refine ⟨14425483237834182310294739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9616988825222788206863159 14425483237834182310294739)
      ·
        refine ⟨21638224856751273465442109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14425483237834182310294739 21638224856751273465442109)
        ·
          refine ⟨8114334321281727549540791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21638224856751273465442109 8114334321281727549540791)
          ·
            refine ⟨12171501481922591324311187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8114334321281727549540791 12171501481922591324311187)
            ·
              refine ⟨18257252222883886986466781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12171501481922591324311187 18257252222883886986466781)
              ·
                refine ⟨6846469583581457619925043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18257252222883886986466781 6846469583581457619925043)
                ·
                  refine ⟨10269704375372186429887565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6846469583581457619925043 10269704375372186429887565)
                  ·
                    refine ⟨3851139140764569911207837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10269704375372186429887565 3851139140764569911207837)
                    ·
                      refine ⟨1444177177786713716702939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3851139140764569911207837 1444177177786713716702939)
                      ·
                        rfl

theorem cell23_2812525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2812525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812525 prefixEnd_2812525 := by exact prefixLift 2812525
  have htrace : WordTrace (prefixWord ++ tailWord_2812525) baseStart_2812525 baseEnd_2812525 := by
    simpa [prefixWord, tailWord_2812525, baseEnd_2812525] using wordTrace_append hprefix tailTrace_2812525
  have hstable : (prefixWord ++ tailWord_2812525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812525).length < 2 ^ (prefixWord ++ tailWord_2812525).sum := by decide
  have hdescent : baseEnd_2812525 < baseStart_2812525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812535 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_2812535 : Nat := 118140960795 + 2812535 * 2 ^ 59
def prefixEnd_2812535 : Nat := 4983230072969 + 3 ^ 40 * 2812535 * 2
def baseEnd_2812535 : Nat := 1444182312593258677577893

theorem tailTrace_2812535 : CollatzResearch.WordTrace tailWord_2812535 prefixEnd_2812535 1444182312593258677577893 := by
  unfold tailWord_2812535
  simp only [CollatzResearch.WordTrace]
  refine ⟨102581578865673512581071059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68387719243782341720714039 102581578865673512581071059)
  ·
    refine ⟨153872368298510268871606589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102581578865673512581071059 153872368298510268871606589)
    ·
      refine ⟨57702138111941350826852471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153872368298510268871606589 57702138111941350826852471)
      ·
        refine ⟨86553207167912026240278707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57702138111941350826852471 86553207167912026240278707)
        ·
          refine ⟨129829810751868039360418061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86553207167912026240278707 129829810751868039360418061)
          ·
            refine ⟨48686179031950514760156773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129829810751868039360418061 48686179031950514760156773)
            ·
              refine ⟨9128658568490721517529395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48686179031950514760156773 9128658568490721517529395)
              ·
                refine ⟨13692987852736082276294093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9128658568490721517529395 13692987852736082276294093)
                ·
                  refine ⟨5134870444776030853610285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13692987852736082276294093 5134870444776030853610285)
                  ·
                    refine ⟨1925576416791011570103857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5134870444776030853610285 1925576416791011570103857)
                    ·
                      refine ⟨1444182312593258677577893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925576416791011570103857 1444182312593258677577893)
                      ·
                        rfl

theorem cell23_2812535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_2812535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812535 prefixEnd_2812535 := by exact prefixLift 2812535
  have htrace : WordTrace (prefixWord ++ tailWord_2812535) baseStart_2812535 baseEnd_2812535 := by
    simpa [prefixWord, tailWord_2812535, baseEnd_2812535] using wordTrace_append hprefix tailTrace_2812535
  have hstable : (prefixWord ++ tailWord_2812535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812535).length < 2 ^ (prefixWord ++ tailWord_2812535).sum := by decide
  have hdescent : baseEnd_2812535 < baseStart_2812535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812558 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2812558 : Nat := 118140960795 + 2812558 * 2 ^ 59
def prefixEnd_2812558 : Nat := 4983230072969 + 3 ^ 40 * 2812558 * 2
def baseEnd_2812558 : Nat := 481398040882770695863429

theorem tailTrace_2812558 : CollatzResearch.WordTrace tailWord_2812558 prefixEnd_2812558 481398040882770695863429 := by
  unfold tailWord_2812558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822802218073773438644791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68388278496393458339438885 12822802218073773438644791)
  ·
    refine ⟨19234203327110660157967187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12822802218073773438644791 19234203327110660157967187)
    ·
      refine ⟨28851304990665990236950781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19234203327110660157967187 28851304990665990236950781)
      ·
        refine ⟨10819239371499746338856543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28851304990665990236950781 10819239371499746338856543)
        ·
          refine ⟨16228859057249619508284815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10819239371499746338856543 16228859057249619508284815)
          ·
            refine ⟨24343288585874429262427223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228859057249619508284815 24343288585874429262427223)
            ·
              refine ⟨36514932878811643893640835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24343288585874429262427223 36514932878811643893640835)
              ·
                refine ⟨54772399318217465840461253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36514932878811643893640835 54772399318217465840461253)
                ·
                  refine ⟨10269824872165774845086485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54772399318217465840461253 10269824872165774845086485)
                  ·
                    refine ⟨481398040882770695863429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10269824872165774845086485 481398040882770695863429)
                    ·
                      rfl

theorem cell23_2812558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2812558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812558 prefixEnd_2812558 := by exact prefixLift 2812558
  have htrace : WordTrace (prefixWord ++ tailWord_2812558) baseStart_2812558 baseEnd_2812558 := by
    simpa [prefixWord, tailWord_2812558, baseEnd_2812558] using wordTrace_append hprefix tailTrace_2812558
  have hstable : (prefixWord ++ tailWord_2812558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812558).length < 2 ^ (prefixWord ++ tailWord_2812558).sum := by decide
  have hdescent : baseEnd_2812558 < baseStart_2812558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812625 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_2812625 : Nat := 118140960795 + 2812625 * 2 ^ 59
def prefixEnd_2812625 : Nat := 4983230072969 + 3 ^ 40 * 2812625 * 2
def baseEnd_2812625 : Nat := 1444228525852163325452479

theorem tailTrace_2812625 : CollatzResearch.WordTrace tailWord_2812625 prefixEnd_2812625 1444228525852163325452479 := by
  unfold tailWord_2812625
  simp only [CollatzResearch.WordTrace]
  refine ⟨102584861435347457951847329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68389907623564971967898219 102584861435347457951847329)
  ·
    refine ⟨76938646076510593463885497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102584861435347457951847329 76938646076510593463885497)
    ·
      refine ⟨57703984557382945097914123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76938646076510593463885497 57703984557382945097914123)
      ·
        refine ⟨86555976836074417646871185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57703984557382945097914123 86555976836074417646871185)
        ·
          refine ⟨64916982627055813235153389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86555976836074417646871185 64916982627055813235153389)
          ·
            refine ⟨24343868485145929963182521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64916982627055813235153389 24343868485145929963182521)
            ·
              refine ⟨18257901363859447472386891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24343868485145929963182521 18257901363859447472386891)
              ·
                refine ⟨27386852045789171208580337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18257901363859447472386891 27386852045789171208580337)
                ·
                  refine ⟨20540139034341878406435253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27386852045789171208580337 20540139034341878406435253)
                  ·
                    refine ⟨1925638034469551100603305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20540139034341878406435253 1925638034469551100603305)
                    ·
                      refine ⟨1444228525852163325452479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925638034469551100603305 1444228525852163325452479)
                      ·
                        rfl

theorem cell23_2812625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_2812625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812625 prefixEnd_2812625 := by exact prefixLift 2812625
  have htrace : WordTrace (prefixWord ++ tailWord_2812625) baseStart_2812625 baseEnd_2812625 := by
    simpa [prefixWord, tailWord_2812625, baseEnd_2812625] using wordTrace_append hprefix tailTrace_2812625
  have hstable : (prefixWord ++ tailWord_2812625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812625).length < 2 ^ (prefixWord ++ tailWord_2812625).sum := by decide
  have hdescent : baseEnd_2812625 < baseStart_2812625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812655 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_2812655 : Nat := 118140960795 + 2812655 * 2 ^ 59
def prefixEnd_2812655 : Nat := 4983230072969 + 3 ^ 40 * 2812655 * 2
def baseEnd_2812655 : Nat := 1444243930271798208077341

theorem tailTrace_2812655 : CollatzResearch.WordTrace tailWord_2812655 prefixEnd_2812655 1444243930271798208077341 := by
  unfold tailWord_2812655
  simp only [CollatzResearch.WordTrace]
  refine ⟨102585955625238773075439419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68390637083492515383626279 102585955625238773075439419)
  ·
    refine ⟨153878933437858159613159129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102585955625238773075439419 153878933437858159613159129)
    ·
      refine ⟨115409200078393619709869347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153878933437858159613159129 115409200078393619709869347)
      ·
        refine ⟨173113800117590429564804021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115409200078393619709869347 173113800117590429564804021)
        ·
          refine ⟨16229418761024102771700377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173113800117590429564804021 16229418761024102771700377)
          ·
            refine ⟨12172064070768077078775283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16229418761024102771700377 12172064070768077078775283)
            ·
              refine ⟨18258096106152115618162925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172064070768077078775283 18258096106152115618162925)
              ·
                refine ⟨6846786039807043356811097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18258096106152115618162925 6846786039807043356811097)
                ·
                  refine ⟨5135089529855282517608323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846786039807043356811097 5135089529855282517608323)
                  ·
                    refine ⟨7702634294782923776412485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135089529855282517608323 7702634294782923776412485)
                    ·
                      refine ⟨1444243930271798208077341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7702634294782923776412485 1444243930271798208077341)
                      ·
                        rfl

theorem cell23_2812655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_2812655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812655 prefixEnd_2812655 := by exact prefixLift 2812655
  have htrace : WordTrace (prefixWord ++ tailWord_2812655) baseStart_2812655 baseEnd_2812655 := by
    simpa [prefixWord, tailWord_2812655, baseEnd_2812655] using wordTrace_append hprefix tailTrace_2812655
  have hstable : (prefixWord ++ tailWord_2812655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812655).length < 2 ^ (prefixWord ++ tailWord_2812655).sum := by decide
  have hdescent : baseEnd_2812655 < baseStart_2812655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812722 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_2812722 : Nat := 118140960795 + 2812722 * 2 ^ 59
def prefixEnd_2812722 : Nat := 4983230072969 + 3 ^ 40 * 2812722 * 2
def baseEnd_2812722 : Nat := 1444278333475649445939533

theorem tailTrace_2812722 : CollatzResearch.WordTrace tailWord_2812722 prefixEnd_2812722 1444278333475649445939533 := by
  unfold tailWord_2812722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647099828999010879532105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68392266210664029012085613 25647099828999010879532105)
  ·
    refine ⟨19235324871749258159649079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25647099828999010879532105 19235324871749258159649079)
    ·
      refine ⟨28852987307623887239473619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19235324871749258159649079 28852987307623887239473619)
      ·
        refine ⟨43279480961435830859210429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28852987307623887239473619 43279480961435830859210429)
        ·
          refine ⟨16229805360538436572203911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43279480961435830859210429 16229805360538436572203911)
          ·
            refine ⟨24344708040807654858305867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16229805360538436572203911 24344708040807654858305867)
            ·
              refine ⟨36517062061211482287458801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24344708040807654858305867 36517062061211482287458801)
              ·
                refine ⟨27387796545908611715594101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36517062061211482287458801 27387796545908611715594101)
                ·
                  refine ⟨2567605926178932348336947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27387796545908611715594101 2567605926178932348336947)
                  ·
                    refine ⟨3851408889268398522505421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567605926178932348336947 3851408889268398522505421)
                    ·
                      refine ⟨1444278333475649445939533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3851408889268398522505421 1444278333475649445939533)
                      ·
                        rfl

theorem cell23_2812722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_2812722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812722 prefixEnd_2812722 := by exact prefixLift 2812722
  have htrace : WordTrace (prefixWord ++ tailWord_2812722) baseStart_2812722 baseEnd_2812722 := by
    simpa [prefixWord, tailWord_2812722, baseEnd_2812722] using wordTrace_append hprefix tailTrace_2812722
  have hstable : (prefixWord ++ tailWord_2812722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812722).length < 2 ^ (prefixWord ++ tailWord_2812722).sum := by decide
  have hdescent : baseEnd_2812722 < baseStart_2812722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812732 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_2812732 : Nat := 118140960795 + 2812732 * 2 ^ 59
def prefixEnd_2812732 : Nat := 4983230072969 + 3 ^ 40 * 2812732 * 2
def baseEnd_2812732 : Nat := 1444283468282194406814487

theorem tailTrace_2812732 : CollatzResearch.WordTrace tailWord_2812732 prefixEnd_2812732 1444283468282194406814487 := by
  unfold tailWord_2812732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51294382022979907612996225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68392509363973210150661633 51294382022979907612996225)
  ·
    refine ⟨38470786517234930709747169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51294382022979907612996225 38470786517234930709747169)
    ·
      refine ⟨28853089887926198032310377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38470786517234930709747169 28853089887926198032310377)
      ·
        refine ⟨21639817415944648524232783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28853089887926198032310377 21639817415944648524232783)
        ·
          refine ⟨32459726123916972786349175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21639817415944648524232783 32459726123916972786349175)
          ·
            refine ⟨48689589185875459179523763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32459726123916972786349175 48689589185875459179523763)
            ·
              refine ⟨73034383778813188769285645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48689589185875459179523763 73034383778813188769285645)
              ·
                refine ⟨27387893917054945788482117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73034383778813188769285645 27387893917054945788482117)
                ·
                  refine ⟨5135230109447802335340397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27387893917054945788482117 5135230109447802335340397)
                  ·
                    refine ⟨1925711291042925875752649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5135230109447802335340397 1925711291042925875752649)
                    ·
                      refine ⟨1444283468282194406814487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925711291042925875752649 1444283468282194406814487)
                      ·
                        rfl

theorem cell23_2812732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_2812732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812732 prefixEnd_2812732 := by exact prefixLift 2812732
  have htrace : WordTrace (prefixWord ++ tailWord_2812732) baseStart_2812732 baseEnd_2812732 := by
    simpa [prefixWord, tailWord_2812732, baseEnd_2812732] using wordTrace_append hprefix tailTrace_2812732
  have hstable : (prefixWord ++ tailWord_2812732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812732).length < 2 ^ (prefixWord ++ tailWord_2812732).sum := by decide
  have hdescent : baseEnd_2812732 < baseStart_2812732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812739 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 1, 1, 3]
def baseStart_2812739 : Nat := 118140960795 + 2812739 * 2 ^ 59
def prefixEnd_2812739 : Nat := 4983230072969 + 3 ^ 40 * 2812739 * 2
def baseEnd_2812739 : Nat := 1444287062646775879426955

theorem tailTrace_2812739 : CollatzResearch.WordTrace tailWord_2812739 prefixEnd_2812739 1444287062646775879426955 := by
  unfold tailWord_2812739
  simp only [CollatzResearch.WordTrace]
  refine ⟨102589019356934455421497271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68392679571289636947664847 102589019356934455421497271)
  ·
    refine ⟨153883529035401683132245907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102589019356934455421497271 153883529035401683132245907)
    ·
      refine ⟨230825293553102524698368861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153883529035401683132245907 230825293553102524698368861)
      ·
        refine ⟨86559485082413446761888323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230825293553102524698368861 86559485082413446761888323)
        ·
          refine ⟨129839227623620170142832485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86559485082413446761888323 129839227623620170142832485)
          ·
            refine ⟨24344855179428781901781091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129839227623620170142832485 24344855179428781901781091)
            ·
              refine ⟨36517282769143172852671637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24344855179428781901781091 36517282769143172852671637)
              ·
                refine ⟨1711747629803586227468983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36517282769143172852671637 1711747629803586227468983)
                ·
                  refine ⟨2567621444705379341203475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711747629803586227468983 2567621444705379341203475)
                  ·
                    refine ⟨3851432167058069011805213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567621444705379341203475 3851432167058069011805213)
                    ·
                      refine ⟨1444287062646775879426955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3851432167058069011805213 1444287062646775879426955)
                      ·
                        rfl

theorem cell23_2812739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_2812739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812739 prefixEnd_2812739 := by exact prefixLift 2812739
  have htrace : WordTrace (prefixWord ++ tailWord_2812739) baseStart_2812739 baseEnd_2812739 := by
    simpa [prefixWord, tailWord_2812739, baseEnd_2812739] using wordTrace_append hprefix tailTrace_2812739
  have hstable : (prefixWord ++ tailWord_2812739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812739).length < 2 ^ (prefixWord ++ tailWord_2812739).sum := by decide
  have hdescent : baseEnd_2812739 < baseStart_2812739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812762 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_2812762 : Nat := 118140960795 + 2812762 * 2 ^ 59
def prefixEnd_2812762 : Nat := 4983230072969 + 3 ^ 40 * 2812762 * 2
def baseEnd_2812762 : Nat := 1444298872701829289439349

theorem tailTrace_2812762 : CollatzResearch.WordTrace tailWord_2812762 prefixEnd_2812762 1444298872701829289439349 := by
  unfold tailWord_2812762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647464558962782587396135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68393238823900753566389693 25647464558962782587396135)
  ·
    refine ⟨38471196838444173881094203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25647464558962782587396135 38471196838444173881094203)
    ·
      refine ⟨57706795257666260821641305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38471196838444173881094203 57706795257666260821641305)
      ·
        refine ⟨43280096443249695616230979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57706795257666260821641305 43280096443249695616230979)
        ·
          refine ⟨64920144664874543424346469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43280096443249695616230979 64920144664874543424346469)
          ·
            refine ⟨12172527124663976892064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64920144664874543424346469 12172527124663976892064963)
            ·
              refine ⟨18258790686995965338097445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172527124663976892064963 18258790686995965338097445)
              ·
                refine ⟨3423523253811743500893271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18258790686995965338097445 3423523253811743500893271)
                ·
                  refine ⟨5135284880717615251339907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423523253811743500893271 5135284880717615251339907)
                  ·
                    refine ⟨7702927321076422877009861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135284880717615251339907 7702927321076422877009861)
                    ·
                      refine ⟨1444298872701829289439349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7702927321076422877009861 1444298872701829289439349)
                      ·
                        rfl

theorem cell23_2812762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_2812762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812762 prefixEnd_2812762 := by exact prefixLift 2812762
  have htrace : WordTrace (prefixWord ++ tailWord_2812762) baseStart_2812762 baseEnd_2812762 := by
    simpa [prefixWord, tailWord_2812762, baseEnd_2812762] using wordTrace_append hprefix tailTrace_2812762
  have hstable : (prefixWord ++ tailWord_2812762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812762).length < 2 ^ (prefixWord ++ tailWord_2812762).sum := by decide
  have hdescent : baseEnd_2812762 < baseStart_2812762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812772 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_2812772 : Nat := 118140960795 + 2812772 * 2 ^ 59
def prefixEnd_2812772 : Nat := 4983230072969 + 3 ^ 40 * 2812772 * 2
def baseEnd_2812772 : Nat := 481434669169458083438101

theorem tailTrace_2812772 : CollatzResearch.WordTrace tailWord_2812772 prefixEnd_2812772 481434669169458083438101 := by
  unfold tailWord_2812772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51295111482907451028724285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68393481977209934704965713 51295111482907451028724285)
  ·
    refine ⟨19235666806090294135771607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51295111482907451028724285 19235666806090294135771607)
    ·
      refine ⟨28853500209135441203657411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19235666806090294135771607 28853500209135441203657411)
      ·
        refine ⟨43280250313703161805486117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28853500209135441203657411 43280250313703161805486117)
        ·
          refine ⟨8115046933819342838528647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43280250313703161805486117 8115046933819342838528647)
          ·
            refine ⟨12172570400729014257792971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115046933819342838528647 12172570400729014257792971)
            ·
              refine ⟨18258855601093521386689457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172570400729014257792971 18258855601093521386689457)
              ·
                refine ⟨13694141700820141040017093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18258855601093521386689457 13694141700820141040017093)
                ·
                  refine ⟨2567651568903776445003205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13694141700820141040017093 2567651568903776445003205)
                  ·
                    refine ⟨481434669169458083438101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567651568903776445003205 481434669169458083438101)
                    ·
                      rfl

theorem cell23_2812772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_2812772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812772 prefixEnd_2812772 := by exact prefixLift 2812772
  have htrace : WordTrace (prefixWord ++ tailWord_2812772) baseStart_2812772 baseEnd_2812772 := by
    simpa [prefixWord, tailWord_2812772, baseEnd_2812772] using wordTrace_append hprefix tailTrace_2812772
  have hstable : (prefixWord ++ tailWord_2812772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812772).length < 2 ^ (prefixWord ++ tailWord_2812772).sum := by decide
  have hdescent : baseEnd_2812772 < baseStart_2812772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812785 : List Nat := [1, 2, 2, 2, 1, 6, 9]
def baseStart_2812785 : Nat := 118140960795 + 2812785 * 2 ^ 59
def prefixEnd_2812785 : Nat := 4983230072969 + 3 ^ 40 * 2812785 * 2
def baseEnd_2812785 : Nat := 17830996083418304931503

theorem tailTrace_2812785 : CollatzResearch.WordTrace tailWord_2812785 prefixEnd_2812785 17830996083418304931503 := by
  unfold tailWord_2812785
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590697114767805277671809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68393798076511870185114539 102590697114767805277671809)
  ·
    refine ⟨76943022836075853958253857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102590697114767805277671809 76943022836075853958253857)
    ·
      refine ⟨57707267127056890468690393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76943022836075853958253857 57707267127056890468690393)
      ·
        refine ⟨43280450345292667851517795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57707267127056890468690393 43280450345292667851517795)
        ·
          refine ⟨64920675517939001777276693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43280450345292667851517795 64920675517939001777276693)
          ·
            refine ⟨3043156664903390708309845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64920675517939001777276693 3043156664903390708309845)
            ·
              refine ⟨17830996083418304931503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3043156664903390708309845 17830996083418304931503)
              ·
                rfl

theorem cell23_2812785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 9].length) (baseStart_2812785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812785 prefixEnd_2812785 := by exact prefixLift 2812785
  have htrace : WordTrace (prefixWord ++ tailWord_2812785) baseStart_2812785 baseEnd_2812785 := by
    simpa [prefixWord, tailWord_2812785, baseEnd_2812785] using wordTrace_append hprefix tailTrace_2812785
  have hstable : (prefixWord ++ tailWord_2812785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812785).length < 2 ^ (prefixWord ++ tailWord_2812785).sum := by decide
  have hdescent : baseEnd_2812785 < baseStart_2812785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812790 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2812790 : Nat := 118140960795 + 2812790 * 2 ^ 59
def prefixEnd_2812790 : Nat := 4983230072969 + 3 ^ 40 * 2812790 * 2
def baseEnd_2812790 : Nat := 1444313250160155179889221

theorem tailTrace_2812790 : CollatzResearch.WordTrace tailWord_2812790 prefixEnd_2812790 1444313250160155179889221 := by
  unfold tailWord_2812790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411929967484355695725239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68393919653166460754402549 6411929967484355695725239)
  ·
    refine ⟨9617894951226533543587859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411929967484355695725239 9617894951226533543587859)
    ·
      refine ⟨14426842426839800315381789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9617894951226533543587859 14426842426839800315381789)
      ·
        refine ⟨5410065910064925118268171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14426842426839800315381789 5410065910064925118268171)
        ·
          refine ⟨8115098865097387677402257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410065910064925118268171 8115098865097387677402257)
          ·
            refine ⟨6086324148823040758051693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115098865097387677402257 6086324148823040758051693)
            ·
              refine ⟨2282371555808640284269385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086324148823040758051693 2282371555808640284269385)
              ·
                refine ⟨1711778666856480213202039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282371555808640284269385 1711778666856480213202039)
                ·
                  refine ⟨2567668000284720319803059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711778666856480213202039 2567668000284720319803059)
                  ·
                    refine ⟨3851502000427080479704589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567668000284720319803059 3851502000427080479704589)
                    ·
                      refine ⟨1444313250160155179889221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3851502000427080479704589 1444313250160155179889221)
                      ·
                        rfl

theorem cell23_2812790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2812790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812790 prefixEnd_2812790 := by exact prefixLift 2812790
  have htrace : WordTrace (prefixWord ++ tailWord_2812790) baseStart_2812790 baseEnd_2812790 := by
    simpa [prefixWord, tailWord_2812790, baseEnd_2812790] using wordTrace_append hprefix tailTrace_2812790
  have hstable : (prefixWord ++ tailWord_2812790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812790).length < 2 ^ (prefixWord ++ tailWord_2812790).sum := by decide
  have hdescent : baseEnd_2812790 < baseStart_2812790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812796 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_2812796 : Nat := 118140960795 + 2812796 * 2 ^ 59
def prefixEnd_2812796 : Nat := 4983230072969 + 3 ^ 40 * 2812796 * 2
def baseEnd_2812796 : Nat := 1444316331044082156414193

theorem tailTrace_2812796 : CollatzResearch.WordTrace tailWord_2812796 prefixEnd_2812796 1444316331044082156414193 := by
  unfold tailWord_2812796
  simp only [CollatzResearch.WordTrace]
  refine ⟨51295549158863977078161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68394065545151969437548161 51295549158863977078161121)
  ·
    refine ⟨38471661869147982808620841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51295549158863977078161121 38471661869147982808620841)
    ·
      refine ⟨28853746401860987106465631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38471661869147982808620841 28853746401860987106465631)
      ·
        refine ⟨43280619602791480659698447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28853746401860987106465631 43280619602791480659698447)
        ·
          refine ⟨64920929404187220989547671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43280619602791480659698447 64920929404187220989547671)
          ·
            refine ⟨97381394106280831484321507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64920929404187220989547671 97381394106280831484321507)
            ·
              refine ⟨146072091159421247226482261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97381394106280831484321507 146072091159421247226482261)
              ·
                refine ⟨1711782318274467740935339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 146072091159421247226482261 1711782318274467740935339)
                ·
                  refine ⟨2567673477411701611403009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711782318274467740935339 2567673477411701611403009)
                  ·
                    refine ⟨1925755108058776208552257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567673477411701611403009 1925755108058776208552257)
                    ·
                      refine ⟨1444316331044082156414193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925755108058776208552257 1444316331044082156414193)
                      ·
                        rfl

theorem cell23_2812796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_2812796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812796 prefixEnd_2812796 := by exact prefixLift 2812796
  have htrace : WordTrace (prefixWord ++ tailWord_2812796) baseStart_2812796 baseEnd_2812796 := by
    simpa [prefixWord, tailWord_2812796, baseEnd_2812796] using wordTrace_append hprefix tailTrace_2812796
  have hstable : (prefixWord ++ tailWord_2812796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812796).length < 2 ^ (prefixWord ++ tailWord_2812796).sum := by decide
  have hdescent : baseEnd_2812796 < baseStart_2812796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812855 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2812855 : Nat := 118140960795 + 2812855 * 2 ^ 59
def prefixEnd_2812855 : Nat := 4983230072969 + 3 ^ 40 * 2812855 * 2
def baseEnd_2812855 : Nat := 1444346626402697425576421

theorem tailTrace_2812855 : CollatzResearch.WordTrace tailWord_2812855 prefixEnd_2812855 1444346626402697425576421 := by
  unfold tailWord_2812855
  simp only [CollatzResearch.WordTrace]
  refine ⟨102593250224514207232720019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68395500149676138155146679 102593250224514207232720019)
  ·
    refine ⟨153889875336771310849080029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102593250224514207232720019 153889875336771310849080029)
    ·
      refine ⟨57708703251289241568405011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153889875336771310849080029 57708703251289241568405011)
      ·
        refine ⟨86563054876933862352607517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57708703251289241568405011 86563054876933862352607517)
        ·
          refine ⟨32461145578850198382227819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86563054876933862352607517 32461145578850198382227819)
          ·
            refine ⟨48691718368275297573341729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32461145578850198382227819 48691718368275297573341729)
            ·
              refine ⟨36518788776206473180006297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48691718368275297573341729 36518788776206473180006297)
              ·
                refine ⟨27389091582154854885004723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36518788776206473180006297 27389091582154854885004723)
                ·
                  refine ⟨41083637373232282327507085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27389091582154854885004723 41083637373232282327507085)
                  ·
                    refine ⟨15406364014962105872815157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41083637373232282327507085 15406364014962105872815157)
                    ·
                      refine ⟨1444346626402697425576421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15406364014962105872815157 1444346626402697425576421)
                      ·
                        rfl

theorem cell23_2812855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2812855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812855 prefixEnd_2812855 := by exact prefixLift 2812855
  have htrace : WordTrace (prefixWord ++ tailWord_2812855) baseStart_2812855 baseEnd_2812855 := by
    simpa [prefixWord, tailWord_2812855, baseEnd_2812855] using wordTrace_append hprefix tailTrace_2812855
  have hstable : (prefixWord ++ tailWord_2812855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812855).length < 2 ^ (prefixWord ++ tailWord_2812855).sum := by decide
  have hdescent : baseEnd_2812855 < baseStart_2812855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812862 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2812862 : Nat := 118140960795 + 2812862 * 2 ^ 59
def prefixEnd_2812862 : Nat := 4983230072969 + 3 ^ 40 * 2812862 * 2
def baseEnd_2812862 : Nat := 481450073589092966062963

theorem tailTrace_2812862 : CollatzResearch.WordTrace tailWord_2812862 prefixEnd_2812862 481450073589092966062963 := by
  unfold tailWord_2812862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12824188191936105928528105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68395670356992564952149893 12824188191936105928528105)
  ·
    refine ⟨9618141143952079446396079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12824188191936105928528105 9618141143952079446396079)
    ·
      refine ⟨14427211715928119169594119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618141143952079446396079 14427211715928119169594119)
      ·
        refine ⟨21640817573892178754391179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14427211715928119169594119 21640817573892178754391179)
        ·
          refine ⟨32461226360838268131586769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21640817573892178754391179 32461226360838268131586769)
          ·
            refine ⟨24345919770628701098690077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32461226360838268131586769 24345919770628701098690077)
            ·
              refine ⟨9129719913985762912008779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24345919770628701098690077 9129719913985762912008779)
              ·
                refine ⟨13694579870978644368013169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9129719913985762912008779 13694579870978644368013169)
                ·
                  refine ⟨10270934903233983276009877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13694579870978644368013169 10270934903233983276009877)
                  ·
                    refine ⟨481450073589092966062963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10270934903233983276009877 481450073589092966062963)
                    ·
                      rfl

theorem cell23_2812862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2812862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812862 prefixEnd_2812862 := by exact prefixLift 2812862
  have htrace : WordTrace (prefixWord ++ tailWord_2812862) baseStart_2812862 baseEnd_2812862 := by
    simpa [prefixWord, tailWord_2812862, baseEnd_2812862] using wordTrace_append hprefix tailTrace_2812862
  have hstable : (prefixWord ++ tailWord_2812862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812862).length < 2 ^ (prefixWord ++ tailWord_2812862).sum := by decide
  have hdescent : baseEnd_2812862 < baseStart_2812862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812870 : List Nat := [6, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2812870 : Nat := 118140960795 + 2812870 * 2 ^ 59
def prefixEnd_2812870 : Nat := 4983230072969 + 3 ^ 40 * 2812870 * 2
def baseEnd_2812870 : Nat := 53494604763426476551439

theorem tailTrace_2812870 : CollatzResearch.WordTrace tailWord_2812870 prefixEnd_2812870 53494604763426476551439 := by
  unfold tailWord_2812870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206056166233120774828627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68395864879639909863010709 3206056166233120774828627)
  ·
    refine ⟨4809084249349681162242941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206056166233120774828627 4809084249349681162242941)
    ·
      refine ⟨1803406593506130435841103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4809084249349681162242941 1803406593506130435841103)
      ·
        refine ⟨2705109890259195653761655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803406593506130435841103 2705109890259195653761655)
        ·
          refine ⟨4057664835388793480642483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705109890259195653761655 4057664835388793480642483)
          ·
            refine ⟨6086497253083190220963725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057664835388793480642483 6086497253083190220963725)
            ·
              refine ⟨2282436469906196332861397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086497253083190220963725 2282436469906196332861397)
              ·
                refine ⟨53494604763426476551439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2282436469906196332861397 53494604763426476551439)
                ·
                  rfl

theorem cell23_2812870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2812870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812870 prefixEnd_2812870 := by exact prefixLift 2812870
  have htrace : WordTrace (prefixWord ++ tailWord_2812870) baseStart_2812870 baseEnd_2812870 := by
    simpa [prefixWord, tailWord_2812870, baseEnd_2812870] using wordTrace_append hprefix tailTrace_2812870
  have hstable : (prefixWord ++ tailWord_2812870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812870).length < 2 ^ (prefixWord ++ tailWord_2812870).sum := by decide
  have hdescent : baseEnd_2812870 < baseStart_2812870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812875 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 9]
def baseStart_2812875 : Nat := 118140960795 + 2812875 * 2 ^ 59
def prefixEnd_2812875 : Nat := 4983230072969 + 3 ^ 40 * 2812875 * 2
def baseEnd_2812875 : Nat := 160484099557309705258481

theorem tailTrace_2812875 : CollatzResearch.WordTrace tailWord_2812875 prefixEnd_2812875 160484099557309705258481 := by
  unfold tailWord_2812875
  simp only [CollatzResearch.WordTrace]
  refine ⟨102593979684441750648448079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68395986456294500432298719 102593979684441750648448079)
  ·
    refine ⟨153890969526662625972672119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102593979684441750648448079 153890969526662625972672119)
    ·
      refine ⟨230836454289993938959008179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153890969526662625972672119 230836454289993938959008179)
      ·
        refine ⟨346254681434990908438512269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230836454289993938959008179 346254681434990908438512269)
        ·
          refine ⟨129845505538121590664442101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346254681434990908438512269 129845505538121590664442101)
          ·
            refine ⟨12173016144198899124791447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129845505538121590664442101 12173016144198899124791447)
            ·
              refine ⟨18259524216298348687187171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173016144198899124791447 18259524216298348687187171)
              ·
                refine ⟨27389286324447523030780757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18259524216298348687187171 27389286324447523030780757)
                ·
                  refine ⟨160484099557309705258481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27389286324447523030780757 160484099557309705258481)
                  ·
                    rfl

theorem cell23_2812875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_2812875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812875 prefixEnd_2812875 := by exact prefixLift 2812875
  have htrace : WordTrace (prefixWord ++ tailWord_2812875) baseStart_2812875 baseEnd_2812875 := by
    simpa [prefixWord, tailWord_2812875, baseEnd_2812875] using wordTrace_append hprefix tailTrace_2812875
  have hstable : (prefixWord ++ tailWord_2812875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812875).length < 2 ^ (prefixWord ++ tailWord_2812875).sum := by decide
  have hdescent : baseEnd_2812875 < baseStart_2812875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812903 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2812903 : Nat := 118140960795 + 2812903 * 2 ^ 59
def prefixEnd_2812903 : Nat := 4983230072969 + 3 ^ 40 * 2812903 * 2
def baseEnd_2812903 : Nat := 1444371273474113237776201

theorem tailTrace_2812903 : CollatzResearch.WordTrace tailWord_2812903 prefixEnd_2812903 1444371273474113237776201 := by
  unfold tailWord_2812903
  simp only [CollatzResearch.WordTrace]
  refine ⟨102595000928340311430467363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68396667285560207620311575 102595000928340311430467363)
  ·
    refine ⟨153892501392510467145701045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102595000928340311430467363 153892501392510467145701045)
    ·
      refine ⟨14427422005547856294909473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153892501392510467145701045 14427422005547856294909473)
      ·
        refine ⟨10820566504160892221182105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14427422005547856294909473 10820566504160892221182105)
        ·
          refine ⟨8115424878120669165886579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10820566504160892221182105 8115424878120669165886579)
          ·
            refine ⟨12173137317181003748829869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115424878120669165886579 12173137317181003748829869)
            ·
              refine ⟨4564926493942876405811201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12173137317181003748829869 4564926493942876405811201)
              ·
                refine ⟨3423694870457157304358401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4564926493942876405811201 3423694870457157304358401)
                ·
                  refine ⟨2567771152842867978268801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3423694870457157304358401 2567771152842867978268801)
                  ·
                    refine ⟨1925828364632150983701601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567771152842867978268801 1925828364632150983701601)
                    ·
                      refine ⟨1444371273474113237776201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925828364632150983701601 1444371273474113237776201)
                      ·
                        rfl

theorem cell23_2812903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2812903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812903 prefixEnd_2812903 := by exact prefixLift 2812903
  have htrace : WordTrace (prefixWord ++ tailWord_2812903) baseStart_2812903 baseEnd_2812903 := by
    simpa [prefixWord, tailWord_2812903, baseEnd_2812903] using wordTrace_append hprefix tailTrace_2812903
  have hstable : (prefixWord ++ tailWord_2812903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812903).length < 2 ^ (prefixWord ++ tailWord_2812903).sum := by decide
  have hdescent : baseEnd_2812903 < baseStart_2812903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812959 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2812959 : Nat := 118140960795 + 2812959 * 2 ^ 59
def prefixEnd_2812959 : Nat := 4983230072969 + 3 ^ 40 * 2812959 * 2
def baseEnd_2812959 : Nat := 1444400028390765018675943

theorem tailTrace_2812959 : CollatzResearch.WordTrace tailWord_2812959 prefixEnd_2812959 1444400028390765018675943 := by
  unfold tailWord_2812959
  simp only [CollatzResearch.WordTrace]
  refine ⟨102597043416137432994505931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68398028944091621996337287 102597043416137432994505931)
  ·
    refine ⟨153895565124206149491758897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102597043416137432994505931 153895565124206149491758897)
    ·
      refine ⟨115421673843154612118819173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153895565124206149491758897 115421673843154612118819173)
      ·
        refine ⟨21641563845591489772278595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115421673843154612118819173 21641563845591489772278595)
        ·
          refine ⟨32462345768387234658417893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21641563845591489772278595 32462345768387234658417893)
          ·
            refine ⟨6086689831572606498453355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32462345768387234658417893 6086689831572606498453355)
            ·
              refine ⟨9130034747358909747680033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086689831572606498453355 9130034747358909747680033)
              ·
                refine ⟨6847526060519182310760025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9130034747358909747680033 6847526060519182310760025)
                ·
                  refine ⟨5135644545389386733070019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6847526060519182310760025 5135644545389386733070019)
                  ·
                    refine ⟨7703466818084080099605029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135644545389386733070019 7703466818084080099605029)
                    ·
                      refine ⟨1444400028390765018675943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7703466818084080099605029 1444400028390765018675943)
                      ·
                        rfl

theorem cell23_2812959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2812959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2812959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2812959 prefixEnd_2812959 := by exact prefixLift 2812959
  have htrace : WordTrace (prefixWord ++ tailWord_2812959) baseStart_2812959 baseEnd_2812959 := by
    simpa [prefixWord, tailWord_2812959, baseEnd_2812959] using wordTrace_append hprefix tailTrace_2812959
  have hstable : (prefixWord ++ tailWord_2812959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812959).length < 2 ^ (prefixWord ++ tailWord_2812959).sum := by decide
  have hdescent : baseEnd_2812959 < baseStart_2812959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813046 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2813046 : Nat := 118140960795 + 2813046 * 2 ^ 59
def prefixEnd_2813046 : Nat := 4983230072969 + 3 ^ 40 * 2813046 * 2
def baseEnd_2813046 : Nat := 481481567069235392762681

theorem tailTrace_2813046 : CollatzResearch.WordTrace tailWord_2813046 prefixEnd_2813046 481481567069235392762681 := by
  unfold tailWord_2813046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412513535426390428307687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68400144377881497901948661 6412513535426390428307687)
  ·
    refine ⟨9618770303139585642461531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412513535426390428307687 9618770303139585642461531)
    ·
      refine ⟨14428155454709378463692297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618770303139585642461531 14428155454709378463692297)
      ·
        refine ⟨10821116591032033847769223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14428155454709378463692297 10821116591032033847769223)
        ·
          refine ⟨16231674886548050771653835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10821116591032033847769223 16231674886548050771653835)
          ·
            refine ⟨24347512329822076157480753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16231674886548050771653835 24347512329822076157480753)
            ·
              refine ⟨18260634247366557118110565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24347512329822076157480753 18260634247366557118110565)
              ·
                refine ⟨3423868921381229459645731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18260634247366557118110565 3423868921381229459645731)
                ·
                  refine ⟨5135803382071844189468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423868921381229459645731 5135803382071844189468597)
                  ·
                    refine ⟨481481567069235392762681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5135803382071844189468597 481481567069235392762681)
                    ·
                      rfl

theorem cell23_2813046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2813046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813046 prefixEnd_2813046 := by exact prefixLift 2813046
  have htrace : WordTrace (prefixWord ++ tailWord_2813046) baseStart_2813046 baseEnd_2813046 := by
    simpa [prefixWord, tailWord_2813046, baseEnd_2813046] using wordTrace_append hprefix tailTrace_2813046
  have hstable : (prefixWord ++ tailWord_2813046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813046).length < 2 ^ (prefixWord ++ tailWord_2813046).sum := by decide
  have hdescent : baseEnd_2813046 < baseStart_2813046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813054 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2813054 : Nat := 118140960795 + 2813054 * 2 ^ 59
def prefixEnd_2813054 : Nat := 4983230072969 + 3 ^ 40 * 2813054 * 2
def baseEnd_2813054 : Nat := 481482936350980715662669

theorem tailTrace_2813054 : CollatzResearch.WordTrace tailWord_2813054 prefixEnd_2813054 481482936350980715662669 := by
  unfold tailWord_2813054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825063543849158027401777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68400338900528842812809477 12825063543849158027401777)
  ·
    refine ⟨9618797657886868520551333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12825063543849158027401777 9618797657886868520551333)
    ·
      refine ⟨1803524560853787847603375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9618797657886868520551333 1803524560853787847603375)
      ·
        refine ⟨2705286841280681771405063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803524560853787847603375 2705286841280681771405063)
        ·
          refine ⟨4057930261921022657107595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705286841280681771405063 4057930261921022657107595)
          ·
            refine ⟨6086895392881533985661393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057930261921022657107595 6086895392881533985661393)
            ·
              refine ⟨4565171544661150489246045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6086895392881533985661393 4565171544661150489246045)
              ·
                refine ⟨1711939329247931433467267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565171544661150489246045 1711939329247931433467267)
                ·
                  refine ⟨2567908993871897150200901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711939329247931433467267 2567908993871897150200901)
                  ·
                    refine ⟨481482936350980715662669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567908993871897150200901 481482936350980715662669)
                    ·
                      rfl

theorem cell23_2813054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2813054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813054 prefixEnd_2813054 := by exact prefixLift 2813054
  have htrace : WordTrace (prefixWord ++ tailWord_2813054) baseStart_2813054 baseEnd_2813054 := by
    simpa [prefixWord, tailWord_2813054, baseEnd_2813054] using wordTrace_append hprefix tailTrace_2813054
  have hstable : (prefixWord ++ tailWord_2813054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813054).length < 2 ^ (prefixWord ++ tailWord_2813054).sum := by decide
  have hdescent : baseEnd_2813054 < baseStart_2813054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813059 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 4, 4]
def baseStart_2813059 : Nat := 118140960795 + 2813059 * 2 ^ 59
def prefixEnd_2813059 : Nat := 4983230072969 + 3 ^ 40 * 2813059 * 2
def baseEnd_2813059 : Nat := 481483792152071542475161

theorem tailTrace_2813059 : CollatzResearch.WordTrace tailWord_2813059 prefixEnd_2813059 481483792152071542475161 := by
  unfold tailWord_2813059
  simp only [CollatzResearch.WordTrace]
  refine ⟨102600690715775150073146231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68400460477183433382097487 102600690715775150073146231)
  ·
    refine ⟨153901036073662725109719347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102600690715775150073146231 153901036073662725109719347)
    ·
      refine ⟨230851554110494087664579021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153901036073662725109719347 230851554110494087664579021)
      ·
        refine ⟨86569332791435282874217133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230851554110494087664579021 86569332791435282874217133)
        ·
          refine ⟨32463499796788231077831425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86569332791435282874217133 32463499796788231077831425)
          ·
            refine ⟨24347624847591173308373569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32463499796788231077831425 24347624847591173308373569)
            ·
              refine ⟨18260718635693379981280177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24347624847591173308373569 18260718635693379981280177)
              ·
                refine ⟨13695538976770034985960133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18260718635693379981280177 13695538976770034985960133)
                ·
                  refine ⟨2567913558144381559867525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13695538976770034985960133 2567913558144381559867525)
                  ·
                    refine ⟨481483792152071542475161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567913558144381559867525 481483792152071542475161)
                    ·
                      rfl

theorem cell23_2813059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 4].length) (baseStart_2813059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813059 prefixEnd_2813059 := by exact prefixLift 2813059
  have htrace : WordTrace (prefixWord ++ tailWord_2813059) baseStart_2813059 baseEnd_2813059 := by
    simpa [prefixWord, tailWord_2813059, baseEnd_2813059] using wordTrace_append hprefix tailTrace_2813059
  have hstable : (prefixWord ++ tailWord_2813059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813059).length < 2 ^ (prefixWord ++ tailWord_2813059).sum := by decide
  have hdescent : baseEnd_2813059 < baseStart_2813059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813060 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2813060 : Nat := 118140960795 + 2813060 * 2 ^ 59
def prefixEnd_2813060 : Nat := 4983230072969 + 3 ^ 40 * 2813060 * 2
def baseEnd_2813060 : Nat := 1444451889936869123512979

theorem tailTrace_2813060 : CollatzResearch.WordTrace tailWord_2813060 prefixEnd_2813060 1444451889936869123512979 := by
  unfold tailWord_2813060
  simp only [CollatzResearch.WordTrace]
  refine ⟨51300363594385763621966317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68400484792514351495955089 51300363594385763621966317)
  ·
    refine ⟨19237636347894661358237369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51300363594385763621966317 19237636347894661358237369)
    ·
      refine ⟨14428227260920996018678027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19237636347894661358237369 14428227260920996018678027)
      ·
        refine ⟨21642340891381494028017041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14428227260920996018678027 21642340891381494028017041)
        ·
          refine ⟨16231755668536120521012781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21642340891381494028017041 16231755668536120521012781)
          ·
            refine ⟨6086908375701045195379793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16231755668536120521012781 6086908375701045195379793)
            ·
              refine ⟨4565181281775783896534845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6086908375701045195379793 4565181281775783896534845)
              ·
                refine ⟨1711942980665918961200567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565181281775783896534845 1711942980665918961200567)
                ·
                  refine ⟨2567914470998878441800851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711942980665918961200567 2567914470998878441800851)
                  ·
                    refine ⟨3851871706498317662701277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567914470998878441800851 3851871706498317662701277)
                    ·
                      refine ⟨1444451889936869123512979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3851871706498317662701277 1444451889936869123512979)
                      ·
                        rfl

theorem cell23_2813060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2813060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813060 prefixEnd_2813060 := by exact prefixLift 2813060
  have htrace : WordTrace (prefixWord ++ tailWord_2813060) baseStart_2813060 baseEnd_2813060 := by
    simpa [prefixWord, tailWord_2813060, baseEnd_2813060] using wordTrace_append hprefix tailTrace_2813060
  have hstable : (prefixWord ++ tailWord_2813060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813060).length < 2 ^ (prefixWord ++ tailWord_2813060).sum := by decide
  have hdescent : baseEnd_2813060 < baseStart_2813060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813066 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_2813066 : Nat := 118140960795 + 2813066 * 2 ^ 59
def prefixEnd_2813066 : Nat := 4983230072969 + 3 ^ 40 * 2813066 * 2
def baseEnd_2813066 : Nat := 1444454970820796100037951

theorem tailTrace_2813066 : CollatzResearch.WordTrace tailWord_2813066 prefixEnd_2813066 1444454970820796100037951 := by
  unfold tailWord_2813066
  simp only [CollatzResearch.WordTrace]
  refine ⟨25650236506687447567162763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68400630684499860179100701 25650236506687447567162763)
  ·
    refine ⟨38475354760031171350744145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25650236506687447567162763 38475354760031171350744145)
    ·
      refine ⟨28856516070023378513058109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38475354760031171350744145 28856516070023378513058109)
      ·
        refine ⟨10821193526258766942396791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28856516070023378513058109 10821193526258766942396791)
        ·
          refine ⟨16231790289388150413595187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10821193526258766942396791 16231790289388150413595187)
          ·
            refine ⟨24347685434082225620392781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16231790289388150413595187 24347685434082225620392781)
            ·
              refine ⟨9130382037780834607647293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24347685434082225620392781 9130382037780834607647293)
              ·
                refine ⟨3423893264167812977867735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9130382037780834607647293 3423893264167812977867735)
                ·
                  refine ⟨5135839896251719466801603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423893264167812977867735 5135839896251719466801603)
                  ·
                    refine ⟨7703759844377579200202405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135839896251719466801603 7703759844377579200202405)
                    ·
                      refine ⟨1444454970820796100037951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7703759844377579200202405 1444454970820796100037951)
                      ·
                        rfl

theorem cell23_2813066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_2813066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813066 prefixEnd_2813066 := by exact prefixLift 2813066
  have htrace : WordTrace (prefixWord ++ tailWord_2813066) baseStart_2813066 baseEnd_2813066 := by
    simpa [prefixWord, tailWord_2813066, baseEnd_2813066] using wordTrace_append hprefix tailTrace_2813066
  have hstable : (prefixWord ++ tailWord_2813066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813066).length < 2 ^ (prefixWord ++ tailWord_2813066).sum := by decide
  have hdescent : baseEnd_2813066 < baseStart_2813066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813086 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2813086 : Nat := 118140960795 + 2813086 * 2 ^ 59
def prefixEnd_2813086 : Nat := 4983230072969 + 3 ^ 40 * 2813086 * 2
def baseEnd_2813086 : Nat := 1444465240433886021787859

theorem tailTrace_2813086 : CollatzResearch.WordTrace tailWord_2813086 prefixEnd_2813086 1444465240433886021787859 := by
  unfold tailWord_2813086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825209435834666710547389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68401116991118222456252741 12825209435834666710547389)
  ·
    refine ⟨4809453538438000016455271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12825209435834666710547389 4809453538438000016455271)
    ·
      refine ⟨7214180307657000024682907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809453538438000016455271 7214180307657000024682907)
      ·
        refine ⟨10821270461485500037024361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214180307657000024682907 10821270461485500037024361)
        ·
          refine ⟨8115952846114125027768271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821270461485500037024361 8115952846114125027768271)
          ·
            refine ⟨12173929269171187541652407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115952846114125027768271 12173929269171187541652407)
            ·
              refine ⟨18260893903756781312478611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173929269171187541652407 18260893903756781312478611)
              ·
                refine ⟨27391340855635171968717917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18260893903756781312478611 27391340855635171968717917)
                ·
                  refine ⟨10271752820863189488269219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27391340855635171968717917 10271752820863189488269219)
                  ·
                    refine ⟨15407629231294784232403829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10271752820863189488269219 15407629231294784232403829)
                    ·
                      refine ⟨1444465240433886021787859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15407629231294784232403829 1444465240433886021787859)
                      ·
                        rfl

theorem cell23_2813086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2813086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813086 prefixEnd_2813086 := by exact prefixLift 2813086
  have htrace : WordTrace (prefixWord ++ tailWord_2813086) baseStart_2813086 baseEnd_2813086 := by
    simpa [prefixWord, tailWord_2813086, baseEnd_2813086] using wordTrace_append hprefix tailTrace_2813086
  have hstable : (prefixWord ++ tailWord_2813086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813086).length < 2 ^ (prefixWord ++ tailWord_2813086).sum := by decide
  have hdescent : baseEnd_2813086 < baseStart_2813086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813093 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_2813093 : Nat := 118140960795 + 2813093 * 2 ^ 59
def prefixEnd_2813093 : Nat := 4983230072969 + 3 ^ 40 * 2813093 * 2
def baseEnd_2813093 : Nat := 481489611599489164800109

theorem tailTrace_2813093 : CollatzResearch.WordTrace tailWord_2813093 prefixEnd_2813093 481489611599489164800109 := by
  unfold tailWord_2813093
  simp only [CollatzResearch.WordTrace]
  refine ⟨102601930797651973879883933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68401287198434649253255955 102601930797651973879883933)
  ·
    refine ⟨38475724049119490204956475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102601930797651973879883933 38475724049119490204956475)
    ·
      refine ⟨57713586073679235307434713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38475724049119490204956475 57713586073679235307434713)
      ·
        refine ⟨43285189555259426480576035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57713586073679235307434713 43285189555259426480576035)
        ·
          refine ⟨64927784332889139720864053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43285189555259426480576035 64927784332889139720864053)
          ·
            refine ⟨6086979781208356848831005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64927784332889139720864053 6086979781208356848831005)
            ·
              refine ⟨2282617417953133818311627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086979781208356848831005 2282617417953133818311627)
              ·
                refine ⟨3423926126929700727467441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282617417953133818311627 3423926126929700727467441)
                ·
                  refine ⟨2567944595197275545600581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3423926126929700727467441 2567944595197275545600581)
                  ·
                    refine ⟨481489611599489164800109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2567944595197275545600581 481489611599489164800109)
                    ·
                      rfl

theorem cell23_2813093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_2813093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813093 prefixEnd_2813093 := by exact prefixLift 2813093
  have htrace : WordTrace (prefixWord ++ tailWord_2813093) baseStart_2813093 baseEnd_2813093 := by
    simpa [prefixWord, tailWord_2813093, baseEnd_2813093] using wordTrace_append hprefix tailTrace_2813093
  have hstable : (prefixWord ++ tailWord_2813093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813093).length < 2 ^ (prefixWord ++ tailWord_2813093).sum := by decide
  have hdescent : baseEnd_2813093 < baseStart_2813093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813106 : List Nat := [3, 2, 1, 1, 1, 6, 2, 7]
def baseStart_2813106 : Nat := 118140960795 + 2813106 * 2 ^ 59
def prefixEnd_2813106 : Nat := 4983230072969 + 3 ^ 40 * 2813106 * 2
def baseEnd_2813106 : Nat := 53499092964702812723621

theorem tailTrace_2813106 : CollatzResearch.WordTrace tailWord_2813106 prefixEnd_2813106 53499092964702812723621 := by
  unfold tailWord_2813106
  simp only [CollatzResearch.WordTrace]
  refine ⟨25650601236651219275026793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68401603297736584733404781 25650601236651219275026793)
  ·
    refine ⟨19237950927488414456270095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25650601236651219275026793 19237950927488414456270095)
    ·
      refine ⟨28856926391232621684405143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19237950927488414456270095 28856926391232621684405143)
      ·
        refine ⟨43285389586848932526607715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28856926391232621684405143 43285389586848932526607715)
        ·
          refine ⟨64928084380273398789911573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43285389586848932526607715 64928084380273398789911573)
          ·
            refine ⟨3043503955325315568277105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64928084380273398789911573 3043503955325315568277105)
            ·
              refine ⟨2282627966493986676207829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043503955325315568277105 2282627966493986676207829)
              ·
                refine ⟨53499092964702812723621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2282627966493986676207829 53499092964702812723621)
                ·
                  rfl

theorem cell23_2813106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 7].length) (baseStart_2813106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813106 prefixEnd_2813106 := by exact prefixLift 2813106
  have htrace : WordTrace (prefixWord ++ tailWord_2813106) baseStart_2813106 baseEnd_2813106 := by
    simpa [prefixWord, tailWord_2813106, baseEnd_2813106] using wordTrace_append hprefix tailTrace_2813106
  have hstable : (prefixWord ++ tailWord_2813106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813106).length < 2 ^ (prefixWord ++ tailWord_2813106).sum := by decide
  have hdescent : baseEnd_2813106 < baseStart_2813106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813134 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_2813134 : Nat := 118140960795 + 2813134 * 2 ^ 59
def prefixEnd_2813134 : Nat := 4983230072969 + 3 ^ 40 * 2813134 * 2
def baseEnd_2813134 : Nat := 1444489887505301833987639

theorem tailTrace_2813134 : CollatzResearch.WordTrace tailWord_2813134 prefixEnd_2813134 1444489887505301833987639 := by
  unfold tailWord_2813134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825428273812929735265807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68402284127002291921417637 12825428273812929735265807)
  ·
    refine ⟨19238142410719394602898711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12825428273812929735265807 19238142410719394602898711)
    ·
      refine ⟨28857213616079091904348067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19238142410719394602898711 28857213616079091904348067)
      ·
        refine ⟨43285820424118637856522101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28857213616079091904348067 43285820424118637856522101)
        ·
          refine ⟨4058045664761122299048947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43285820424118637856522101 4058045664761122299048947)
          ·
            refine ⟨6087068497141683448573421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058045664761122299048947 6087068497141683448573421)
            ·
              refine ⟨2282650686428131293215033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6087068497141683448573421 2282650686428131293215033)
              ·
                refine ⟨1711988014821098469911275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282650686428131293215033 1711988014821098469911275)
                ·
                  refine ⟨2567982022231647704866913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711988014821098469911275 2567982022231647704866913)
                  ·
                    refine ⟨1925986516673735778650185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567982022231647704866913 1925986516673735778650185)
                    ·
                      refine ⟨1444489887505301833987639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1925986516673735778650185 1444489887505301833987639)
                      ·
                        rfl

theorem cell23_2813134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_2813134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813134 prefixEnd_2813134 := by exact prefixLift 2813134
  have htrace : WordTrace (prefixWord ++ tailWord_2813134) baseStart_2813134 baseEnd_2813134 := by
    simpa [prefixWord, tailWord_2813134, baseEnd_2813134] using wordTrace_append hprefix tailTrace_2813134
  have hstable : (prefixWord ++ tailWord_2813134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813134).length < 2 ^ (prefixWord ++ tailWord_2813134).sum := by decide
  have hdescent : baseEnd_2813134 < baseStart_2813134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813169 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2813169 : Nat := 118140960795 + 2813169 * 2 ^ 59
def prefixEnd_2813169 : Nat := 4983230072969 + 3 ^ 40 * 2813169 * 2
def baseEnd_2813169 : Nat := 1444507859328209197049977

theorem tailTrace_2813169 : CollatzResearch.WordTrace tailWord_2813169 prefixEnd_2813169 1444507859328209197049977 := by
  unfold tailWord_2813169
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604702745376638859650561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68403135163584425906433707 102604702745376638859650561)
  ·
    refine ⟨76953527059032479144737921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102604702745376638859650561 76953527059032479144737921)
    ·
      refine ⟨57715145294274359358553441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76953527059032479144737921 57715145294274359358553441)
      ·
        refine ⟨43286358970705769518915081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57715145294274359358553441 43286358970705769518915081)
        ·
          refine ⟨32464769228029327139186311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43286358970705769518915081 32464769228029327139186311)
          ·
            refine ⟨48697153842043990708779467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32464769228029327139186311 48697153842043990708779467)
            ·
              refine ⟨73045730763065986063169201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48697153842043990708779467 73045730763065986063169201)
              ·
                refine ⟨54784298072299489547376901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73045730763065986063169201 54784298072299489547376901)
                ·
                  refine ⟨10272055888556154290133169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54784298072299489547376901 10272055888556154290133169)
                  ·
                    refine ⟨7704041916417115717599877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10272055888556154290133169 7704041916417115717599877)
                    ·
                      refine ⟨1444507859328209197049977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7704041916417115717599877 1444507859328209197049977)
                      ·
                        rfl

theorem cell23_2813169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2813169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813169 prefixEnd_2813169 := by exact prefixLift 2813169
  have htrace : WordTrace (prefixWord ++ tailWord_2813169) baseStart_2813169 baseEnd_2813169 := by
    simpa [prefixWord, tailWord_2813169, baseEnd_2813169] using wordTrace_append hprefix tailTrace_2813169
  have hstable : (prefixWord ++ tailWord_2813169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813169).length < 2 ^ (prefixWord ++ tailWord_2813169).sum := by decide
  have hdescent : baseEnd_2813169 < baseStart_2813169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813289 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2813289 : Nat := 118140960795 + 2813289 * 2 ^ 59
def prefixEnd_2813289 : Nat := 4983230072969 + 3 ^ 40 * 2813289 * 2
def baseEnd_2813289 : Nat := 1444569477006748727549425

theorem tailTrace_2813289 : CollatzResearch.WordTrace tailWord_2813289 prefixEnd_2813289 1444569477006748727549425 := by
  unfold tailWord_2813289
  simp only [CollatzResearch.WordTrace]
  refine ⟨102609079504941899354018921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68406053003294599569345947 102609079504941899354018921)
  ·
    refine ⟨76956809628706424515514191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102609079504941899354018921 76956809628706424515514191)
    ·
      refine ⟨115435214443059636773271287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76956809628706424515514191 115435214443059636773271287)
      ·
        refine ⟨173152821664589455159906931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115435214443059636773271287 173152821664589455159906931)
        ·
          refine ⟨259729232496884182739860397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173152821664589455159906931 259729232496884182739860397)
          ·
            refine ⟨97398462186331568527447649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259729232496884182739860397 97398462186331568527447649)
            ·
              refine ⟨73048846639748676395585737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97398462186331568527447649 73048846639748676395585737)
              ·
                refine ⟨54786634979811507296689303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73048846639748676395585737 54786634979811507296689303)
                ·
                  refine ⟨82179952469717260945033955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54786634979811507296689303 82179952469717260945033955)
                  ·
                    refine ⟨123269928704575891417550933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82179952469717260945033955 123269928704575891417550933)
                    ·
                      refine ⟨1444569477006748727549425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123269928704575891417550933 1444569477006748727549425)
                      ·
                        rfl

theorem cell23_2813289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2813289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813289 prefixEnd_2813289 := by exact prefixLift 2813289
  have htrace : WordTrace (prefixWord ++ tailWord_2813289) baseStart_2813289 baseEnd_2813289 := by
    simpa [prefixWord, tailWord_2813289, baseEnd_2813289] using wordTrace_append hprefix tailTrace_2813289
  have hstable : (prefixWord ++ tailWord_2813289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813289).length < 2 ^ (prefixWord ++ tailWord_2813289).sum := by decide
  have hdescent : baseEnd_2813289 < baseStart_2813289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813320 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 6]
def baseStart_2813320 : Nat := 118140960795 + 2813320 * 2 ^ 59
def prefixEnd_2813320 : Nat := 4983230072969 + 3 ^ 40 * 2813320 * 2
def baseEnd_2813320 : Nat := 160509488323004234029087

theorem tailTrace_2813320 : CollatzResearch.WordTrace tailWord_2813320 prefixEnd_2813320 160509488323004234029087 := by
  unfold tailWord_2813320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51305105083914795824198707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68406806778553061098931609 51305105083914795824198707)
  ·
    refine ⟨76957657625872193736298061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51305105083914795824198707 76957657625872193736298061)
    ·
      refine ⟨28859121609702072651111773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76957657625872193736298061 28859121609702072651111773)
      ·
        refine ⟨10822170603638277244166915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28859121609702072651111773 10822170603638277244166915)
        ·
          refine ⟨16233255905457415866250373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822170603638277244166915 16233255905457415866250373)
          ·
            refine ⟨3043735482273265474921945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16233255905457415866250373 3043735482273265474921945)
            ·
              refine ⟨2282801611704949106191459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043735482273265474921945 2282801611704949106191459)
              ·
                refine ⟨3424202417557423659287189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282801611704949106191459 3424202417557423659287189)
                ·
                  refine ⟨160509488323004234029087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3424202417557423659287189 160509488323004234029087)
                  ·
                    rfl

theorem cell23_2813320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 6].length) (baseStart_2813320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813320 prefixEnd_2813320 := by exact prefixLift 2813320
  have htrace : WordTrace (prefixWord ++ tailWord_2813320) baseStart_2813320 baseEnd_2813320 := by
    simpa [prefixWord, tailWord_2813320, baseEnd_2813320] using wordTrace_append hprefix tailTrace_2813320
  have hstable : (prefixWord ++ tailWord_2813320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813320).length < 2 ^ (prefixWord ++ tailWord_2813320).sum := by decide
  have hdescent : baseEnd_2813320 < baseStart_2813320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813323 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 4, 3, 2]
def baseStart_2813323 : Nat := 118140960795 + 2813323 * 2 ^ 59
def prefixEnd_2813323 : Nat := 4983230072969 + 3 ^ 40 * 2813323 * 2
def baseEnd_2813323 : Nat := 1444586935349001594524269

theorem tailTrace_2813323 : CollatzResearch.WordTrace tailWord_2813323 prefixEnd_2813323 1444586935349001594524269 := by
  unfold tailWord_2813323
  simp only [CollatzResearch.WordTrace]
  refine ⟨102610319586818723160756623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68406879724545815440504415 102610319586818723160756623)
  ·
    refine ⟨153915479380228084741134935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102610319586818723160756623 153915479380228084741134935)
    ·
      refine ⟨230873219070342127111702403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153915479380228084741134935 230873219070342127111702403)
      ·
        refine ⟨346309828605513190667553605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230873219070342127111702403 346309828605513190667553605)
        ·
          refine ⟨64933092863533723250166301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346309828605513190667553605 64933092863533723250166301)
          ·
            refine ⟨24349909823825146218812363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64933092863533723250166301 24349909823825146218812363)
            ·
              refine ⟨36524864735737719328218545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24349909823825146218812363 36524864735737719328218545)
              ·
                refine ⟨27393648551803289496163909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36524864735737719328218545 27393648551803289496163909)
                ·
                  refine ⟨5136309103463116780530733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27393648551803289496163909 5136309103463116780530733)
                  ·
                    refine ⟨1926115913798668792699025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5136309103463116780530733 1926115913798668792699025)
                    ·
                      refine ⟨1444586935349001594524269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926115913798668792699025 1444586935349001594524269)
                      ·
                        rfl

theorem cell23_2813323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 3, 2].length) (baseStart_2813323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813323 prefixEnd_2813323 := by exact prefixLift 2813323
  have htrace : WordTrace (prefixWord ++ tailWord_2813323) baseStart_2813323 baseEnd_2813323 := by
    simpa [prefixWord, tailWord_2813323, baseEnd_2813323] using wordTrace_append hprefix tailTrace_2813323
  have hstable : (prefixWord ++ tailWord_2813323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813323).length < 2 ^ (prefixWord ++ tailWord_2813323).sum := by decide
  have hdescent : baseEnd_2813323 < baseStart_2813323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813333 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2813333 : Nat := 118140960795 + 2813333 * 2 ^ 59
def prefixEnd_2813333 : Nat := 4983230072969 + 3 ^ 40 * 2813333 * 2
def baseEnd_2813333 : Nat := 481530690051848851799741

theorem tailTrace_2813333 : CollatzResearch.WordTrace tailWord_2813333 prefixEnd_2813333 481530690051848851799741 := by
  unfold tailWord_2813333
  simp only [CollatzResearch.WordTrace]
  refine ⟨102610684316782494868620653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68407122877854996579080435 102610684316782494868620653)
  ·
    refine ⟨38479006618793435575732745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102610684316782494868620653 38479006618793435575732745)
    ·
      refine ⟨28859254964095076681799559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38479006618793435575732745 28859254964095076681799559)
      ·
        refine ⟨43288882446142615022699339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28859254964095076681799559 43288882446142615022699339)
        ·
          refine ⟨64933323669213922534049009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43288882446142615022699339 64933323669213922534049009)
          ·
            refine ⟨48699992751910441900536757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64933323669213922534049009 48699992751910441900536757)
            ·
              refine ⟨4565624320491603928175321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48699992751910441900536757 4565624320491603928175321)
              ·
                refine ⟨3424218240368702946131491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565624320491603928175321 3424218240368702946131491)
                ·
                  refine ⟨5136327360553054419197237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424218240368702946131491 5136327360553054419197237)
                  ·
                    refine ⟨481530690051848851799741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5136327360553054419197237 481530690051848851799741)
                    ·
                      rfl

theorem cell23_2813333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2813333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813333 prefixEnd_2813333 := by exact prefixLift 2813333
  have htrace : WordTrace (prefixWord ++ tailWord_2813333) baseStart_2813333 baseEnd_2813333 := by
    simpa [prefixWord, tailWord_2813333, baseEnd_2813333] using wordTrace_append hprefix tailTrace_2813333
  have hstable : (prefixWord ++ tailWord_2813333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813333).length < 2 ^ (prefixWord ++ tailWord_2813333).sum := by decide
  have hdescent : baseEnd_2813333 < baseStart_2813333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813357 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2813357 : Nat := 118140960795 + 2813357 * 2 ^ 59
def prefixEnd_2813357 : Nat := 4983230072969 + 3 ^ 40 * 2813357 * 2
def baseEnd_2813357 : Nat := 1444604393691254461499113

theorem tailTrace_2813357 : CollatzResearch.WordTrace tailWord_2813357 prefixEnd_2813357 1444604393691254461499113 := by
  unfold tailWord_2813357
  simp only [CollatzResearch.WordTrace]
  refine ⟨102611559668695546967494325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68407706445797031311662883 102611559668695546967494325)
  ·
    refine ⟨9619833718940207528202593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102611559668695546967494325 9619833718940207528202593)
    ·
      refine ⟨7214875289205155646151945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9619833718940207528202593 7214875289205155646151945)
      ·
        refine ⟨5411156466903866734613959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7214875289205155646151945 5411156466903866734613959)
        ·
          refine ⟨8116734700355800101920939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411156466903866734613959 8116734700355800101920939)
          ·
            refine ⟨12175102050533700152881409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116734700355800101920939 12175102050533700152881409)
            ·
              refine ⟨9131326537900275114661057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175102050533700152881409 9131326537900275114661057)
              ·
                refine ⟨6848494903425206335995793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9131326537900275114661057 6848494903425206335995793)
                ·
                  refine ⟨5136371177568904751996845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6848494903425206335995793 5136371177568904751996845)
                  ·
                    refine ⟨1926139191588339281998817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5136371177568904751996845 1926139191588339281998817)
                    ·
                      refine ⟨1444604393691254461499113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926139191588339281998817 1444604393691254461499113)
                      ·
                        rfl

theorem cell23_2813357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2813357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813357 prefixEnd_2813357 := by exact prefixLift 2813357
  have htrace : WordTrace (prefixWord ++ tailWord_2813357) baseStart_2813357 baseEnd_2813357 := by
    simpa [prefixWord, tailWord_2813357, baseEnd_2813357] using wordTrace_append hprefix tailTrace_2813357
  have hstable : (prefixWord ++ tailWord_2813357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813357).length < 2 ^ (prefixWord ++ tailWord_2813357).sum := by decide
  have hdescent : baseEnd_2813357 < baseStart_2813357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813373 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2813373 : Nat := 118140960795 + 2813373 * 2 ^ 59
def prefixEnd_2813373 : Nat := 4983230072969 + 3 ^ 40 * 2813373 * 2
def baseEnd_2813373 : Nat := 1444612609381726398899039

theorem tailTrace_2813373 : CollatzResearch.WordTrace tailWord_2813373 prefixEnd_2813373 1444612609381726398899039 := by
  unfold tailWord_2813373
  simp only [CollatzResearch.WordTrace]
  refine ⟨102612143236637581700076773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68408095491091721133384515 102612143236637581700076773)
  ·
    refine ⟨19239776856869546568764395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102612143236637581700076773 19239776856869546568764395)
    ·
      refine ⟨28859665285304319853146593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19239776856869546568764395 28859665285304319853146593)
      ·
        refine ⟨21644748963978239889859945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28859665285304319853146593 21644748963978239889859945)
        ·
          refine ⟨16233561722983679917394959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21644748963978239889859945 16233561722983679917394959)
          ·
            refine ⟨24350342584475519876092439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16233561722983679917394959 24350342584475519876092439)
            ·
              refine ⟨36525513876713279814138659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24350342584475519876092439 36525513876713279814138659)
              ·
                refine ⟨54788270815069919721207989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36525513876713279814138659 54788270815069919721207989)
                ·
                  refine ⟨5136400388912804973863249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54788270815069919721207989 5136400388912804973863249)
                  ·
                    refine ⟨3852300291684603730397437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5136400388912804973863249 3852300291684603730397437)
                    ·
                      refine ⟨1444612609381726398899039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852300291684603730397437 1444612609381726398899039)
                      ·
                        rfl

theorem cell23_2813373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2813373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813373 prefixEnd_2813373 := by exact prefixLift 2813373
  have htrace : WordTrace (prefixWord ++ tailWord_2813373) baseStart_2813373 baseEnd_2813373 := by
    simpa [prefixWord, tailWord_2813373, baseEnd_2813373] using wordTrace_append hprefix tailTrace_2813373
  have hstable : (prefixWord ++ tailWord_2813373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813373).length < 2 ^ (prefixWord ++ tailWord_2813373).sum := by decide
  have hdescent : baseEnd_2813373 < baseStart_2813373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813376 : List Nat := [2, 1, 1, 2, 3, 1, 5, 8]
def baseStart_2813376 : Nat := 118140960795 + 2813376 * 2 ^ 59
def prefixEnd_2813376 : Nat := 4983230072969 + 3 ^ 40 * 2813376 * 2
def baseEnd_2813376 : Nat := 53504227771247773598575

theorem tailTrace_2813376 : CollatzResearch.WordTrace tailWord_2813376 prefixEnd_2813376 53504227771247773598575 := by
  unfold tailWord_2813376
  simp only [CollatzResearch.WordTrace]
  refine ⟨51306126327813356606217991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68408168437084475474957321 51306126327813356606217991)
  ·
    refine ⟨76959189491720034909326987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51306126327813356606217991 76959189491720034909326987)
    ·
      refine ⟨115438784237580052363990481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76959189491720034909326987 115438784237580052363990481)
      ·
        refine ⟨86579088178185039272992861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115438784237580052363990481 86579088178185039272992861)
        ·
          refine ⟨32467158066819389727372323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86579088178185039272992861 32467158066819389727372323)
          ·
            refine ⟨48700737100229084591058485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32467158066819389727372323 48700737100229084591058485)
            ·
              refine ⟨4565694103146476680411733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48700737100229084591058485 4565694103146476680411733)
              ·
                refine ⟨53504227771247773598575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4565694103146476680411733 53504227771247773598575)
                ·
                  rfl

theorem cell23_2813376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 8].length) (baseStart_2813376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813376 prefixEnd_2813376 := by exact prefixLift 2813376
  have htrace : WordTrace (prefixWord ++ tailWord_2813376) baseStart_2813376 baseEnd_2813376 := by
    simpa [prefixWord, tailWord_2813376, baseEnd_2813376] using wordTrace_append hprefix tailTrace_2813376
  have hstable : (prefixWord ++ tailWord_2813376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813376).length < 2 ^ (prefixWord ++ tailWord_2813376).sum := by decide
  have hdescent : baseEnd_2813376 < baseStart_2813376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813380 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2813380 : Nat := 118140960795 + 2813380 * 2 ^ 59
def prefixEnd_2813380 : Nat := 4983230072969 + 3 ^ 40 * 2813380 * 2
def baseEnd_2813380 : Nat := 481538734582102623837169

theorem tailTrace_2813380 : CollatzResearch.WordTrace tailWord_2813380 prefixEnd_2813380 481538734582102623837169 := by
  unfold tailWord_2813380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51306199273806110947790797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68408265698408147930387729 51306199273806110947790797)
  ·
    refine ⟨19239824727677291605421549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51306199273806110947790797 19239824727677291605421549)
    ·
      refine ⟨7214934272878984352033081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19239824727677291605421549 7214934272878984352033081)
      ·
        refine ⟨5411200704659238264024811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7214934272878984352033081 5411200704659238264024811)
        ·
          refine ⟨8116801056988857396037217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411200704659238264024811 8116801056988857396037217)
          ·
            refine ⟨6087600792741643047027913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116801056988857396037217 6087600792741643047027913)
            ·
              refine ⟨4565700594556232285270935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087600792741643047027913 4565700594556232285270935)
              ·
                refine ⟨6848550891834348427906403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565700594556232285270935 6848550891834348427906403)
                ·
                  refine ⟨10272826337751522641859605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848550891834348427906403 10272826337751522641859605)
                  ·
                    refine ⟨481538734582102623837169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10272826337751522641859605 481538734582102623837169)
                    ·
                      rfl

theorem cell23_2813380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2813380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813380 prefixEnd_2813380 := by exact prefixLift 2813380
  have htrace : WordTrace (prefixWord ++ tailWord_2813380) baseStart_2813380 baseEnd_2813380 := by
    simpa [prefixWord, tailWord_2813380, baseEnd_2813380] using wordTrace_append hprefix tailTrace_2813380
  have hstable : (prefixWord ++ tailWord_2813380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813380).length < 2 ^ (prefixWord ++ tailWord_2813380).sum := by decide
  have hdescent : baseEnd_2813380 < baseStart_2813380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813383 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_2813383 : Nat := 118140960795 + 2813383 * 2 ^ 59
def prefixEnd_2813383 : Nat := 4983230072969 + 3 ^ 40 * 2813383 * 2
def baseEnd_2813383 : Nat := 1444617744188271359773993

theorem tailTrace_2813383 : CollatzResearch.WordTrace tailWord_2813383 prefixEnd_2813383 1444617744188271359773993 := by
  unfold tailWord_2813383
  simp only [CollatzResearch.WordTrace]
  refine ⟨102612507966601353407940803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68408338644400902271960535 102612507966601353407940803)
  ·
    refine ⟨153918761949902030111911205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102612507966601353407940803 153918761949902030111911205)
    ·
      refine ⟨28859767865606630645983351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153918761949902030111911205 28859767865606630645983351)
      ·
        refine ⟨43289651798409945968975027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28859767865606630645983351 43289651798409945968975027)
        ·
          refine ⟨64934477697614918953462541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43289651798409945968975027 64934477697614918953462541)
          ·
            refine ⟨24350429136605594607548453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64934477697614918953462541 24350429136605594607548453)
            ·
              refine ⟨4565705463113548988915335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24350429136605594607548453 4565705463113548988915335)
              ·
                refine ⟨6848558194670323483373003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565705463113548988915335 6848558194670323483373003)
                ·
                  refine ⟨10272837292005485225059505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848558194670323483373003 10272837292005485225059505)
                  ·
                    refine ⟨7704627969004113918794629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10272837292005485225059505 7704627969004113918794629)
                    ·
                      refine ⟨1444617744188271359773993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7704627969004113918794629 1444617744188271359773993)
                      ·
                        rfl

theorem cell23_2813383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_2813383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813383 prefixEnd_2813383 := by exact prefixLift 2813383
  have htrace : WordTrace (prefixWord ++ tailWord_2813383) baseStart_2813383 baseEnd_2813383 := by
    simpa [prefixWord, tailWord_2813383, baseEnd_2813383] using wordTrace_append hprefix tailTrace_2813383
  have hstable : (prefixWord ++ tailWord_2813383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813383).length < 2 ^ (prefixWord ++ tailWord_2813383).sum := by decide
  have hdescent : baseEnd_2813383 < baseStart_2813383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813403 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 3]
def baseStart_2813403 : Nat := 118140960795 + 2813403 * 2 ^ 59
def prefixEnd_2813403 : Nat := 4983230072969 + 3 ^ 40 * 2813403 * 2
def baseEnd_2813403 : Nat := 1444628013801361281523901

theorem tailTrace_2813403 : CollatzResearch.WordTrace tailWord_2813403 prefixEnd_2813403 1444628013801361281523901 := by
  unfold tailWord_2813403
  simp only [CollatzResearch.WordTrace]
  refine ⟨102613237426528896823668863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68408824951019264549112575 102613237426528896823668863)
  ·
    refine ⟨153919856139793345235503295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102613237426528896823668863 153919856139793345235503295)
    ·
      refine ⟨230879784209690017853254943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153919856139793345235503295 230879784209690017853254943)
      ·
        refine ⟨346319676314535026779882415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230879784209690017853254943 346319676314535026779882415)
        ·
          refine ⟨519479514471802540169823623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346319676314535026779882415 519479514471802540169823623)
          ·
            refine ⟨779219271707703810254735435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519479514471802540169823623 779219271707703810254735435)
            ·
              refine ⟨1168828907561555715382103153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779219271707703810254735435 1168828907561555715382103153)
              ·
                refine ⟨876621680671166786536577365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168828907561555715382103153 876621680671166786536577365)
                ·
                  refine ⟨2568227580091308944931379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 876621680671166786536577365 2568227580091308944931379)
                  ·
                    refine ⟨3852341370136963417397069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568227580091308944931379 3852341370136963417397069)
                    ·
                      refine ⟨1444628013801361281523901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852341370136963417397069 1444628013801361281523901)
                      ·
                        rfl

theorem cell23_2813403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 1, 3].length) (baseStart_2813403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813403 prefixEnd_2813403 := by exact prefixLift 2813403
  have htrace : WordTrace (prefixWord ++ tailWord_2813403) baseStart_2813403 baseEnd_2813403 := by
    simpa [prefixWord, tailWord_2813403, baseEnd_2813403] using wordTrace_append hprefix tailTrace_2813403
  have hstable : (prefixWord ++ tailWord_2813403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813403).length < 2 ^ (prefixWord ++ tailWord_2813403).sum := by decide
  have hdescent : baseEnd_2813403 < baseStart_2813403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813420 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_2813420 : Nat := 118140960795 + 2813420 * 2 ^ 59
def prefixEnd_2813420 : Nat := 4983230072969 + 3 ^ 40 * 2813420 * 2
def baseEnd_2813420 : Nat := 1444636742972487715011323

theorem tailTrace_2813420 : CollatzResearch.WordTrace tailWord_2813420 prefixEnd_2813420 1444636742972487715011323 := by
  unfold tailWord_2813420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51306928733733654363518857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68409238311644872484691809 51306928733733654363518857)
  ·
    refine ⟨38480196550300240772639143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51306928733733654363518857 38480196550300240772639143)
    ·
      refine ⟨57720294825450361158958715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38480196550300240772639143 57720294825450361158958715)
      ·
        refine ⟨86580442238175541738438073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57720294825450361158958715 86580442238175541738438073)
        ·
          refine ⟨64935331678631656303828555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86580442238175541738438073 64935331678631656303828555)
          ·
            refine ⟨97402997517947484455742833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64935331678631656303828555 97402997517947484455742833)
            ·
              refine ⟨73052248138460613341807125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97402997517947484455742833 73052248138460613341807125)
              ·
                refine ⟨3424324131490341250397209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73052248138460613341807125 3424324131490341250397209)
                ·
                  refine ⟨2568243098617755937797907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424324131490341250397209 2568243098617755937797907)
                  ·
                    refine ⟨3852364647926633906696861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568243098617755937797907 3852364647926633906696861)
                    ·
                      refine ⟨1444636742972487715011323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852364647926633906696861 1444636742972487715011323)
                      ·
                        rfl

theorem cell23_2813420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_2813420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813420 prefixEnd_2813420 := by exact prefixLift 2813420
  have htrace : WordTrace (prefixWord ++ tailWord_2813420) baseStart_2813420 baseEnd_2813420 := by
    simpa [prefixWord, tailWord_2813420, baseEnd_2813420] using wordTrace_append hprefix tailTrace_2813420
  have hstable : (prefixWord ++ tailWord_2813420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813420).length < 2 ^ (prefixWord ++ tailWord_2813420).sum := by decide
  have hdescent : baseEnd_2813420 < baseStart_2813420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813447 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2813447 : Nat := 118140960795 + 2813447 * 2 ^ 59
def prefixEnd_2813447 : Nat := 4983230072969 + 3 ^ 40 * 2813447 * 2
def baseEnd_2813447 : Nat := 1444650606950159109373699

theorem tailTrace_2813447 : CollatzResearch.WordTrace tailWord_2813447 prefixEnd_2813447 1444650606950159109373699 := by
  unfold tailWord_2813447
  simp only [CollatzResearch.WordTrace]
  refine ⟨102614842238369492338270595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68409894825579661558847063 102614842238369492338270595)
  ·
    refine ⟨153922263357554238507405893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102614842238369492338270595 153922263357554238507405893)
    ·
      refine ⟨28860424379541419720138605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153922263357554238507405893 28860424379541419720138605)
      ·
        refine ⟨10822659142328032395051977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28860424379541419720138605 10822659142328032395051977)
        ·
          refine ⟨8116994356746024296288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10822659142328032395051977 8116994356746024296288983)
          ·
            refine ⟨12175491535119036444433475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116994356746024296288983 12175491535119036444433475)
            ·
              refine ⟨18263237302678554666650213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12175491535119036444433475 18263237302678554666650213)
              ·
                refine ⟨3424356994252228999996915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18263237302678554666650213 3424356994252228999996915)
                ·
                  refine ⟨5136535491378343499995373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424356994252228999996915 5136535491378343499995373)
                  ·
                    refine ⟨1926200809266878812498265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5136535491378343499995373 1926200809266878812498265)
                    ·
                      refine ⟨1444650606950159109373699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926200809266878812498265 1444650606950159109373699)
                      ·
                        rfl

theorem cell23_2813447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2813447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813447 prefixEnd_2813447 := by exact prefixLift 2813447
  have htrace : WordTrace (prefixWord ++ tailWord_2813447) baseStart_2813447 baseEnd_2813447 := by
    simpa [prefixWord, tailWord_2813447, baseEnd_2813447] using wordTrace_append hprefix tailTrace_2813447
  have hstable : (prefixWord ++ tailWord_2813447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813447).length < 2 ^ (prefixWord ++ tailWord_2813447).sum := by decide
  have hdescent : baseEnd_2813447 < baseStart_2813447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813477 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 2, 2, 2]
def baseStart_2813477 : Nat := 118140960795 + 2813477 * 2 ^ 59
def prefixEnd_2813477 : Nat := 4983230072969 + 3 ^ 40 * 2813477 * 2
def baseEnd_2813477 : Nat := 1444666011369793991998561

theorem tailTrace_2813477 : CollatzResearch.WordTrace tailWord_2813477 prefixEnd_2813477 1444666011369793991998561 := by
  unfold tailWord_2813477
  simp only [CollatzResearch.WordTrace]
  refine ⟨102615936428260807461862685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68410624285507204974575123 102615936428260807461862685)
  ·
    refine ⟨38480976160597802798198507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102615936428260807461862685 38480976160597802798198507)
    ·
      refine ⟨57721464240896704197297761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38480976160597802798198507 57721464240896704197297761)
      ·
        refine ⟨43291098180672528147973321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57721464240896704197297761 43291098180672528147973321)
        ·
          refine ⟨32468323635504396110979991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43291098180672528147973321 32468323635504396110979991)
          ·
            refine ⟨48702485453256594166469987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32468323635504396110979991 48702485453256594166469987)
            ·
              refine ⟨73053728179884891249704981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48702485453256594166469987 73053728179884891249704981)
              ·
                refine ⟨3424393508432104277329921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73053728179884891249704981 3424393508432104277329921)
                ·
                  refine ⟨2568295131324078207997441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424393508432104277329921 2568295131324078207997441)
                  ·
                    refine ⟨1926221348493058655998081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568295131324078207997441 1926221348493058655998081)
                    ·
                      refine ⟨1444666011369793991998561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926221348493058655998081 1444666011369793991998561)
                      ·
                        rfl

theorem cell23_2813477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_2813477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813477 prefixEnd_2813477 := by exact prefixLift 2813477
  have htrace : WordTrace (prefixWord ++ tailWord_2813477) baseStart_2813477 baseEnd_2813477 := by
    simpa [prefixWord, tailWord_2813477, baseEnd_2813477] using wordTrace_append hprefix tailTrace_2813477
  have hstable : (prefixWord ++ tailWord_2813477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813477).length < 2 ^ (prefixWord ++ tailWord_2813477).sum := by decide
  have hdescent : baseEnd_2813477 < baseStart_2813477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813573 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 8]
def baseStart_2813573 : Nat := 118140960795 + 2813573 * 2 ^ 59
def prefixEnd_2813573 : Nat := 4983230072969 + 3 ^ 40 * 2813573 * 2
def baseEnd_2813573 : Nat := 160523922834736179599791

theorem tailTrace_2813573 : CollatzResearch.WordTrace tailWord_2813573 prefixEnd_2813573 160523922834736179599791 := by
  unfold tailWord_2813573
  simp only [CollatzResearch.WordTrace]
  refine ⟨102619437835913015857357373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68412958557275343904904915 102619437835913015857357373)
  ·
    refine ⟨38482289188467380946509015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102619437835913015857357373 38482289188467380946509015)
    ·
      refine ⟨57723433782701071419763523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38482289188467380946509015 57723433782701071419763523)
      ·
        refine ⟨86585150674051607129645285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57723433782701071419763523 86585150674051607129645285)
        ·
          refine ⟨16234715751384676336808491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86585150674051607129645285 16234715751384676336808491)
          ·
            refine ⟨24352073627077014505212737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16234715751384676336808491 24352073627077014505212737)
            ·
              refine ⟨18264055220307760878909553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24352073627077014505212737 18264055220307760878909553)
              ·
                refine ⟨13698041415230820659182165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18264055220307760878909553 13698041415230820659182165)
                ·
                  refine ⟨160523922834736179599791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13698041415230820659182165 160523922834736179599791)
                  ·
                    rfl

theorem cell23_2813573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_2813573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813573 prefixEnd_2813573 := by exact prefixLift 2813573
  have htrace : WordTrace (prefixWord ++ tailWord_2813573) baseStart_2813573 baseEnd_2813573 := by
    simpa [prefixWord, tailWord_2813573, baseEnd_2813573] using wordTrace_append hprefix tailTrace_2813573
  have hstable : (prefixWord ++ tailWord_2813573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813573).length < 2 ^ (prefixWord ++ tailWord_2813573).sum := by decide
  have hdescent : baseEnd_2813573 < baseStart_2813573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813577 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 1, 4]
def baseStart_2813577 : Nat := 118140960795 + 2813577 * 2 ^ 59
def prefixEnd_2813577 : Nat := 4983230072969 + 3 ^ 40 * 2813577 * 2
def baseEnd_2813577 : Nat := 481572453145081200249367

theorem tailTrace_2813577 : CollatzResearch.WordTrace tailWord_2813577 prefixEnd_2813577 481572453145081200249367 := by
  unfold tailWord_2813577
  simp only [CollatzResearch.WordTrace]
  refine ⟨102619583727898524540502985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68413055818599016360335323 102619583727898524540502985)
  ·
    refine ⟨76964687795923893405377239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102619583727898524540502985 76964687795923893405377239)
    ·
      refine ⟨115447031693885840108065859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76964687795923893405377239 115447031693885840108065859)
      ·
        refine ⟨173170547540828760162098789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115447031693885840108065859 173170547540828760162098789)
        ·
          refine ⟨32469477663905392530393523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173170547540828760162098789 32469477663905392530393523)
          ·
            refine ⟨48704216495858088795590285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32469477663905392530393523 48704216495858088795590285)
            ·
              refine ⟨18264081185946783298346357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48704216495858088795590285 18264081185946783298346357)
              ·
                refine ⟨1712257611182510934219971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18264081185946783298346357 1712257611182510934219971)
                ·
                  refine ⟨2568386416773766401329957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712257611182510934219971 2568386416773766401329957)
                  ·
                    refine ⟨481572453145081200249367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568386416773766401329957 481572453145081200249367)
                    ·
                      rfl

theorem cell23_2813577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 4].length) (baseStart_2813577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813577 prefixEnd_2813577 := by exact prefixLift 2813577
  have htrace : WordTrace (prefixWord ++ tailWord_2813577) baseStart_2813577 baseEnd_2813577 := by
    simpa [prefixWord, tailWord_2813577, baseEnd_2813577] using wordTrace_append hprefix tailTrace_2813577
  have hstable : (prefixWord ++ tailWord_2813577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813577).length < 2 ^ (prefixWord ++ tailWord_2813577).sum := by decide
  have hdescent : baseEnd_2813577 < baseStart_2813577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813671 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2813671 : Nat := 118140960795 + 2813671 * 2 ^ 59
def prefixEnd_2813671 : Nat := 4983230072969 + 3 ^ 40 * 2813671 * 2
def baseEnd_2813671 : Nat := 481588542205588744324223

theorem tailTrace_2813671 : CollatzResearch.WordTrace tailWord_2813671 prefixEnd_2813671 481588542205588744324223 := by
  unfold tailWord_2813671
  simp only [CollatzResearch.WordTrace]
  refine ⟨102623012189557978594424867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68415341459705319062949911 102623012189557978594424867)
  ·
    refine ⟨153934518284336967891637301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102623012189557978594424867 153934518284336967891637301)
    ·
      refine ⟨14431361089156590739840997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153934518284336967891637301 14431361089156590739840997)
      ·
        refine ⟨2705880204216860763720187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14431361089156590739840997 2705880204216860763720187)
        ·
          refine ⟨4058820306325291145580281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705880204216860763720187 4058820306325291145580281)
          ·
            refine ⟨3044115229743968359185211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4058820306325291145580281 3044115229743968359185211)
            ·
              refine ⟨4566172844615952538777817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044115229743968359185211 4566172844615952538777817)
              ·
                refine ⟨3424629633461964404083363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566172844615952538777817 3424629633461964404083363)
                ·
                  refine ⟨5136944450192946606125045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424629633461964404083363 5136944450192946606125045)
                  ·
                    refine ⟨481588542205588744324223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5136944450192946606125045 481588542205588744324223)
                    ·
                      rfl

theorem cell23_2813671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2813671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813671 prefixEnd_2813671 := by exact prefixLift 2813671
  have htrace : WordTrace (prefixWord ++ tailWord_2813671) baseStart_2813671 baseEnd_2813671 := by
    simpa [prefixWord, tailWord_2813671, baseEnd_2813671] using wordTrace_append hprefix tailTrace_2813671
  have hstable : (prefixWord ++ tailWord_2813671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813671).length < 2 ^ (prefixWord ++ tailWord_2813671).sum := by decide
  have hdescent : baseEnd_2813671 < baseStart_2813671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813674 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_2813674 : Nat := 118140960795 + 2813674 * 2 ^ 59
def prefixEnd_2813674 : Nat := 4983230072969 + 3 ^ 40 * 2813674 * 2
def baseEnd_2813674 : Nat := 1444767167058729721235155

theorem tailTrace_2813674 : CollatzResearch.WordTrace tailWord_2813674 prefixEnd_2813674 1444767167058729721235155 := by
  unfold tailWord_2813674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25655780402136777526696019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68415414405698073404522717 25655780402136777526696019)
  ·
    refine ⟨38483670603205166290044029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25655780402136777526696019 38483670603205166290044029)
    ·
      refine ⟨14431376476201937358766511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38483670603205166290044029 14431376476201937358766511)
      ·
        refine ⟨21647064714302906038149767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14431376476201937358766511 21647064714302906038149767)
        ·
          refine ⟨32470597071454359057224651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21647064714302906038149767 32470597071454359057224651)
          ·
            refine ⟨48705895607181538585836977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32470597071454359057224651 48705895607181538585836977)
            ·
              refine ⟨36529421705386153939377733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48705895607181538585836977 36529421705386153939377733)
              ·
                refine ⟨6849266569759903863633325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36529421705386153939377733 6849266569759903863633325)
                ·
                  refine ⟨2568474963659963948862497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6849266569759903863633325 2568474963659963948862497)
                  ·
                    refine ⟨1926356222744972961646873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568474963659963948862497 1926356222744972961646873)
                    ·
                      refine ⟨1444767167058729721235155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926356222744972961646873 1444767167058729721235155)
                      ·
                        rfl

theorem cell23_2813674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_2813674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813674 prefixEnd_2813674 := by exact prefixLift 2813674
  have htrace : WordTrace (prefixWord ++ tailWord_2813674) baseStart_2813674 baseEnd_2813674 := by
    simpa [prefixWord, tailWord_2813674, baseEnd_2813674] using wordTrace_append hprefix tailTrace_2813674
  have hstable : (prefixWord ++ tailWord_2813674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813674).length < 2 ^ (prefixWord ++ tailWord_2813674).sum := by decide
  have hdescent : baseEnd_2813674 < baseStart_2813674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813684 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2813684 : Nat := 118140960795 + 2813684 * 2 ^ 59
def prefixEnd_2813684 : Nat := 4983230072969 + 3 ^ 40 * 2813684 * 2
def baseEnd_2813684 : Nat := 481590767288424894036703

theorem tailTrace_2813684 : CollatzResearch.WordTrace tailWord_2813684 prefixEnd_2813684 481590767288424894036703 := by
  unfold tailWord_2813684
  simp only [CollatzResearch.WordTrace]
  refine ⟨51311743169255440907324053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68415657559007254543098737 51311743169255440907324053)
  ·
    refine ⟨2405237961058848792530815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51311743169255440907324053 2405237961058848792530815)
    ·
      refine ⟨3607856941588273188796223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405237961058848792530815 3607856941588273188796223)
      ·
        refine ⟨5411785412382409783194335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607856941588273188796223 5411785412382409783194335)
        ·
          refine ⟨8117678118573614674791503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411785412382409783194335 8117678118573614674791503)
          ·
            refine ⟨12176517177860422012187255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117678118573614674791503 12176517177860422012187255)
            ·
              refine ⟨18264775766790633018280883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12176517177860422012187255 18264775766790633018280883)
              ·
                refine ⟨27397163650185949527421325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18264775766790633018280883 27397163650185949527421325)
                ·
                  refine ⟨10273936368819731072782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27397163650185949527421325 10273936368819731072782997)
                  ·
                    refine ⟨481590767288424894036703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10273936368819731072782997 481590767288424894036703)
                    ·
                      rfl

theorem cell23_2813684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2813684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813684 prefixEnd_2813684 := by exact prefixLift 2813684
  have htrace : WordTrace (prefixWord ++ tailWord_2813684) baseStart_2813684 baseEnd_2813684 := by
    simpa [prefixWord, tailWord_2813684, baseEnd_2813684] using wordTrace_append hprefix tailTrace_2813684
  have hstable : (prefixWord ++ tailWord_2813684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813684).length < 2 ^ (prefixWord ++ tailWord_2813684).sum := by decide
  have hdescent : baseEnd_2813684 < baseStart_2813684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813707 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 3]
def baseStart_2813707 : Nat := 118140960795 + 2813707 * 2 ^ 59
def prefixEnd_2813707 : Nat := 4983230072969 + 3 ^ 40 * 2813707 * 2
def baseEnd_2813707 : Nat := 1444784111920328092122503

theorem tailTrace_2813707 : CollatzResearch.WordTrace tailWord_2813707 prefixEnd_2813707 1444784111920328092122503 := by
  unfold tailWord_2813707
  simp only [CollatzResearch.WordTrace]
  refine ⟨102624325217427556742735375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68416216811618371161823583 102624325217427556742735375)
  ·
    refine ⟨153936487826141335114103063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102624325217427556742735375 153936487826141335114103063)
    ·
      refine ⟨230904731739212002671154595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153936487826141335114103063 230904731739212002671154595)
      ·
        refine ⟨346357097608818004006731893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230904731739212002671154595 346357097608818004006731893)
        ·
          refine ⟨32470977900826687875631115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346357097608818004006731893 32470977900826687875631115)
          ·
            refine ⟨48706466851240031813446673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32470977900826687875631115 48706466851240031813446673)
            ·
              refine ⟨36529850138430023860085005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48706466851240031813446673 36529850138430023860085005)
              ·
                refine ⟨13698693801911258947531877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36529850138430023860085005 13698693801911258947531877)
                ·
                  refine ⟨2568505087858361052662227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13698693801911258947531877 2568505087858361052662227)
                  ·
                    refine ⟨3852757631787541578993341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568505087858361052662227 3852757631787541578993341)
                    ·
                      refine ⟨1444784111920328092122503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852757631787541578993341 1444784111920328092122503)
                      ·
                        rfl

theorem cell23_2813707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 3].length) (baseStart_2813707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813707 prefixEnd_2813707 := by exact prefixLift 2813707
  have htrace : WordTrace (prefixWord ++ tailWord_2813707) baseStart_2813707 baseEnd_2813707 := by
    simpa [prefixWord, tailWord_2813707, baseEnd_2813707] using wordTrace_append hprefix tailTrace_2813707
  have hstable : (prefixWord ++ tailWord_2813707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813707).length < 2 ^ (prefixWord ++ tailWord_2813707).sum := by decide
  have hdescent : baseEnd_2813707 < baseStart_2813707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813708 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_2813708 : Nat := 118140960795 + 2813708 * 2 ^ 59
def prefixEnd_2813708 : Nat := 4983230072969 + 3 ^ 40 * 2813708 * 2
def baseEnd_2813708 : Nat := 1444784625400982588209999

theorem tailTrace_2813708 : CollatzResearch.WordTrace tailWord_2813708 prefixEnd_2813708 1444784625400982588209999 := by
  unfold tailWord_2813708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51312180845211966956760889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68416241126949289275681185 51312180845211966956760889)
  ·
    refine ⟨38484135633908975217570667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51312180845211966956760889 38484135633908975217570667)
    ·
      refine ⟨57726203450863462826356001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38484135633908975217570667 57726203450863462826356001)
      ·
        refine ⟨43294652588147597119767001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57726203450863462826356001 43294652588147597119767001)
        ·
          refine ⟨32470989441110697839825251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43294652588147597119767001 32470989441110697839825251)
          ·
            refine ⟨48706484161666046759737877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32470989441110697839825251 48706484161666046759737877)
            ·
              refine ⟨2283116445078095941862713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48706484161666046759737877 2283116445078095941862713)
              ·
                refine ⟨1712337333808571956397035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283116445078095941862713 1712337333808571956397035)
                ·
                  refine ⟨2568506000712857934595553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712337333808571956397035 2568506000712857934595553)
                  ·
                    refine ⟨1926379500534643450946665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568506000712857934595553 1926379500534643450946665)
                    ·
                      refine ⟨1444784625400982588209999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926379500534643450946665 1444784625400982588209999)
                      ·
                        rfl

theorem cell23_2813708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_2813708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813708 prefixEnd_2813708 := by exact prefixLift 2813708
  have htrace : WordTrace (prefixWord ++ tailWord_2813708) baseStart_2813708 baseEnd_2813708 := by
    simpa [prefixWord, tailWord_2813708, baseEnd_2813708] using wordTrace_append hprefix tailTrace_2813708
  have hstable : (prefixWord ++ tailWord_2813708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813708).length < 2 ^ (prefixWord ++ tailWord_2813708).sum := by decide
  have hdescent : baseEnd_2813708 < baseStart_2813708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813710 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2813710 : Nat := 118140960795 + 2813710 * 2 ^ 59
def prefixEnd_2813710 : Nat := 4983230072969 + 3 ^ 40 * 2813710 * 2
def baseEnd_2813710 : Nat := 481595217454097193461663

theorem tailTrace_2813710 : CollatzResearch.WordTrace tailWord_2813710 prefixEnd_2813710 481595217454097193461663 := by
  unfold tailWord_2813710
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828054329552086031886823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68416289757611125503396389 12828054329552086031886823)
  ·
    refine ⟨19242081494328129047830235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12828054329552086031886823 19242081494328129047830235)
    ·
      refine ⟨28863122241492193571745353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19242081494328129047830235 28863122241492193571745353)
      ·
        refine ⟨21647341681119145178809015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28863122241492193571745353 21647341681119145178809015)
        ·
          refine ⟨32471012521678717768213523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21647341681119145178809015 32471012521678717768213523)
          ·
            refine ⟨48706518782518076652320285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32471012521678717768213523 48706518782518076652320285)
            ·
              refine ⟨18264944543444278744620107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48706518782518076652320285 18264944543444278744620107)
              ·
                refine ⟨27397416815166418116930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18264944543444278744620107 27397416815166418116930161)
                ·
                  refine ⟨20548062611374813587697621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27397416815166418116930161 20548062611374813587697621)
                  ·
                    refine ⟨481595217454097193461663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20548062611374813587697621 481595217454097193461663)
                    ·
                      rfl

theorem cell23_2813710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2813710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813710 prefixEnd_2813710 := by exact prefixLift 2813710
  have htrace : WordTrace (prefixWord ++ tailWord_2813710) baseStart_2813710 baseEnd_2813710 := by
    simpa [prefixWord, tailWord_2813710, baseEnd_2813710] using wordTrace_append hprefix tailTrace_2813710
  have hstable : (prefixWord ++ tailWord_2813710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813710).length < 2 ^ (prefixWord ++ tailWord_2813710).sum := by decide
  have hdescent : baseEnd_2813710 < baseStart_2813710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813714 : List Nat := [3, 2, 4, 1, 1, 3, 1, 8]
def baseStart_2813714 : Nat := 118140960795 + 2813714 * 2 ^ 59
def prefixEnd_2813714 : Nat := 4983230072969 + 3 ^ 40 * 2813714 * 2
def baseEnd_2813714 : Nat := 53510655788329983879073

theorem tailTrace_2813714 : CollatzResearch.WordTrace tailWord_2813714 prefixEnd_2813714 53510655788329983879073 := by
  unfold tailWord_2813714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25656145132100549234560049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68416387018934797958826797 25656145132100549234560049)
  ·
    refine ⟨19242108849075411925920037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25656145132100549234560049 19242108849075411925920037)
    ·
      refine ⟨3607895409201639736110007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19242108849075411925920037 3607895409201639736110007)
      ·
        refine ⟨5411843113802459604165011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607895409201639736110007 5411843113802459604165011)
        ·
          refine ⟨8117764670703689406247517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411843113802459604165011 8117764670703689406247517)
          ·
            refine ⟨3044161751513883527342819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8117764670703689406247517 3044161751513883527342819)
            ·
              refine ⟨4566242627270825291014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044161751513883527342819 4566242627270825291014229)
              ·
                refine ⟨53510655788329983879073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4566242627270825291014229 53510655788329983879073)
                ·
                  rfl

theorem cell23_2813714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 8].length) (baseStart_2813714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813714 prefixEnd_2813714 := by exact prefixLift 2813714
  have htrace : WordTrace (prefixWord ++ tailWord_2813714) baseStart_2813714 baseEnd_2813714 := by
    simpa [prefixWord, tailWord_2813714, baseEnd_2813714] using wordTrace_append hprefix tailTrace_2813714
  have hstable : (prefixWord ++ tailWord_2813714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813714).length < 2 ^ (prefixWord ++ tailWord_2813714).sum := by decide
  have hdescent : baseEnd_2813714 < baseStart_2813714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813724 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_2813724 : Nat := 118140960795 + 2813724 * 2 ^ 59
def prefixEnd_2813724 : Nat := 4983230072969 + 3 ^ 40 * 2813724 * 2
def baseEnd_2813724 : Nat := 1444792841091454525609925

theorem tailTrace_2813724 : CollatzResearch.WordTrace tailWord_2813724 prefixEnd_2813724 1444792841091454525609925 := by
  unfold tailWord_2813724
  simp only [CollatzResearch.WordTrace]
  refine ⟨51312472629182984323052113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68416630172243979097402817 51312472629182984323052113)
  ·
    refine ⟨38484354471887238242289085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51312472629182984323052113 38484354471887238242289085)
    ·
      refine ⟨14431632926957714340858407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38484354471887238242289085 14431632926957714340858407)
      ·
        refine ⟨21647449390436571511287611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14431632926957714340858407 21647449390436571511287611)
        ·
          refine ⟨32471174085654857266931417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21647449390436571511287611 32471174085654857266931417)
          ·
            refine ⟨24353380564241142950198563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32471174085654857266931417 24353380564241142950198563)
            ·
              refine ⟨36530070846361714425297845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24353380564241142950198563 36530070846361714425297845)
              ·
                refine ⟨3424694141846410727371673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36530070846361714425297845 3424694141846410727371673)
                ·
                  refine ⟨2568520606384808045528755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424694141846410727371673 2568520606384808045528755)
                  ·
                    refine ⟨3852780909577212068293133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568520606384808045528755 3852780909577212068293133)
                    ·
                      refine ⟨1444792841091454525609925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852780909577212068293133 1444792841091454525609925)
                      ·
                        rfl

theorem cell23_2813724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_2813724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813724 prefixEnd_2813724 := by exact prefixLift 2813724
  have htrace : WordTrace (prefixWord ++ tailWord_2813724) baseStart_2813724 baseEnd_2813724 := by
    simpa [prefixWord, tailWord_2813724, baseEnd_2813724] using wordTrace_append hprefix tailTrace_2813724
  have hstable : (prefixWord ++ tailWord_2813724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813724).length < 2 ^ (prefixWord ++ tailWord_2813724).sum := by decide
  have hdescent : baseEnd_2813724 < baseStart_2813724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813757 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_2813757 : Nat := 118140960795 + 2813757 * 2 ^ 59
def prefixEnd_2813757 : Nat := 4983230072969 + 3 ^ 40 * 2813757 * 2
def baseEnd_2813757 : Nat := 481603261984350965499091

theorem tailTrace_2813757 : CollatzResearch.WordTrace tailWord_2813757 prefixEnd_2813757 481603261984350965499091 := by
  unfold tailWord_2813757
  simp only [CollatzResearch.WordTrace]
  refine ⟨102626148867246415282055525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68417432578164276854703683 102626148867246415282055525)
  ·
    refine ⟨19242402912608702865385411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102626148867246415282055525 19242402912608702865385411)
    ·
      refine ⟨28863604368913054298078117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19242402912608702865385411 28863604368913054298078117)
      ·
        refine ⟨5411925819171197680889647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28863604368913054298078117 5411925819171197680889647)
        ·
          refine ⟨8117888728756796521334471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411925819171197680889647 8117888728756796521334471)
          ·
            refine ⟨12176833093135194782001707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117888728756796521334471 12176833093135194782001707)
            ·
              refine ⟨18265249639702792173002561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12176833093135194782001707 18265249639702792173002561)
              ·
                refine ⟨13698937229777094129751921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18265249639702792173002561 13698937229777094129751921)
                ·
                  refine ⟨10274202922332820597313941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13698937229777094129751921 10274202922332820597313941)
                  ·
                    refine ⟨481603261984350965499091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10274202922332820597313941 481603261984350965499091)
                    ·
                      rfl

theorem cell23_2813757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_2813757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813757 prefixEnd_2813757 := by exact prefixLift 2813757
  have htrace : WordTrace (prefixWord ++ tailWord_2813757) baseStart_2813757 baseEnd_2813757 := by
    simpa [prefixWord, tailWord_2813757, baseEnd_2813757] using wordTrace_append hprefix tailTrace_2813757
  have hstable : (prefixWord ++ tailWord_2813757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813757).length < 2 ^ (prefixWord ++ tailWord_2813757).sum := by decide
  have hdescent : baseEnd_2813757 < baseStart_2813757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813758 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_2813758 : Nat := 118140960795 + 2813758 * 2 ^ 59
def prefixEnd_2813758 : Nat := 4983230072969 + 3 ^ 40 * 2813758 * 2
def baseEnd_2813758 : Nat := 1444810299433707392584769

theorem tailTrace_2813758 : CollatzResearch.WordTrace tailWord_2813758 prefixEnd_2813758 1444810299433707392584769 := by
  unfold tailWord_2813758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828273167530349056605241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68417456893495194968561285 12828273167530349056605241)
  ·
    refine ⟨9621204875647761792453931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12828273167530349056605241 9621204875647761792453931)
    ·
      refine ⟨14431807313471642688680897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9621204875647761792453931 14431807313471642688680897)
      ·
        refine ⟨10823855485103732016510673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14431807313471642688680897 10823855485103732016510673)
        ·
          refine ⟨8117891613827799012383005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10823855485103732016510673 8117891613827799012383005)
          ·
            refine ⟨3044209355185424629643627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8117891613827799012383005 3044209355185424629643627)
            ·
              refine ⟨4566314032778136944465441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044209355185424629643627 4566314032778136944465441)
              ·
                refine ⟨3424735524583602708349081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566314032778136944465441 3424735524583602708349081)
                ·
                  refine ⟨2568551643437702031261811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424735524583602708349081 2568551643437702031261811)
                  ·
                    refine ⟨3852827465156553046892717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568551643437702031261811 3852827465156553046892717)
                    ·
                      refine ⟨1444810299433707392584769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3852827465156553046892717 1444810299433707392584769)
                      ·
                        rfl

theorem cell23_2813758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_2813758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813758 prefixEnd_2813758 := by exact prefixLift 2813758
  have htrace : WordTrace (prefixWord ++ tailWord_2813758) baseStart_2813758 baseEnd_2813758 := by
    simpa [prefixWord, tailWord_2813758, baseEnd_2813758] using wordTrace_append hprefix tailTrace_2813758
  have hstable : (prefixWord ++ tailWord_2813758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813758).length < 2 ^ (prefixWord ++ tailWord_2813758).sum := by decide
  have hdescent : baseEnd_2813758 < baseStart_2813758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813777 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2813777 : Nat := 118140960795 + 2813777 * 2 ^ 59
def prefixEnd_2813777 : Nat := 4983230072969 + 3 ^ 40 * 2813777 * 2
def baseEnd_2813777 : Nat := 1444820055566142818247181

theorem tailTrace_2813777 : CollatzResearch.WordTrace tailWord_2813777 prefixEnd_2813777 1444820055566142818247181 := by
  unfold tailWord_2813777
  simp only [CollatzResearch.WordTrace]
  refine ⟨102626878327173958697783585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68417918884782639131855723 102626878327173958697783585)
  ·
    refine ⟨76970158745380469023337689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102626878327173958697783585 76970158745380469023337689)
    ·
      refine ⟨57727619059035351767503267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76970158745380469023337689 57727619059035351767503267)
      ·
        refine ⟨86591428588553027651254901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57727619059035351767503267 86591428588553027651254901)
        ·
          refine ⟨8117946430176846342305147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86591428588553027651254901 8117946430176846342305147)
          ·
            refine ⟨12176919645265269513457721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117946430176846342305147 12176919645265269513457721)
            ·
              refine ⟨9132689733948952135093291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12176919645265269513457721 9132689733948952135093291)
              ·
                refine ⟨13699034600923428202639937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132689733948952135093291 13699034600923428202639937)
                ·
                  refine ⟨10274275950692571151979953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13699034600923428202639937 10274275950692571151979953)
                  ·
                    refine ⟨7705706963019428363984965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10274275950692571151979953 7705706963019428363984965)
                    ·
                      refine ⟨1444820055566142818247181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7705706963019428363984965 1444820055566142818247181)
                      ·
                        rfl

theorem cell23_2813777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2813777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813777 prefixEnd_2813777 := by exact prefixLift 2813777
  have htrace : WordTrace (prefixWord ++ tailWord_2813777) baseStart_2813777 baseEnd_2813777 := by
    simpa [prefixWord, tailWord_2813777, baseEnd_2813777] using wordTrace_append hprefix tailTrace_2813777
  have hstable : (prefixWord ++ tailWord_2813777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813777).length < 2 ^ (prefixWord ++ tailWord_2813777).sum := by decide
  have hdescent : baseEnd_2813777 < baseStart_2813777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813781 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_2813781 : Nat := 118140960795 + 2813781 * 2 ^ 59
def prefixEnd_2813781 : Nat := 4983230072969 + 3 ^ 40 * 2813781 * 2
def baseEnd_2813781 : Nat := 1444822109488760802597163

theorem tailTrace_2813781 : CollatzResearch.WordTrace tailWord_2813781 prefixEnd_2813781 1444822109488760802597163 := by
  unfold tailWord_2813781
  simp only [CollatzResearch.WordTrace]
  refine ⟨102627024219159467380929197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68418016146106311587286131 102627024219159467380929197)
  ·
    refine ⟨38485134082184800267848449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102627024219159467380929197 38485134082184800267848449)
    ·
      refine ⟨28863850561638600200886337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38485134082184800267848449 28863850561638600200886337)
      ·
        refine ⟨21647887921228950150664753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28863850561638600200886337 21647887921228950150664753)
        ·
          refine ⟨16235915940921712612998565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21647887921228950150664753 16235915940921712612998565)
          ·
            refine ⟨3044234238922821114937231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16235915940921712612998565 3044234238922821114937231)
            ·
              refine ⟨4566351358384231672405847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044234238922821114937231 4566351358384231672405847)
              ·
                refine ⟨6849527037576347508608771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566351358384231672405847 6849527037576347508608771)
                ·
                  refine ⟨10274290556364521262913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849527037576347508608771 10274290556364521262913157)
                  ·
                    refine ⟨1926429479318347736796217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10274290556364521262913157 1926429479318347736796217)
                    ·
                      refine ⟨1444822109488760802597163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926429479318347736796217 1444822109488760802597163)
                      ·
                        rfl

theorem cell23_2813781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_2813781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813781 prefixEnd_2813781 := by exact prefixLift 2813781
  have htrace : WordTrace (prefixWord ++ tailWord_2813781) baseStart_2813781 baseEnd_2813781 := by
    simpa [prefixWord, tailWord_2813781, baseEnd_2813781] using wordTrace_append hprefix tailTrace_2813781
  have hstable : (prefixWord ++ tailWord_2813781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813781).length < 2 ^ (prefixWord ++ tailWord_2813781).sum := by decide
  have hdescent : baseEnd_2813781 < baseStart_2813781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813804 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 5]
def baseStart_2813804 : Nat := 118140960795 + 2813804 * 2 ^ 59
def prefixEnd_2813804 : Nat := 4983230072969 + 3 ^ 40 * 2813804 * 2
def baseEnd_2813804 : Nat := 160537102171534912512173

theorem tailTrace_2813804 : CollatzResearch.WordTrace tailWord_2813804 prefixEnd_2813804 160537102171534912512173 := by
  unfold tailWord_2813804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51313931549038071154508233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68418575398717428206010977 51313931549038071154508233)
  ·
    refine ⟨38485448661778553365881175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51313931549038071154508233 38485448661778553365881175)
    ·
      refine ⟨57728172992667830048821763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38485448661778553365881175 57728172992667830048821763)
      ·
        refine ⟨86592259489001745073232645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57728172992667830048821763 86592259489001745073232645)
        ·
          refine ⟨16236048654187827201231121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86592259489001745073232645 16236048654187827201231121)
          ·
            refine ⟨12177036490640870400923341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16236048654187827201231121 12177036490640870400923341)
            ·
              refine ⟨4566388683990326400346253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12177036490640870400923341 4566388683990326400346253)
              ·
                refine ⟨1712395756496372400129845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4566388683990326400346253 1712395756496372400129845)
                ·
                  refine ⟨160537102171534912512173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1712395756496372400129845 160537102171534912512173)
                  ·
                    rfl

theorem cell23_2813804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_2813804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813804 prefixEnd_2813804 := by exact prefixLift 2813804
  have htrace : WordTrace (prefixWord ++ tailWord_2813804) baseStart_2813804 baseEnd_2813804 := by
    simpa [prefixWord, tailWord_2813804, baseEnd_2813804] using wordTrace_append hprefix tailTrace_2813804
  have hstable : (prefixWord ++ tailWord_2813804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813804).length < 2 ^ (prefixWord ++ tailWord_2813804).sum := by decide
  have hdescent : baseEnd_2813804 < baseStart_2813804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813807 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 7, 2]
def baseStart_2813807 : Nat := 118140960795 + 2813807 * 2 ^ 59
def prefixEnd_2813807 : Nat := 4983230072969 + 3 ^ 40 * 2813807 * 2
def baseEnd_2813807 : Nat := 1444835459985777700872043

theorem tailTrace_2813807 : CollatzResearch.WordTrace tailWord_2813807 prefixEnd_2813807 1444835459985777700872043 := by
  unfold tailWord_2813807
  simp only [CollatzResearch.WordTrace]
  refine ⟨102627972517065273821375675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68418648344710182547583783 102627972517065273821375675)
  ·
    refine ⟨153941958775597910732063513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102627972517065273821375675 153941958775597910732063513)
    ·
      refine ⟨115456469081698433049047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153941958775597910732063513 115456469081698433049047635)
      ·
        refine ⟨173184703622547649573571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115456469081698433049047635 173184703622547649573571453)
        ·
          refine ⟨64944263858455368590089295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173184703622547649573571453 64944263858455368590089295)
          ·
            refine ⟨97416395787683052885133943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64944263858455368590089295 97416395787683052885133943)
            ·
              refine ⟨146124593681524579327700915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97416395787683052885133943 146124593681524579327700915)
              ·
                refine ⟨219186890522286868991551373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146124593681524579327700915 219186890522286868991551373)
                ·
                  refine ⟨82195083945857575871831765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219186890522286868991551373 82195083945857575871831765)
                  ·
                    refine ⟨1926447279981036934496057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82195083945857575871831765 1926447279981036934496057)
                    ·
                      refine ⟨1444835459985777700872043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926447279981036934496057 1444835459985777700872043)
                      ·
                        rfl

theorem cell23_2813807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 7, 2].length) (baseStart_2813807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813807 prefixEnd_2813807 := by exact prefixLift 2813807
  have htrace : WordTrace (prefixWord ++ tailWord_2813807) baseStart_2813807 baseEnd_2813807 := by
    simpa [prefixWord, tailWord_2813807, baseEnd_2813807] using wordTrace_append hprefix tailTrace_2813807
  have hstable : (prefixWord ++ tailWord_2813807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813807).length < 2 ^ (prefixWord ++ tailWord_2813807).sum := by decide
  have hdescent : baseEnd_2813807 < baseStart_2813807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813817 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_2813817 : Nat := 118140960795 + 2813817 * 2 ^ 59
def prefixEnd_2813817 : Nat := 4983230072969 + 3 ^ 40 * 2813817 * 2
def baseEnd_2813817 : Nat := 481613531597440887248999

theorem tailTrace_2813817 : CollatzResearch.WordTrace tailWord_2813817 prefixEnd_2813817 481613531597440887248999 := by
  unfold tailWord_2813817
  simp only [CollatzResearch.WordTrace]
  refine ⟨102628337247029045529239705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68418891498019363686159803 102628337247029045529239705)
  ·
    refine ⟨76971252935271784146929779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102628337247029045529239705 76971252935271784146929779)
    ·
      refine ⟨115456879402907676220394669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76971252935271784146929779 115456879402907676220394669)
      ·
        refine ⟨43296329776090378582648001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115456879402907676220394669 43296329776090378582648001)
        ·
          refine ⟨32472247332067783936986001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43296329776090378582648001 32472247332067783936986001)
          ·
            refine ⟨24354185499050837952739501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32472247332067783936986001 24354185499050837952739501)
            ·
              refine ⟨9132819562144064232277313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24354185499050837952739501 9132819562144064232277313)
              ·
                refine ⟨6849614671608048174207985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9132819562144064232277313 6849614671608048174207985)
                ·
                  refine ⟨5137211003706036130655989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6849614671608048174207985 5137211003706036130655989)
                  ·
                    refine ⟨481613531597440887248999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5137211003706036130655989 481613531597440887248999)
                    ·
                      rfl

theorem cell23_2813817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_2813817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813817 prefixEnd_2813817 := by exact prefixLift 2813817
  have htrace : WordTrace (prefixWord ++ tailWord_2813817) baseStart_2813817 baseEnd_2813817 := by
    simpa [prefixWord, tailWord_2813817, baseEnd_2813817] using wordTrace_append hprefix tailTrace_2813817
  have hstable : (prefixWord ++ tailWord_2813817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813817).length < 2 ^ (prefixWord ++ tailWord_2813817).sum := by decide
  have hdescent : baseEnd_2813817 < baseStart_2813817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2813820 : Nat := 118140960795 + 2813820 * 2 ^ 59
def prefixEnd_2813820 : Nat := 4983230072969 + 3 ^ 40 * 2813820 * 2
def baseEnd_2813820 : Nat := 1444842135234286150009483

theorem tailTrace_2813820 : CollatzResearch.WordTrace tailWord_2813820 prefixEnd_2813820 1444842135234286150009483 := by
  unfold tailWord_2813820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51314223333009088520799457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68418964444012118027732609 51314223333009088520799457)
  ·
    refine ⟨38485667499756816390599593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51314223333009088520799457 38485667499756816390599593)
    ·
      refine ⟨28864250624817612292949695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38485667499756816390599593 28864250624817612292949695)
      ·
        refine ⟨43296375937226418439424543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28864250624817612292949695 43296375937226418439424543)
        ·
          refine ⟨64944563905839627659136815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43296375937226418439424543 64944563905839627659136815)
          ·
            refine ⟨97416845858759441488705223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64944563905839627659136815 97416845858759441488705223)
            ·
              refine ⟨146125268788139162233057835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97416845858759441488705223 146125268788139162233057835)
              ·
                refine ⟨219187903182208743349586753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146125268788139162233057835 219187903182208743349586753)
                ·
                  refine ⟨164390927386656557512190065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219187903182208743349586753 164390927386656557512190065)
                  ·
                    refine ⟨123293195539992418134142549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164390927386656557512190065 123293195539992418134142549)
                    ·
                      refine ⟨1444842135234286150009483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123293195539992418134142549 1444842135234286150009483)
                      ·
                        rfl

theorem cell23_2813820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2813820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813820 prefixEnd_2813820 := by exact prefixLift 2813820
  have htrace : WordTrace (prefixWord ++ tailWord_2813820) baseStart_2813820 baseEnd_2813820 := by
    simpa [prefixWord, tailWord_2813820, baseEnd_2813820] using wordTrace_append hprefix tailTrace_2813820
  have hstable : (prefixWord ++ tailWord_2813820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813820).length < 2 ^ (prefixWord ++ tailWord_2813820).sum := by decide
  have hdescent : baseEnd_2813820 < baseStart_2813820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813827 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_2813827 : Nat := 118140960795 + 2813827 * 2 ^ 59
def prefixEnd_2813827 : Nat := 4983230072969 + 3 ^ 40 * 2813827 * 2
def baseEnd_2813827 : Nat := 1444845729598867622621951

theorem tailTrace_2813827 : CollatzResearch.WordTrace tailWord_2813827 prefixEnd_2813827 1444845729598867622621951 := by
  unfold tailWord_2813827
  simp only [CollatzResearch.WordTrace]
  refine ⟨102628701976992817237103735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68419134651328544824735823 102628701976992817237103735)
  ·
    refine ⟨153943052965489225855655603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102628701976992817237103735 153943052965489225855655603)
    ·
      refine ⟨230914579448233838783483405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153943052965489225855655603 230914579448233838783483405)
      ·
        refine ⟨86592967293087689543806277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230914579448233838783483405 86592967293087689543806277)
        ·
          refine ⟨16236181367453941789463677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86592967293087689543806277 16236181367453941789463677)
          ·
            refine ⟨6088568012795228171048879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16236181367453941789463677 6088568012795228171048879)
            ·
              refine ⟨9132852019192842256573319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088568012795228171048879 9132852019192842256573319)
              ·
                refine ⟨13699278028789263384859979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132852019192842256573319 13699278028789263384859979)
                ·
                  refine ⟨20548917043183895077289969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13699278028789263384859979 20548917043183895077289969)
                  ·
                    refine ⟨15411687782387921307967477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20548917043183895077289969 15411687782387921307967477)
                    ·
                      refine ⟨1444845729598867622621951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15411687782387921307967477 1444845729598867622621951)
                      ·
                        rfl

theorem cell23_2813827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_2813827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813827 prefixEnd_2813827 := by exact prefixLift 2813827
  have htrace : WordTrace (prefixWord ++ tailWord_2813827) baseStart_2813827 baseEnd_2813827 := by
    simpa [prefixWord, tailWord_2813827, baseEnd_2813827] using wordTrace_append hprefix tailTrace_2813827
  have hstable : (prefixWord ++ tailWord_2813827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813827).length < 2 ^ (prefixWord ++ tailWord_2813827).sum := by decide
  have hdescent : baseEnd_2813827 < baseStart_2813827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813832 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2813832 : Nat := 118140960795 + 2813832 * 2 ^ 59
def prefixEnd_2813832 : Nat := 4983230072969 + 3 ^ 40 * 2813832 * 2
def baseEnd_2813832 : Nat := 1444848297002140103059429

theorem tailTrace_2813832 : CollatzResearch.WordTrace tailWord_2813832 prefixEnd_2813832 1444848297002140103059429 := by
  unfold tailWord_2813832
  simp only [CollatzResearch.WordTrace]
  refine ⟨51314442170987351545517875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68419256227983135394023833 51314442170987351545517875)
  ·
    refine ⟨76971663256481027318276813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51314442170987351545517875 76971663256481027318276813)
    ·
      refine ⟨28864373721180385244353805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76971663256481027318276813 28864373721180385244353805)
      ·
        refine ⟨10824140145442644466632677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28864373721180385244353805 10824140145442644466632677)
        ·
          refine ⟨2029526277270495837493627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10824140145442644466632677 2029526277270495837493627)
          ·
            refine ⟨3044289415905743756240441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029526277270495837493627 3044289415905743756240441)
            ·
              refine ⟨2283217061929307817180331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044289415905743756240441 2283217061929307817180331)
              ·
                refine ⟨3424825592893961725770497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283217061929307817180331 3424825592893961725770497)
                ·
                  refine ⟨2568619194670471294327873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424825592893961725770497 2568619194670471294327873)
                  ·
                    refine ⟨1926464396002853470745905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568619194670471294327873 1926464396002853470745905)
                    ·
                      refine ⟨1444848297002140103059429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926464396002853470745905 1444848297002140103059429)
                      ·
                        rfl

theorem cell23_2813832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2813832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813832 prefixEnd_2813832 := by exact prefixLift 2813832
  have htrace : WordTrace (prefixWord ++ tailWord_2813832) baseStart_2813832 baseEnd_2813832 := by
    simpa [prefixWord, tailWord_2813832, baseEnd_2813832] using wordTrace_append hprefix tailTrace_2813832
  have hstable : (prefixWord ++ tailWord_2813832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813832).length < 2 ^ (prefixWord ++ tailWord_2813832).sum := by decide
  have hdescent : baseEnd_2813832 < baseStart_2813832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813881 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 1, 4]
def baseStart_2813881 : Nat := 118140960795 + 2813881 * 2 ^ 59
def prefixEnd_2813881 : Nat := 4983230072969 + 3 ^ 40 * 2813881 * 2
def baseEnd_2813881 : Nat := 481624485851403470448901

theorem tailTrace_2813881 : CollatzResearch.WordTrace tailWord_2813881 prefixEnd_2813881 481624485851403470448901 := by
  unfold tailWord_2813881
  simp only [CollatzResearch.WordTrace]
  refine ⟨102630671518797184459569497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68420447679198122973046331 102630671518797184459569497)
  ·
    refine ⟨76973003639097888344677123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102630671518797184459569497 76973003639097888344677123)
    ·
      refine ⟨115459505458646832517015685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76973003639097888344677123 115459505458646832517015685)
      ·
        refine ⟨21648657273496281096940441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115459505458646832517015685 21648657273496281096940441)
        ·
          refine ⟨16236492955122210822705331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21648657273496281096940441 16236492955122210822705331)
          ·
            refine ⟨24354739432683316234057997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16236492955122210822705331 24354739432683316234057997)
            ·
              refine ⟨9133027287256243587771749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24354739432683316234057997 9133027287256243587771749)
              ·
                refine ⟨1712442616360545672707203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9133027287256243587771749 1712442616360545672707203)
                ·
                  refine ⟨2568663924540818509060805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712442616360545672707203 2568663924540818509060805)
                  ·
                    refine ⟨481624485851403470448901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568663924540818509060805 481624485851403470448901)
                    ·
                      rfl

theorem cell23_2813881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_2813881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813881 prefixEnd_2813881 := by exact prefixLift 2813881
  have htrace : WordTrace (prefixWord ++ tailWord_2813881) baseStart_2813881 baseEnd_2813881 := by
    simpa [prefixWord, tailWord_2813881, baseEnd_2813881] using wordTrace_append hprefix tailTrace_2813881
  have hstable : (prefixWord ++ tailWord_2813881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813881).length < 2 ^ (prefixWord ++ tailWord_2813881).sum := by decide
  have hdescent : baseEnd_2813881 < baseStart_2813881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813904 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_2813904 : Nat := 118140960795 + 2813904 * 2 ^ 59
def prefixEnd_2813904 : Nat := 4983230072969 + 3 ^ 40 * 2813904 * 2
def baseEnd_2813904 : Nat := 1444885267609263821359097

theorem tailTrace_2813904 : CollatzResearch.WordTrace tailWord_2813904 prefixEnd_2813904 1444885267609263821359097 := by
  unfold tailWord_2813904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51315755198856929693828383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68421006931809239591771177 51315755198856929693828383)
  ·
    refine ⟨76973632798285394540742575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51315755198856929693828383 76973632798285394540742575)
    ·
      refine ⟨115460449197428091811113863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76973632798285394540742575 115460449197428091811113863)
      ·
        refine ⟨173190673796142137716670795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115460449197428091811113863 173190673796142137716670795)
        ·
          refine ⟨259786010694213206575006193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173190673796142137716670795 259786010694213206575006193)
          ·
            refine ⟨194839508020659904931254645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259786010694213206575006193 194839508020659904931254645)
            ·
              refine ⟨18266203876936866087305123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194839508020659904931254645 18266203876936866087305123)
              ·
                refine ⟨27399305815405299130957685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18266203876936866087305123 27399305815405299130957685)
                ·
                  refine ⟨2568684920194246793527283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27399305815405299130957685 2568684920194246793527283)
                  ·
                    refine ⟨3853027380291370190290925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568684920194246793527283 3853027380291370190290925)
                    ·
                      refine ⟨1444885267609263821359097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853027380291370190290925 1444885267609263821359097)
                      ·
                        rfl

theorem cell23_2813904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_2813904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813904 prefixEnd_2813904 := by exact prefixLift 2813904
  have htrace : WordTrace (prefixWord ++ tailWord_2813904) baseStart_2813904 baseEnd_2813904 := by
    simpa [prefixWord, tailWord_2813904, baseEnd_2813904] using wordTrace_append hprefix tailTrace_2813904
  have hstable : (prefixWord ++ tailWord_2813904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813904).length < 2 ^ (prefixWord ++ tailWord_2813904).sum := by decide
  have hdescent : baseEnd_2813904 < baseStart_2813904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813924 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_2813924 : Nat := 118140960795 + 2813924 * 2 ^ 59
def prefixEnd_2813924 : Nat := 4983230072969 + 3 ^ 40 * 2813924 * 2
def baseEnd_2813924 : Nat := 481631845740784581036335

theorem tailTrace_2813924 : CollatzResearch.WordTrace tailWord_2813924 prefixEnd_2813924 481631845740784581036335 := by
  unfold tailWord_2813924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51316119928820701401692413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68421493238427601868923217 51316119928820701401692413)
  ·
    refine ⟨19243544973307763025634655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51316119928820701401692413 19243544973307763025634655)
    ·
      refine ⟨28865317459961644538451983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19243544973307763025634655 28865317459961644538451983)
      ·
        refine ⟨43297976189942466807677975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28865317459961644538451983 43297976189942466807677975)
        ·
          refine ⟨64946964284913700211516963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43297976189942466807677975 64946964284913700211516963)
          ·
            refine ⟨97420446427370550317275445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64946964284913700211516963 97420446427370550317275445)
            ·
              refine ⟨9133166852565989092244573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97420446427370550317275445 9133166852565989092244573)
              ·
                refine ⟨3424937569712245909591715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9133166852565989092244573 3424937569712245909591715)
                ·
                  refine ⟨5137406354568368864387573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424937569712245909591715 5137406354568368864387573)
                  ·
                    refine ⟨481631845740784581036335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5137406354568368864387573 481631845740784581036335)
                    ·
                      rfl

theorem cell23_2813924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_2813924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813924 prefixEnd_2813924 := by exact prefixLift 2813924
  have htrace : WordTrace (prefixWord ++ tailWord_2813924) baseStart_2813924 baseEnd_2813924 := by
    simpa [prefixWord, tailWord_2813924, baseEnd_2813924] using wordTrace_append hprefix tailTrace_2813924
  have hstable : (prefixWord ++ tailWord_2813924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813924).length < 2 ^ (prefixWord ++ tailWord_2813924).sum := by decide
  have hdescent : baseEnd_2813924 < baseStart_2813924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813947 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_2813947 : Nat := 118140960795 + 2813947 * 2 ^ 59
def prefixEnd_2813947 : Nat := 4983230072969 + 3 ^ 40 * 2813947 * 2
def baseEnd_2813947 : Nat := 1444907347277407153121399

theorem tailTrace_2813947 : CollatzResearch.WordTrace tailWord_2813947 prefixEnd_2813947 1444907347277407153121399 := by
  unfold tailWord_2813947
  simp only [CollatzResearch.WordTrace]
  refine ⟨102633078736558077731472095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68422052491038718487648063 102633078736558077731472095)
  ·
    refine ⟨153949618104837116597208143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102633078736558077731472095 153949618104837116597208143)
    ·
      refine ⟨230924427157255674895812215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153949618104837116597208143 230924427157255674895812215)
      ·
        refine ⟨346386640735883512343718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230924427157255674895812215 346386640735883512343718323)
        ·
          refine ⟨519579961103825268515577485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346386640735883512343718323 519579961103825268515577485)
          ·
            refine ⟨194842485413934475693341557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519579961103825268515577485 194842485413934475693341557)
            ·
              refine ⟨18266483007556357096250771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194842485413934475693341557 18266483007556357096250771)
              ·
                refine ⟨27399724511334535644376157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18266483007556357096250771 27399724511334535644376157)
                ·
                  refine ⟨10274896691750450866641059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27399724511334535644376157 10274896691750450866641059)
                  ·
                    refine ⟨15412345037625676299961589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274896691750450866641059 15412345037625676299961589)
                    ·
                      refine ⟨1444907347277407153121399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15412345037625676299961589 1444907347277407153121399)
                      ·
                        rfl

theorem cell23_2813947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_2813947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813947 prefixEnd_2813947 := by exact prefixLift 2813947
  have htrace : WordTrace (prefixWord ++ tailWord_2813947) baseStart_2813947 baseEnd_2813947 := by
    simpa [prefixWord, tailWord_2813947, baseEnd_2813947] using wordTrace_append hprefix tailTrace_2813947
  have hstable : (prefixWord ++ tailWord_2813947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813947).length < 2 ^ (prefixWord ++ tailWord_2813947).sum := by decide
  have hdescent : baseEnd_2813947 < baseStart_2813947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813981 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2813981 : Nat := 118140960795 + 2813981 * 2 ^ 59
def prefixEnd_2813981 : Nat := 4983230072969 + 3 ^ 40 * 2813981 * 2
def baseEnd_2813981 : Nat := 1444924805619660020096243

theorem tailTrace_2813981 : CollatzResearch.WordTrace tailWord_2813981 prefixEnd_2813981 1444924805619660020096243 := by
  unfold tailWord_2813981
  simp only [CollatzResearch.WordTrace]
  refine ⟨102634318818434901538209797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68422879212289934358806531 102634318818434901538209797)
  ·
    refine ⟨19243934778456544038414337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102634318818434901538209797 19243934778456544038414337)
    ·
      refine ⟨14432951083842408028810753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19243934778456544038414337 14432951083842408028810753)
      ·
        refine ⟨10824713312881806021608065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14432951083842408028810753 10824713312881806021608065)
        ·
          refine ⟨8118534984661354516206049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824713312881806021608065 8118534984661354516206049)
          ·
            refine ⟨6088901238496015887154537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118534984661354516206049 6088901238496015887154537)
            ·
              refine ⟨4566675928872011915365903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088901238496015887154537 4566675928872011915365903)
              ·
                refine ⟨6850013893308017873048855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566675928872011915365903 6850013893308017873048855)
                ·
                  refine ⟨10275020839962026809573283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850013893308017873048855 10275020839962026809573283)
                  ·
                    refine ⟨15412531259943040214359925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10275020839962026809573283 15412531259943040214359925)
                    ·
                      refine ⟨1444924805619660020096243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15412531259943040214359925 1444924805619660020096243)
                      ·
                        rfl

theorem cell23_2813981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2813981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2813981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2813981 prefixEnd_2813981 := by exact prefixLift 2813981
  have htrace : WordTrace (prefixWord ++ tailWord_2813981) baseStart_2813981 baseEnd_2813981 := by
    simpa [prefixWord, tailWord_2813981, baseEnd_2813981] using wordTrace_append hprefix tailTrace_2813981
  have hstable : (prefixWord ++ tailWord_2813981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813981).length < 2 ^ (prefixWord ++ tailWord_2813981).sum := by decide
  have hdescent : baseEnd_2813981 < baseStart_2813981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814011 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 3]
def baseStart_2814011 : Nat := 118140960795 + 2814011 * 2 ^ 59
def prefixEnd_2814011 : Nat := 4983230072969 + 3 ^ 40 * 2814011 * 2
def baseEnd_2814011 : Nat := 1444940210039294902721105

theorem tailTrace_2814011 : CollatzResearch.WordTrace tailWord_2814011 prefixEnd_2814011 1444940210039294902721105 := by
  unfold tailWord_2814011
  simp only [CollatzResearch.WordTrace]
  refine ⟨102635413008326216661801887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68423608672217477774534591 102635413008326216661801887)
  ·
    refine ⟨153953119512489324992702831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102635413008326216661801887 153953119512489324992702831)
    ·
      refine ⟨230929679268733987489054247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153953119512489324992702831 230929679268733987489054247)
      ·
        refine ⟨346394518903100981233581371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230929679268733987489054247 346394518903100981233581371)
        ·
          refine ⟨519591778354651471850372057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346394518903100981233581371 519591778354651471850372057)
          ·
            refine ⟨389693833765988603887779043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519591778354651471850372057 389693833765988603887779043)
            ·
              refine ⟨584540750648982905831668565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389693833765988603887779043 584540750648982905831668565)
              ·
                refine ⟨3425043460833884213857433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 584540750648982905831668565 3425043460833884213857433)
                ·
                  refine ⟨2568782595625413160393075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3425043460833884213857433 2568782595625413160393075)
                  ·
                    refine ⟨3853173893438119740589613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568782595625413160393075 3853173893438119740589613)
                    ·
                      refine ⟨1444940210039294902721105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853173893438119740589613 1444940210039294902721105)
                      ·
                        rfl

theorem cell23_2814011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 1, 3].length) (baseStart_2814011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814011 prefixEnd_2814011 := by exact prefixLift 2814011
  have htrace : WordTrace (prefixWord ++ tailWord_2814011) baseStart_2814011 baseEnd_2814011 := by
    simpa [prefixWord, tailWord_2814011, baseEnd_2814011] using wordTrace_append hprefix tailTrace_2814011
  have hstable : (prefixWord ++ tailWord_2814011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814011).length < 2 ^ (prefixWord ++ tailWord_2814011).sum := by decide
  have hdescent : baseEnd_2814011 < baseStart_2814011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814027 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 8]
def baseStart_2814027 : Nat := 118140960795 + 2814027 * 2 ^ 59
def prefixEnd_2814027 : Nat := 4983230072969 + 3 ^ 40 * 2814027 * 2
def baseEnd_2814027 : Nat := 481649475243255613373677

theorem tailTrace_2814027 : CollatzResearch.WordTrace tailWord_2814027 prefixEnd_2814027 481649475243255613373677 := by
  unfold tailWord_2814027
  simp only [CollatzResearch.WordTrace]
  refine ⟨102635996576268251394384335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68423997717512167596256223 102635996576268251394384335)
  ·
    refine ⟨153953994864402377091576503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102635996576268251394384335 153953994864402377091576503)
    ·
      refine ⟨230930992296603565637364755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153953994864402377091576503 230930992296603565637364755)
      ·
        refine ⟨346396488444905348456047133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230930992296603565637364755 346396488444905348456047133)
        ·
          refine ⟨129898683166839505671017675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346396488444905348456047133 129898683166839505671017675)
          ·
            refine ⟨194848024750259258506526513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129898683166839505671017675 194848024750259258506526513)
            ·
              refine ⟨146136018562694443879894885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194848024750259258506526513 146136018562694443879894885)
              ·
                refine ⟨27400503480505208227480291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146136018562694443879894885 27400503480505208227480291)
                ·
                  refine ⟨41100755220757812341220437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27400503480505208227480291 41100755220757812341220437)
                  ·
                    refine ⟨481649475243255613373677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41100755220757812341220437 481649475243255613373677)
                    ·
                      rfl

theorem cell23_2814027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_2814027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814027 prefixEnd_2814027 := by exact prefixLift 2814027
  have htrace : WordTrace (prefixWord ++ tailWord_2814027) baseStart_2814027 baseEnd_2814027 := by
    simpa [prefixWord, tailWord_2814027, baseEnd_2814027] using wordTrace_append hprefix tailTrace_2814027
  have hstable : (prefixWord ++ tailWord_2814027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814027).length < 2 ^ (prefixWord ++ tailWord_2814027).sum := by decide
  have hdescent : baseEnd_2814027 < baseStart_2814027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814045 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2814045 : Nat := 118140960795 + 2814045 * 2 ^ 59
def prefixEnd_2814045 : Nat := 4983230072969 + 3 ^ 40 * 2814045 * 2
def baseEnd_2814045 : Nat := 1444957668381547769695949

theorem tailTrace_2814045 : CollatzResearch.WordTrace tailWord_2814045 prefixEnd_2814045 1444957668381547769695949 := by
  unfold tailWord_2814045
  simp only [CollatzResearch.WordTrace]
  refine ⟨102636653090203040468539589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68424435393468693645693059 102636653090203040468539589)
  ·
    refine ⟨19244372454413070087851173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102636653090203040468539589 19244372454413070087851173)
    ·
      refine ⟨3608319835202450641472095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19244372454413070087851173 3608319835202450641472095)
      ·
        refine ⟨5412479752803675962208143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608319835202450641472095 5412479752803675962208143)
        ·
          refine ⟨8118719629205513943312215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412479752803675962208143 8118719629205513943312215)
          ·
            refine ⟨12178079443808270914968323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118719629205513943312215 12178079443808270914968323)
            ·
              refine ⟨18267119165712406372452485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12178079443808270914968323 18267119165712406372452485)
              ·
                refine ⟨3425084843571076194834841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18267119165712406372452485 3425084843571076194834841)
                ·
                  refine ⟨2568813632678307146126131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3425084843571076194834841 2568813632678307146126131)
                  ·
                    refine ⟨3853220449017460719189197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568813632678307146126131 3853220449017460719189197)
                    ·
                      refine ⟨1444957668381547769695949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853220449017460719189197 1444957668381547769695949)
                      ·
                        rfl

theorem cell23_2814045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2814045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814045 prefixEnd_2814045 := by exact prefixLift 2814045
  have htrace : WordTrace (prefixWord ++ tailWord_2814045) baseStart_2814045 baseEnd_2814045 := by
    simpa [prefixWord, tailWord_2814045, baseEnd_2814045] using wordTrace_append hprefix tailTrace_2814045
  have hstable : (prefixWord ++ tailWord_2814045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814045).length < 2 ^ (prefixWord ++ tailWord_2814045).sum := by decide
  have hdescent : baseEnd_2814045 < baseStart_2814045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814046 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2814046 : Nat := 118140960795 + 2814046 * 2 ^ 59
def prefixEnd_2814046 : Nat := 4983230072969 + 3 ^ 40 * 2814046 * 2
def baseEnd_2814046 : Nat := 1444958181862202265783445

theorem tailTrace_2814046 : CollatzResearch.WordTrace tailWord_2814046 prefixEnd_2814046 1444958181862202265783445 := by
  unfold tailWord_2814046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829586195399927204915749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68424459708799611759550661 12829586195399927204915749)
  ·
    refine ⟨2405547411637486350921703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12829586195399927204915749 2405547411637486350921703)
    ·
      refine ⟨3608321117456229526382555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405547411637486350921703 3608321117456229526382555)
      ·
        refine ⟨5412481676184344289573833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608321117456229526382555 5412481676184344289573833)
        ·
          refine ⟨4059361257138258217180375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412481676184344289573833 4059361257138258217180375)
          ·
            refine ⟨6089041885707387325770563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059361257138258217180375 6089041885707387325770563)
            ·
              refine ⟨9133562828561080988655845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089041885707387325770563 9133562828561080988655845)
              ·
                refine ⟨1712543030355202685372971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9133562828561080988655845 1712543030355202685372971)
                ·
                  refine ⟨2568814545532804028059457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712543030355202685372971 2568814545532804028059457)
                  ·
                    refine ⟨1926610909149603021044593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568814545532804028059457 1926610909149603021044593)
                    ·
                      refine ⟨1444958181862202265783445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926610909149603021044593 1444958181862202265783445)
                      ·
                        rfl

theorem cell23_2814046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2814046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814046 prefixEnd_2814046 := by exact prefixLift 2814046
  have htrace : WordTrace (prefixWord ++ tailWord_2814046) baseStart_2814046 baseEnd_2814046 := by
    simpa [prefixWord, tailWord_2814046, baseEnd_2814046] using wordTrace_append hprefix tailTrace_2814046
  have hstable : (prefixWord ++ tailWord_2814046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814046).length < 2 ^ (prefixWord ++ tailWord_2814046).sum := by decide
  have hdescent : baseEnd_2814046 < baseStart_2814046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814064 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_2814064 : Nat := 118140960795 + 2814064 * 2 ^ 59
def prefixEnd_2814064 : Nat := 4983230072969 + 3 ^ 40 * 2814064 * 2
def baseEnd_2814064 : Nat := 1444967424513983195358361

theorem tailTrace_2814064 : CollatzResearch.WordTrace tailWord_2814064 prefixEnd_2814064 1444967424513983195358361 := by
  unfold tailWord_2814064
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318673038567103356740623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68424897384756137808987497 51318673038567103356740623)
  ·
    refine ⟨76978009557850655035110935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51318673038567103356740623 76978009557850655035110935)
    ·
      refine ⟨115467014336775982552666403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76978009557850655035110935 115467014336775982552666403)
      ·
        refine ⟨173200521505163973828999605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115467014336775982552666403 173200521505163973828999605)
        ·
          refine ⟨16237548891109122546468713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173200521505163973828999605 16237548891109122546468713)
          ·
            refine ⟨12178161668331841909851535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16237548891109122546468713 12178161668331841909851535)
            ·
              refine ⟨18267242502497762864777303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12178161668331841909851535 18267242502497762864777303)
              ·
                refine ⟨27400863753746644297165955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18267242502497762864777303 27400863753746644297165955)
                ·
                  refine ⟨41101295630619966445748933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27400863753746644297165955 41101295630619966445748933)
                  ·
                    refine ⟨7706492930741243708577925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41101295630619966445748933 7706492930741243708577925)
                    ·
                      refine ⟨1444967424513983195358361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7706492930741243708577925 1444967424513983195358361)
                      ·
                        rfl

theorem cell23_2814064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_2814064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814064 prefixEnd_2814064 := by exact prefixLift 2814064
  have htrace : WordTrace (prefixWord ++ tailWord_2814064) baseStart_2814064 baseEnd_2814064 := by
    simpa [prefixWord, tailWord_2814064, baseEnd_2814064] using wordTrace_append hprefix tailTrace_2814064
  have hstable : (prefixWord ++ tailWord_2814064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814064).length < 2 ^ (prefixWord ++ tailWord_2814064).sum := by decide
  have hdescent : baseEnd_2814064 < baseStart_2814064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814119 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2814119 : Nat := 118140960795 + 2814119 * 2 ^ 59
def prefixEnd_2814119 : Nat := 4983230072969 + 3 ^ 40 * 2814119 * 2
def baseEnd_2814119 : Nat := 1444995665949980480170609

theorem tailTrace_2814119 : CollatzResearch.WordTrace tailWord_2814119 prefixEnd_2814119 1444995665949980480170609 := by
  unfold tailWord_2814119
  simp only [CollatzResearch.WordTrace]
  refine ⟨102639352091934951106733411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68426234727956634071155607 102639352091934951106733411)
  ·
    refine ⟨153959028137902426660100117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102639352091934951106733411 153959028137902426660100117)
    ·
      refine ⟨7216829443964176249692193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153959028137902426660100117 7216829443964176249692193)
      ·
        refine ⟨5412622082973132187269145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7216829443964176249692193 5412622082973132187269145)
        ·
          refine ⟨4059466562229849140451859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412622082973132187269145 4059466562229849140451859)
          ·
            refine ⟨6089199843344773710677789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059466562229849140451859 6089199843344773710677789)
            ·
              refine ⟨2283449941254290141504171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6089199843344773710677789 2283449941254290141504171)
              ·
                refine ⟨3425174911881435212256257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283449941254290141504171 3425174911881435212256257)
                ·
                  refine ⟨2568881183911076409192193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3425174911881435212256257 2568881183911076409192193)
                  ·
                    refine ⟨1926660887933307306894145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568881183911076409192193 1926660887933307306894145)
                    ·
                      refine ⟨1444995665949980480170609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926660887933307306894145 1444995665949980480170609)
                      ·
                        rfl

theorem cell23_2814119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2814119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814119 prefixEnd_2814119 := by exact prefixLift 2814119
  have htrace : WordTrace (prefixWord ++ tailWord_2814119) baseStart_2814119 baseEnd_2814119 := by
    simpa [prefixWord, tailWord_2814119, baseEnd_2814119] using wordTrace_append hprefix tailTrace_2814119
  have hstable : (prefixWord ++ tailWord_2814119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814119).length < 2 ^ (prefixWord ++ tailWord_2814119).sum := by decide
  have hdescent : baseEnd_2814119 < baseStart_2814119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814141 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2814141 : Nat := 118140960795 + 2814141 * 2 ^ 59
def prefixEnd_2814141 : Nat := 4983230072969 + 3 ^ 40 * 2814141 * 2
def baseEnd_2814141 : Nat := 1445006962524379394095507

theorem tailTrace_2814141 : CollatzResearch.WordTrace tailWord_2814141 prefixEnd_2814141 1445006962524379394095507 := by
  unfold tailWord_2814141
  simp only [CollatzResearch.WordTrace]
  refine ⟨102640154497855248864034277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68426769665236832576022851 102640154497855248864034277)
  ·
    refine ⟨19245028968347859162006427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102640154497855248864034277 19245028968347859162006427)
    ·
      refine ⟨28867543452521788743009641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245028968347859162006427 28867543452521788743009641)
      ·
        refine ⟨21650657589391341557257231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28867543452521788743009641 21650657589391341557257231)
        ·
          refine ⟨32475986384087012335885847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21650657589391341557257231 32475986384087012335885847)
          ·
            refine ⟨48713979576130518503828771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32475986384087012335885847 48713979576130518503828771)
            ·
              refine ⟨73070969364195777755743157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48713979576130518503828771 73070969364195777755743157)
              ·
                refine ⟨6850403377893354164600921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73070969364195777755743157 6850403377893354164600921)
                ·
                  refine ⟨5137802533420015623450691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6850403377893354164600921 5137802533420015623450691)
                  ·
                    refine ⟨7706703800130023435176037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5137802533420015623450691 7706703800130023435176037)
                    ·
                      refine ⟨1445006962524379394095507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7706703800130023435176037 1445006962524379394095507)
                      ·
                        rfl

theorem cell23_2814141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2814141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814141 prefixEnd_2814141 := by exact prefixLift 2814141
  have htrace : WordTrace (prefixWord ++ tailWord_2814141) baseStart_2814141 baseEnd_2814141 := by
    simpa [prefixWord, tailWord_2814141, baseEnd_2814141] using wordTrace_append hprefix tailTrace_2814141
  have hstable : (prefixWord ++ tailWord_2814141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814141).length < 2 ^ (prefixWord ++ tailWord_2814141).sum := by decide
  have hdescent : baseEnd_2814141 < baseStart_2814141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814142 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2814142 : Nat := 118140960795 + 2814142 * 2 ^ 59
def prefixEnd_2814142 : Nat := 4983230072969 + 3 ^ 40 * 2814142 * 2
def baseEnd_2814142 : Nat := 160556386222781543353667

theorem tailTrace_2814142 : CollatzResearch.WordTrace tailWord_2814142 prefixEnd_2814142 160556386222781543353667 := by
  unfold tailWord_2814142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830023871356453254352585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68426793980567750689880453 12830023871356453254352585)
  ·
    refine ⟨9622517903517339940764439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12830023871356453254352585 9622517903517339940764439)
    ·
      refine ⟨14433776855276009911146659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622517903517339940764439 14433776855276009911146659)
      ·
        refine ⟨21650665282914014866719989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433776855276009911146659 21650665282914014866719989)
        ·
          refine ⟨2029749870273188893754999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21650665282914014866719989 2029749870273188893754999)
          ·
            refine ⟨3044624805409783340632499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029749870273188893754999 3044624805409783340632499)
            ·
              refine ⟨4566937208114675010948749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044624805409783340632499 4566937208114675010948749)
              ·
                refine ⟨1712601453043003129105781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4566937208114675010948749 1712601453043003129105781)
                ·
                  refine ⟨160556386222781543353667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1712601453043003129105781 160556386222781543353667)
                  ·
                    rfl

theorem cell23_2814142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2814142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814142 prefixEnd_2814142 := by exact prefixLift 2814142
  have htrace : WordTrace (prefixWord ++ tailWord_2814142) baseStart_2814142 baseEnd_2814142 := by
    simpa [prefixWord, tailWord_2814142, baseEnd_2814142] using wordTrace_append hprefix tailTrace_2814142
  have hstable : (prefixWord ++ tailWord_2814142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814142).length < 2 ^ (prefixWord ++ tailWord_2814142).sum := by decide
  have hdescent : baseEnd_2814142 < baseStart_2814142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814158 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2814158 : Nat := 118140960795 + 2814158 * 2 ^ 59
def prefixEnd_2814158 : Nat := 4983230072969 + 3 ^ 40 * 2814158 * 2
def baseEnd_2814158 : Nat := 1445015691695505827582929

theorem tailTrace_2814158 : CollatzResearch.WordTrace tailWord_2814158 prefixEnd_2814158 1445015691695505827582929 := by
  unfold tailWord_2814158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830096817349207595925391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68427183025862440511602085 12830096817349207595925391)
  ·
    refine ⟨19245145226023811393888087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12830096817349207595925391 19245145226023811393888087)
    ·
      refine ⟨28867717839035717090832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245145226023811393888087 28867717839035717090832131)
      ·
        refine ⟨43301576758553575636248197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28867717839035717090832131 43301576758553575636248197)
        ·
          refine ⟨8119045642228795431796537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43301576758553575636248197 8119045642228795431796537)
          ·
            refine ⟨6089284231671596573847403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119045642228795431796537 6089284231671596573847403)
            ·
              refine ⟨9133926347507394860771105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089284231671596573847403 9133926347507394860771105)
              ·
                refine ⟨6850444760630546145578329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9133926347507394860771105 6850444760630546145578329)
                ·
                  refine ⟨5137833570472909609183747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6850444760630546145578329 5137833570472909609183747)
                  ·
                    refine ⟨7706750355709364413775621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5137833570472909609183747 7706750355709364413775621)
                    ·
                      refine ⟨1445015691695505827582929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7706750355709364413775621 1445015691695505827582929)
                      ·
                        rfl

theorem cell23_2814158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2814158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814158 prefixEnd_2814158 := by exact prefixLift 2814158
  have htrace : WordTrace (prefixWord ++ tailWord_2814158) baseStart_2814158 baseEnd_2814158 := by
    simpa [prefixWord, tailWord_2814158, baseEnd_2814158] using wordTrace_append hprefix tailTrace_2814158
  have hstable : (prefixWord ++ tailWord_2814158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814158).length < 2 ^ (prefixWord ++ tailWord_2814158).sum := by decide
  have hdescent : baseEnd_2814158 < baseStart_2814158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814161 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_2814161 : Nat := 118140960795 + 2814161 * 2 ^ 59
def prefixEnd_2814161 : Nat := 4983230072969 + 3 ^ 40 * 2814161 * 2
def baseEnd_2814161 : Nat := 1445017232137469315845415

theorem tailTrace_2814161 : CollatzResearch.WordTrace tailWord_2814161 prefixEnd_2814161 1445017232137469315845415 := by
  unfold tailWord_2814161
  simp only [CollatzResearch.WordTrace]
  refine ⟨102640883957782792279762337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68427255971855194853174891 102640883957782792279762337)
  ·
    refine ⟨76980662968337094209821753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102640883957782792279762337 76980662968337094209821753)
    ·
      refine ⟨57735497226252820657366315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76980662968337094209821753 57735497226252820657366315)
      ·
        refine ⟨86603245839379230986049473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57735497226252820657366315 86603245839379230986049473)
        ·
          refine ⟨64952434379534423239537105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86603245839379230986049473 64952434379534423239537105)
          ·
            refine ⟨48714325784650817429652829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64952434379534423239537105 48714325784650817429652829)
            ·
              refine ⟨18267872169244056536119811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48714325784650817429652829 18267872169244056536119811)
              ·
                refine ⟨27401808253866084804179717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18267872169244056536119811 27401808253866084804179717)
                ·
                  refine ⟨5137839047599890900783697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27401808253866084804179717 5137839047599890900783697)
                  ·
                    refine ⟨3853379285699918175587773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5137839047599890900783697 3853379285699918175587773)
                    ·
                      refine ⟨1445017232137469315845415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853379285699918175587773 1445017232137469315845415)
                      ·
                        rfl

theorem cell23_2814161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_2814161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814161 prefixEnd_2814161 := by exact prefixLift 2814161
  have htrace : WordTrace (prefixWord ++ tailWord_2814161) baseStart_2814161 baseEnd_2814161 := by
    simpa [prefixWord, tailWord_2814161, baseEnd_2814161] using wordTrace_append hprefix tailTrace_2814161
  have hstable : (prefixWord ++ tailWord_2814161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814161).length < 2 ^ (prefixWord ++ tailWord_2814161).sum := by decide
  have hdescent : baseEnd_2814161 < baseStart_2814161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814168 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 3, 4]
def baseStart_2814168 : Nat := 118140960795 + 2814168 * 2 ^ 59
def prefixEnd_2814168 : Nat := 4983230072969 + 3 ^ 40 * 2814168 * 2
def baseEnd_2814168 : Nat := 481673608834016929485961

theorem tailTrace_2814168 : CollatzResearch.WordTrace tailWord_2814168 prefixEnd_2814168 481673608834016929485961 := by
  unfold tailWord_2814168
  simp only [CollatzResearch.WordTrace]
  refine ⟨51320569634378716237633579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68427426179171621650178105 51320569634378716237633579)
  ·
    refine ⟨76980854451568074356450369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51320569634378716237633579 76980854451568074356450369)
    ·
      refine ⟨57735640838676055767337777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76980854451568074356450369 57735640838676055767337777)
      ·
        refine ⟨43301730629007041825503333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57735640838676055767337777 43301730629007041825503333)
        ·
          refine ⟨8119074492938820342281875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43301730629007041825503333 8119074492938820342281875)
          ·
            refine ⟨12178611739408230513422813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119074492938820342281875 12178611739408230513422813)
            ·
              refine ⟨4566979402278086442533555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12178611739408230513422813 4566979402278086442533555)
              ·
                refine ⟨6850469103417129663800333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566979402278086442533555 6850469103417129663800333)
                ·
                  refine ⟨2568925913781423623925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6850469103417129663800333 2568925913781423623925125)
                  ·
                    refine ⟨481673608834016929485961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2568925913781423623925125 481673608834016929485961)
                    ·
                      rfl

theorem cell23_2814168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_2814168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814168 prefixEnd_2814168 := by exact prefixLift 2814168
  have htrace : WordTrace (prefixWord ++ tailWord_2814168) baseStart_2814168 baseEnd_2814168 := by
    simpa [prefixWord, tailWord_2814168, baseEnd_2814168] using wordTrace_append hprefix tailTrace_2814168
  have hstable : (prefixWord ++ tailWord_2814168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814168).length < 2 ^ (prefixWord ++ tailWord_2814168).sum := by decide
  have hdescent : baseEnd_2814168 < baseStart_2814168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814215 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 6]
def baseStart_2814215 : Nat := 118140960795 + 2814215 * 2 ^ 59
def prefixEnd_2814215 : Nat := 4983230072969 + 3 ^ 40 * 2814215 * 2
def baseEnd_2814215 : Nat := 160560551121423567174463

theorem tailTrace_2814215 : CollatzResearch.WordTrace tailWord_2814215 prefixEnd_2814215 160560551121423567174463 := by
  unfold tailWord_2814215
  simp only [CollatzResearch.WordTrace]
  refine ⟨102642853499587159502228099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68428568999724773001485399 102642853499587159502228099)
  ·
    refine ⟨153964280249380739253342149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102642853499587159502228099 153964280249380739253342149)
    ·
      refine ⟨28868302546758888610001653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153964280249380739253342149 28868302546758888610001653)
      ·
        refine ⟨2706403363758645807187655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28868302546758888610001653 2706403363758645807187655)
        ·
          refine ⟨4059605045637968710781483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706403363758645807187655 4059605045637968710781483)
          ·
            refine ⟨6089407568456953066172225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059605045637968710781483 6089407568456953066172225)
            ·
              refine ⟨4567055676342714799629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6089407568456953066172225 4567055676342714799629169)
              ·
                refine ⟨3425291757257036099721877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4567055676342714799629169 3425291757257036099721877)
                ·
                  refine ⟨160560551121423567174463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3425291757257036099721877 160560551121423567174463)
                  ·
                    rfl

theorem cell23_2814215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 6].length) (baseStart_2814215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814215 prefixEnd_2814215 := by exact prefixLift 2814215
  have htrace : WordTrace (prefixWord ++ tailWord_2814215) baseStart_2814215 baseEnd_2814215 := by
    simpa [prefixWord, tailWord_2814215, baseEnd_2814215] using wordTrace_append hprefix tailTrace_2814215
  have hstable : (prefixWord ++ tailWord_2814215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814215).length < 2 ^ (prefixWord ++ tailWord_2814215).sum := by decide
  have hdescent : baseEnd_2814215 < baseStart_2814215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814241 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2814241 : Nat := 118140960795 + 2814241 * 2 ^ 59
def prefixEnd_2814241 : Nat := 4983230072969 + 3 ^ 40 * 2814241 * 2
def baseEnd_2814241 : Nat := 481686103529943000948349

theorem tailTrace_2814241 : CollatzResearch.WordTrace tailWord_2814241 prefixEnd_2814241 481686103529943000948349 := by
  unfold tailWord_2814241
  simp only [CollatzResearch.WordTrace]
  refine ⟨102643801797492965942674577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68429201198328643961783051 102643801797492965942674577)
  ·
    refine ⟨76982851348119724457005933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102643801797492965942674577 76982851348119724457005933)
    ·
      refine ⟨28868569255544896671377225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76982851348119724457005933 28868569255544896671377225)
      ·
        refine ⟨21651426941658672503532919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28868569255544896671377225 21651426941658672503532919)
        ·
          refine ⟨32477140412488008755299379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21651426941658672503532919 32477140412488008755299379)
          ·
            refine ⟨48715710618732013132949069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32477140412488008755299379 48715710618732013132949069)
            ·
              refine ⟨18268391482024504924855901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48715710618732013132949069 18268391482024504924855901)
              ·
                refine ⟨6850646805759189346820963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18268391482024504924855901 6850646805759189346820963)
                ·
                  refine ⟨10275970208638784020231445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850646805759189346820963 10275970208638784020231445)
                  ·
                    refine ⟨481686103529943000948349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10275970208638784020231445 481686103529943000948349)
                    ·
                      rfl

theorem cell23_2814241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2814241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814241 prefixEnd_2814241 := by exact prefixLift 2814241
  have htrace : WordTrace (prefixWord ++ tailWord_2814241) baseStart_2814241 baseEnd_2814241 := by
    simpa [prefixWord, tailWord_2814241, baseEnd_2814241] using wordTrace_append hprefix tailTrace_2814241
  have hstable : (prefixWord ++ tailWord_2814241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814241).length < 2 ^ (prefixWord ++ tailWord_2814241).sum := by decide
  have hdescent : baseEnd_2814241 < baseStart_2814241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814265 : List Nat := [1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2814265 : Nat := 118140960795 + 2814265 * 2 ^ 59
def prefixEnd_2814265 : Nat := 4983230072969 + 3 ^ 40 * 2814265 * 2
def baseEnd_2814265 : Nat := 1445070634125536908944937

theorem tailTrace_2814265 : CollatzResearch.WordTrace tailWord_2814265 prefixEnd_2814265 1445070634125536908944937 := by
  unfold tailWord_2814265
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644677149406018041548249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68429784766270678694365499 102644677149406018041548249)
  ·
    refine ⟨76983507862054513531161187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102644677149406018041548249 76983507862054513531161187)
    ·
      refine ⟨115475261793081770296741781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76983507862054513531161187 115475261793081770296741781)
      ·
        refine ⟨5412902896550707982659771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115475261793081770296741781 5412902896550707982659771)
        ·
          refine ⟨8119354344826061973989657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412902896550707982659771 8119354344826061973989657)
          ·
            refine ⟨6089515758619546480492243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119354344826061973989657 6089515758619546480492243)
            ·
              refine ⟨9134273637929319720738365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089515758619546480492243 9134273637929319720738365)
              ·
                refine ⟨3425352614223494895276887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9134273637929319720738365 3425352614223494895276887)
                ·
                  refine ⟨5138028921335242342915331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425352614223494895276887 5138028921335242342915331)
                  ·
                    refine ⟨7707043382002863514372997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138028921335242342915331 7707043382002863514372997)
                    ·
                      refine ⟨1445070634125536908944937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7707043382002863514372997 1445070634125536908944937)
                      ·
                        rfl

theorem cell23_2814265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2814265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814265 prefixEnd_2814265 := by exact prefixLift 2814265
  have htrace : WordTrace (prefixWord ++ tailWord_2814265) baseStart_2814265 baseEnd_2814265 := by
    simpa [prefixWord, tailWord_2814265, baseEnd_2814265] using wordTrace_append hprefix tailTrace_2814265
  have hstable : (prefixWord ++ tailWord_2814265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814265).length < 2 ^ (prefixWord ++ tailWord_2814265).sum := by decide
  have hdescent : baseEnd_2814265 < baseStart_2814265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814292 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_2814292 : Nat := 118140960795 + 2814292 * 2 ^ 59
def prefixEnd_2814292 : Nat := 4983230072969 + 3 ^ 40 * 2814292 * 2
def baseEnd_2814292 : Nat := 481694832701069434435771

theorem tailTrace_2814292 : CollatzResearch.WordTrace tailWord_2814292 prefixEnd_2814292 481694832701069434435771 := by
  unfold tailWord_2814292
  simp only [CollatzResearch.WordTrace]
  refine ⟨51322830960154100826390565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68430441280205467768520753 51322830960154100826390565)
  ·
    refine ⟨9623030805028893904948231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51322830960154100826390565 9623030805028893904948231)
    ·
      refine ⟨14434546207543340857422347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623030805028893904948231 14434546207543340857422347)
      ·
        refine ⟨21651819311315011286133521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434546207543340857422347 21651819311315011286133521)
        ·
          refine ⟨16238864483486258464600141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21651819311315011286133521 16238864483486258464600141)
          ·
            refine ⟨6089574181307346924225053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16238864483486258464600141 6089574181307346924225053)
            ·
              refine ⟨2283590317990255096584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6089574181307346924225053 2283590317990255096584395)
              ·
                refine ⟨3425385476985382644876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283590317990255096584395 3425385476985382644876593)
                ·
                  refine ⟨2569039107739036983657445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3425385476985382644876593 2569039107739036983657445)
                  ·
                    refine ⟨481694832701069434435771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569039107739036983657445 481694832701069434435771)
                    ·
                      rfl

theorem cell23_2814292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_2814292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814292 prefixEnd_2814292 := by exact prefixLift 2814292
  have htrace : WordTrace (prefixWord ++ tailWord_2814292) baseStart_2814292 baseEnd_2814292 := by
    simpa [prefixWord, tailWord_2814292, baseEnd_2814292] using wordTrace_append hprefix tailTrace_2814292
  have hstable : (prefixWord ++ tailWord_2814292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814292).length < 2 ^ (prefixWord ++ tailWord_2814292).sum := by decide
  have hdescent : baseEnd_2814292 < baseStart_2814292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814316 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_2814316 : Nat := 118140960795 + 2814316 * 2 ^ 59
def prefixEnd_2814316 : Nat := 4983230072969 + 3 ^ 40 * 2814316 * 2
def baseEnd_2814316 : Nat := 1445096821638916209407203

theorem tailTrace_2814316 : CollatzResearch.WordTrace tailWord_2814316 prefixEnd_2814316 1445096821638916209407203 := by
  unfold tailWord_2814316
  simp only [CollatzResearch.WordTrace]
  refine ⟨51323268636110626875827401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68431024848147502501103201 51323268636110626875827401)
  ·
    refine ⟨38492451477082970156870551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51323268636110626875827401 38492451477082970156870551)
    ·
      refine ⟨57738677215624455235305827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38492451477082970156870551 57738677215624455235305827)
      ·
        refine ⟨86608015823436682852958741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57738677215624455235305827 86608015823436682852958741)
        ·
          refine ⟨4059750741723594508732441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86608015823436682852958741 4059750741723594508732441)
          ·
            refine ⟨3044813056292695881549331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059750741723594508732441 3044813056292695881549331)
            ·
              refine ⟨4567219584439043822323997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044813056292695881549331 4567219584439043822323997)
              ·
                refine ⟨1712707344164641433371499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567219584439043822323997 1712707344164641433371499)
                ·
                  refine ⟨2569061016246962150057249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712707344164641433371499 2569061016246962150057249)
                  ·
                    refine ⟨1926795762185221612542937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569061016246962150057249 1926795762185221612542937)
                    ·
                      refine ⟨1445096821638916209407203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926795762185221612542937 1445096821638916209407203)
                      ·
                        rfl

theorem cell23_2814316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_2814316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814316 prefixEnd_2814316 := by exact prefixLift 2814316
  have htrace : WordTrace (prefixWord ++ tailWord_2814316) baseStart_2814316 baseEnd_2814316 := by
    simpa [prefixWord, tailWord_2814316, baseEnd_2814316] using wordTrace_append hprefix tailTrace_2814316
  have hstable : (prefixWord ++ tailWord_2814316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814316).length < 2 ^ (prefixWord ++ tailWord_2814316).sum := by decide
  have hdescent : baseEnd_2814316 < baseStart_2814316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814321 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2814321 : Nat := 118140960795 + 2814321 * 2 ^ 59
def prefixEnd_2814321 : Nat := 4983230072969 + 3 ^ 40 * 2814321 * 2
def baseEnd_2814321 : Nat := 1445099389042188689844679

theorem tailTrace_2814321 : CollatzResearch.WordTrace tailWord_2814321 prefixEnd_2814321 1445099389042188689844679 := by
  unfold tailWord_2814321
  simp only [CollatzResearch.WordTrace]
  refine ⟨102646719637203139605586817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68431146424802093070391211 102646719637203139605586817)
  ·
    refine ⟨76985039727902354704190113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102646719637203139605586817 76985039727902354704190113)
    ·
      refine ⟨57738779795926766028142585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76985039727902354704190113 57738779795926766028142585)
      ·
        refine ⟨43304084846945074521106939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57738779795926766028142585 43304084846945074521106939)
        ·
          refine ⟨64956127270417611781660409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43304084846945074521106939 64956127270417611781660409)
          ·
            refine ⟨48717095452813208836245307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64956127270417611781660409 48717095452813208836245307)
            ·
              refine ⟨73075643179219813254367961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48717095452813208836245307 73075643179219813254367961)
              ·
                refine ⟨54806732384414859940775971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73075643179219813254367961 54806732384414859940775971)
                ·
                  refine ⟨82210098576622289911163957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54806732384414859940775971 82210098576622289911163957)
                  ·
                    refine ⟨7707196741558339679171621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82210098576622289911163957 7707196741558339679171621)
                    ·
                      refine ⟨1445099389042188689844679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7707196741558339679171621 1445099389042188689844679)
                      ·
                        rfl

theorem cell23_2814321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2814321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814321 prefixEnd_2814321 := by exact prefixLift 2814321
  have htrace : WordTrace (prefixWord ++ tailWord_2814321) baseStart_2814321 baseEnd_2814321 := by
    simpa [prefixWord, tailWord_2814321, baseEnd_2814321] using wordTrace_append hprefix tailTrace_2814321
  have hstable : (prefixWord ++ tailWord_2814321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814321).length < 2 ^ (prefixWord ++ tailWord_2814321).sum := by decide
  have hdescent : baseEnd_2814321 < baseStart_2814321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814341 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_2814341 : Nat := 118140960795 + 2814341 * 2 ^ 59
def prefixEnd_2814341 : Nat := 4983230072969 + 3 ^ 40 * 2814341 * 2
def baseEnd_2814341 : Nat := 1445109658655278611594587

theorem tailTrace_2814341 : CollatzResearch.WordTrace tailWord_2814341 prefixEnd_2814341 1445109658655278611594587 := by
  unfold tailWord_2814341
  simp only [CollatzResearch.WordTrace]
  refine ⟨102647449097130683021314877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68431632731420455347543251 102647449097130683021314877)
  ·
    refine ⟨38492793411424006132993079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102647449097130683021314877 38492793411424006132993079)
    ·
      refine ⟨57739190117136009199489619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38492793411424006132993079 57739190117136009199489619)
      ·
        refine ⟨86608785175704013799234429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57739190117136009199489619 86608785175704013799234429)
        ·
          refine ⟨32478294440889005174712911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86608785175704013799234429 32478294440889005174712911)
          ·
            refine ⟨48717441661333507762069367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32478294440889005174712911 48717441661333507762069367)
            ·
              refine ⟨73076162492000261643104051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48717441661333507762069367 73076162492000261643104051)
              ·
                refine ⟨109614243738000392464656077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73076162492000261643104051 109614243738000392464656077)
                ·
                  refine ⟨41105341401750147174246029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109614243738000392464656077 41105341401750147174246029)
                  ·
                    refine ⟨15414503025656305190342261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41105341401750147174246029 15414503025656305190342261)
                    ·
                      refine ⟨1445109658655278611594587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15414503025656305190342261 1445109658655278611594587)
                      ·
                        rfl

theorem cell23_2814341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_2814341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814341 prefixEnd_2814341 := by exact prefixLift 2814341
  have htrace : WordTrace (prefixWord ++ tailWord_2814341) baseStart_2814341 baseEnd_2814341 := by
    simpa [prefixWord, tailWord_2814341, baseEnd_2814341] using wordTrace_append hprefix tailTrace_2814341
  have hstable : (prefixWord ++ tailWord_2814341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814341).length < 2 ^ (prefixWord ++ tailWord_2814341).sum := by decide
  have hdescent : baseEnd_2814341 < baseStart_2814341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814361 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 9]
def baseStart_2814361 : Nat := 118140960795 + 2814361 * 2 ^ 59
def prefixEnd_2814361 : Nat := 4983230072969 + 3 ^ 40 * 2814361 * 2
def baseEnd_2814361 : Nat := 160568880918707614816055

theorem tailTrace_2814361 : CollatzResearch.WordTrace tailWord_2814361 prefixEnd_2814361 160568880918707614816055 := by
  unfold tailWord_2814361
  simp only [CollatzResearch.WordTrace]
  refine ⟨102648178557058226437042937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68432119038038817624695291 102648178557058226437042937)
  ·
    refine ⟨76986133917793669827782203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102648178557058226437042937 76986133917793669827782203)
    ·
      refine ⟨115479200876690504741673305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76986133917793669827782203 115479200876690504741673305)
      ·
        refine ⟨86609400657517878556254979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115479200876690504741673305 86609400657517878556254979)
        ·
          refine ⟨129914100986276817834382469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86609400657517878556254979 129914100986276817834382469)
          ·
            refine ⟨24358893934926903343946713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129914100986276817834382469 24358893934926903343946713)
            ·
              refine ⟨18269170451195177507960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24358893934926903343946713 18269170451195177507960035)
              ·
                refine ⟨27403755676792766261940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18269170451195177507960035 27403755676792766261940053)
                ·
                  refine ⟨160568880918707614816055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27403755676792766261940053 160568880918707614816055)
                  ·
                    rfl

theorem cell23_2814361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_2814361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814361 prefixEnd_2814361 := by exact prefixLift 2814361
  have htrace : WordTrace (prefixWord ++ tailWord_2814361) baseStart_2814361 baseEnd_2814361 := by
    simpa [prefixWord, tailWord_2814361, baseEnd_2814361] using wordTrace_append hprefix tailTrace_2814361
  have hstable : (prefixWord ++ tailWord_2814361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814361).length < 2 ^ (prefixWord ++ tailWord_2814361).sum := by decide
  have hdescent : baseEnd_2814361 < baseStart_2814361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814376 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2814376 : Nat := 118140960795 + 2814376 * 2 ^ 59
def prefixEnd_2814376 : Nat := 4983230072969 + 3 ^ 40 * 2814376 * 2
def baseEnd_2814376 : Nat := 1445127630478185974656927

theorem tailTrace_2814376 : CollatzResearch.WordTrace tailWord_2814376 prefixEnd_2814376 1445127630478185974656927 := by
  unfold tailWord_2814376
  simp only [CollatzResearch.WordTrace]
  refine ⟨51324362826001941999419491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68432483768002589332559321 51324362826001941999419491)
  ·
    refine ⟨76986544239002912999129237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51324362826001941999419491 76986544239002912999129237)
    ·
      refine ⟨3608744261203261546834183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76986544239002912999129237 3608744261203261546834183)
      ·
        refine ⟨5413116391804892320251275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608744261203261546834183 5413116391804892320251275)
        ·
          refine ⟨8119674587707338480376913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413116391804892320251275 8119674587707338480376913)
          ·
            refine ⟨6089755940780503860282685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119674587707338480376913 6089755940780503860282685)
            ·
              refine ⟨2283658477792688947606007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6089755940780503860282685 2283658477792688947606007)
              ·
                refine ⟨3425487716689033421409011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283658477792688947606007 3425487716689033421409011)
                ·
                  refine ⟨5138231575033550132113517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425487716689033421409011 5138231575033550132113517)
                  ·
                    refine ⟨1926836840637581299542569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5138231575033550132113517 1926836840637581299542569)
                    ·
                      refine ⟨1445127630478185974656927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1926836840637581299542569 1445127630478185974656927)
                      ·
                        rfl

theorem cell23_2814376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2814376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814376 prefixEnd_2814376 := by exact prefixLift 2814376
  have htrace : WordTrace (prefixWord ++ tailWord_2814376) baseStart_2814376 baseEnd_2814376 := by
    simpa [prefixWord, tailWord_2814376, baseEnd_2814376] using wordTrace_append hprefix tailTrace_2814376
  have hstable : (prefixWord ++ tailWord_2814376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814376).length < 2 ^ (prefixWord ++ tailWord_2814376).sum := by decide
  have hdescent : baseEnd_2814376 < baseStart_2814376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814465 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2814465 : Nat := 118140960795 + 2814465 * 2 ^ 59
def prefixEnd_2814465 : Nat := 4983230072969 + 3 ^ 40 * 2814465 * 2
def baseEnd_2814465 : Nat := 1445173330256436126444017

theorem tailTrace_2814465 : CollatzResearch.WordTrace tailWord_2814465 prefixEnd_2814465 1445173330256436126444017 := by
  unfold tailWord_2814465
  simp only [CollatzResearch.WordTrace]
  refine ⟨102651971748681452198828849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68434647832454301465885899 102651971748681452198828849)
  ·
    refine ⟨76988978811511089149121637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102651971748681452198828849 76988978811511089149121637)
    ·
      refine ⟨14435433527158329215460307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76988978811511089149121637 14435433527158329215460307)
      ·
        refine ⟨21653150290737493823190461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14435433527158329215460307 21653150290737493823190461)
        ·
          refine ⟨8119931359026560183696423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21653150290737493823190461 8119931359026560183696423)
          ·
            refine ⟨12179897038539840275544635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119931359026560183696423 12179897038539840275544635)
            ·
              refine ⟨18269845557809760413316953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12179897038539840275544635 18269845557809760413316953)
              ·
                refine ⟨13702384168357320309987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18269845557809760413316953 13702384168357320309987715)
                ·
                  refine ⟨20553576252535980464981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13702384168357320309987715 20553576252535980464981573)
                  ·
                    refine ⟨3853795547350496337184045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20553576252535980464981573 3853795547350496337184045)
                    ·
                      refine ⟨1445173330256436126444017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853795547350496337184045 1445173330256436126444017)
                      ·
                        rfl

theorem cell23_2814465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2814465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814465 prefixEnd_2814465 := by exact prefixLift 2814465
  have htrace : WordTrace (prefixWord ++ tailWord_2814465) baseStart_2814465 baseEnd_2814465 := by
    simpa [prefixWord, tailWord_2814465, baseEnd_2814465] using wordTrace_append hprefix tailTrace_2814465
  have hstable : (prefixWord ++ tailWord_2814465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814465).length < 2 ^ (prefixWord ++ tailWord_2814465).sum := by decide
  have hdescent : baseEnd_2814465 < baseStart_2814465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814506 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 1, 4]
def baseStart_2814506 : Nat := 118140960795 + 2814506 * 2 ^ 59
def prefixEnd_2814506 : Nat := 4983230072969 + 3 ^ 40 * 2814506 * 2
def baseEnd_2814506 : Nat := 481731460987756822010443

theorem tailTrace_2814506 : CollatzResearch.WordTrace tailWord_2814506 prefixEnd_2814506 481731460987756822010443 := by
  unfold tailWord_2814506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663366785383229050267843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68435644761021944134047581 25663366785383229050267843)
  ·
    refine ⟨38495050178074843575401765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25663366785383229050267843 38495050178074843575401765)
    ·
      refine ⟨7217821908389033170387831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38495050178074843575401765 7217821908389033170387831)
      ·
        refine ⟨10826732862583549755581747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217821908389033170387831 10826732862583549755581747)
        ·
          refine ⟨16240099293875324633372621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10826732862583549755581747 16240099293875324633372621)
          ·
            refine ⟨6090037235203246737514733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16240099293875324633372621 6090037235203246737514733)
            ·
              refine ⟨2283763963201217526568025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6090037235203246737514733 2283763963201217526568025)
              ·
                refine ⟨1712822972400913144926019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283763963201217526568025 1712822972400913144926019)
                ·
                  refine ⟨2569234458601369717389029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712822972400913144926019 2569234458601369717389029)
                  ·
                    refine ⟨481731460987756822010443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569234458601369717389029 481731460987756822010443)
                    ·
                      rfl

theorem cell23_2814506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_2814506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814506 prefixEnd_2814506 := by exact prefixLift 2814506
  have htrace : WordTrace (prefixWord ++ tailWord_2814506) baseStart_2814506 baseEnd_2814506 := by
    simpa [prefixWord, tailWord_2814506, baseEnd_2814506] using wordTrace_append hprefix tailTrace_2814506
  have hstable : (prefixWord ++ tailWord_2814506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814506).length < 2 ^ (prefixWord ++ tailWord_2814506).sum := by decide
  have hdescent : baseEnd_2814506 < baseStart_2814506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814512 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_2814512 : Nat := 118140960795 + 2814512 * 2 ^ 59
def prefixEnd_2814512 : Nat := 4983230072969 + 3 ^ 40 * 2814512 * 2
def baseEnd_2814512 : Nat := 1445197463847197442556301

theorem tailTrace_2814512 : CollatzResearch.WordTrace tailWord_2814512 prefixEnd_2814512 1445197463847197442556301 := by
  unfold tailWord_2814512
  simp only [CollatzResearch.WordTrace]
  refine ⟨51326842989755589612894895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68435790653007452817193193 51326842989755589612894895)
  ·
    refine ⟨76990264484633384419342343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51326842989755589612894895 76990264484633384419342343)
    ·
      refine ⟨115485396726950076629013515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76990264484633384419342343 115485396726950076629013515)
      ·
        refine ⟨173228095090425114943520273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115485396726950076629013515 173228095090425114943520273)
        ·
          refine ⟨129921071317818836207640205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173228095090425114943520273 129921071317818836207640205)
          ·
            refine ⟨48720401744182063577865077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129921071317818836207640205 48720401744182063577865077)
            ·
              refine ⟨4567537663517068460424851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48720401744182063577865077 4567537663517068460424851)
              ·
                refine ⟨6851306495275602690637277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567537663517068460424851 6851306495275602690637277)
                ·
                  refine ⟨2569239935728351008988979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6851306495275602690637277 2569239935728351008988979)
                  ·
                    refine ⟨3853859903592526513483469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2569239935728351008988979 3853859903592526513483469)
                    ·
                      refine ⟨1445197463847197442556301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3853859903592526513483469 1445197463847197442556301)
                      ·
                        rfl

theorem cell23_2814512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_2814512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814512 prefixEnd_2814512 := by exact prefixLift 2814512
  have htrace : WordTrace (prefixWord ++ tailWord_2814512) baseStart_2814512 baseEnd_2814512 := by
    simpa [prefixWord, tailWord_2814512, baseEnd_2814512] using wordTrace_append hprefix tailTrace_2814512
  have hstable : (prefixWord ++ tailWord_2814512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814512).length < 2 ^ (prefixWord ++ tailWord_2814512).sum := by decide
  have hdescent : baseEnd_2814512 < baseStart_2814512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814545 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2814545 : Nat := 118140960795 + 2814545 * 2 ^ 59
def prefixEnd_2814545 : Nat := 4983230072969 + 3 ^ 40 * 2814545 * 2
def baseEnd_2814545 : Nat := 481738136236265271147883

theorem tailTrace_2814545 : CollatzResearch.WordTrace tailWord_2814545 prefixEnd_2814545 481738136236265271147883 := by
  unfold tailWord_2814545
  simp only [CollatzResearch.WordTrace]
  refine ⟨102654889588391625861741089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68436593058927750574494059 102654889588391625861741089)
  ·
    refine ⟨76991167191293719396305817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102654889588391625861741089 76991167191293719396305817)
    ·
      refine ⟨57743375393470289547229363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76991167191293719396305817 57743375393470289547229363)
      ·
        refine ⟨86615063090205434320844045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57743375393470289547229363 86615063090205434320844045)
        ·
          refine ⟨32480648658827037870316517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86615063090205434320844045 32480648658827037870316517)
          ·
            refine ⟨6090121623530069600684347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32480648658827037870316517 6090121623530069600684347)
            ·
              refine ⟨9135182435295104401026521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090121623530069600684347 9135182435295104401026521)
              ·
                refine ⟨6851386826471328300769891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9135182435295104401026521 6851386826471328300769891)
                ·
                  refine ⟨10277080239706992451154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6851386826471328300769891 10277080239706992451154837)
                  ·
                    refine ⟨481738136236265271147883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10277080239706992451154837 481738136236265271147883)
                    ·
                      rfl

theorem cell23_2814545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2814545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814545 prefixEnd_2814545 := by exact prefixLift 2814545
  have htrace : WordTrace (prefixWord ++ tailWord_2814545) baseStart_2814545 baseEnd_2814545 := by
    simpa [prefixWord, tailWord_2814545, baseEnd_2814545] using wordTrace_append hprefix tailTrace_2814545
  have hstable : (prefixWord ++ tailWord_2814545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814545).length < 2 ^ (prefixWord ++ tailWord_2814545).sum := by decide
  have hdescent : baseEnd_2814545 < baseStart_2814545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814693 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2814693 : Nat := 118140960795 + 2814693 * 2 ^ 59
def prefixEnd_2814693 : Nat := 4983230072969 + 3 ^ 40 * 2814693 * 2
def baseEnd_2814693 : Nat := 1445290403845661234392969

theorem tailTrace_2814693 : CollatzResearch.WordTrace tailWord_2814693 prefixEnd_2814693 1445290403845661234392969 := by
  unfold tailWord_2814693
  simp only [CollatzResearch.WordTrace]
  refine ⟨102660287591855447138128733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68440191727903631425419155 102660287591855447138128733)
  ·
    refine ⟨38497607846945792676798275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102660287591855447138128733 38497607846945792676798275)
    ·
      refine ⟨57746411770418689015197413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38497607846945792676798275 57746411770418689015197413)
      ·
        refine ⟨10827452206953504190349515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57746411770418689015197413 10827452206953504190349515)
        ·
          refine ⟨16241178310430256285524273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10827452206953504190349515 16241178310430256285524273)
          ·
            refine ⟨12180883732822692214143205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16241178310430256285524273 12180883732822692214143205)
            ·
              refine ⟨2283915699904254790151851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12180883732822692214143205 2283915699904254790151851)
              ·
                refine ⟨3425873549856382185227777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283915699904254790151851 3425873549856382185227777)
                ·
                  refine ⟨2569405162392286638920833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3425873549856382185227777 2569405162392286638920833)
                  ·
                    refine ⟨1927053871794214979190625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569405162392286638920833 1927053871794214979190625)
                    ·
                      refine ⟨1445290403845661234392969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1927053871794214979190625 1445290403845661234392969)
                      ·
                        rfl

theorem cell23_2814693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2814693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814693 prefixEnd_2814693 := by exact prefixLift 2814693
  have htrace : WordTrace (prefixWord ++ tailWord_2814693) baseStart_2814693 baseEnd_2814693 := by
    simpa [prefixWord, tailWord_2814693, baseEnd_2814693] using wordTrace_append hprefix tailTrace_2814693
  have hstable : (prefixWord ++ tailWord_2814693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814693).length < 2 ^ (prefixWord ++ tailWord_2814693).sum := by decide
  have hdescent : baseEnd_2814693 < baseStart_2814693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814705 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2814705 : Nat := 118140960795 + 2814705 * 2 ^ 59
def prefixEnd_2814705 : Nat := 4983230072969 + 3 ^ 40 * 2814705 * 2
def baseEnd_2814705 : Nat := 1445296565613515187442913

theorem tailTrace_2814705 : CollatzResearch.WordTrace tailWord_2814705 prefixEnd_2814705 1445296565613515187442913 := by
  unfold tailWord_2814705
  simp only [CollatzResearch.WordTrace]
  refine ⟨102660725267811973187565569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68440483511874648791710379 102660725267811973187565569)
  ·
    refine ⟨76995543950858979890674177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102660725267811973187565569 76995543950858979890674177)
    ·
      refine ⟨57746657963144234918005633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76995543950858979890674177 57746657963144234918005633)
      ·
        refine ⟨43309993472358176188504225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57746657963144234918005633 43309993472358176188504225)
        ·
          refine ⟨32482495104268632141378169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43309993472358176188504225 32482495104268632141378169)
          ·
            refine ⟨24361871328201474106033627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32482495104268632141378169 24361871328201474106033627)
            ·
              refine ⟨36542806992302211159050441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24361871328201474106033627 36542806992302211159050441)
              ·
                refine ⟨27407105244226658369287831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36542806992302211159050441 27407105244226658369287831)
                ·
                  refine ⟨41110657866339987553931747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27407105244226658369287831 41110657866339987553931747)
                  ·
                    refine ⟨61665986799509981330897621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41110657866339987553931747 61665986799509981330897621)
                    ·
                      refine ⟨1445296565613515187442913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61665986799509981330897621 1445296565613515187442913)
                      ·
                        rfl

theorem cell23_2814705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2814705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814705 prefixEnd_2814705 := by exact prefixLift 2814705
  have htrace : WordTrace (prefixWord ++ tailWord_2814705) baseStart_2814705 baseEnd_2814705 := by
    simpa [prefixWord, tailWord_2814705, baseEnd_2814705] using wordTrace_append hprefix tailTrace_2814705
  have hstable : (prefixWord ++ tailWord_2814705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814705).length < 2 ^ (prefixWord ++ tailWord_2814705).sum := by decide
  have hdescent : baseEnd_2814705 < baseStart_2814705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814712 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 2, 5]
def baseStart_2814712 : Nat := 118140960795 + 2814712 * 2 ^ 59
def prefixEnd_2814712 : Nat := 4983230072969 + 3 ^ 40 * 2814712 * 2
def baseEnd_2814712 : Nat := 481766719992698886685127

theorem tailTrace_2814712 : CollatzResearch.WordTrace tailWord_2814712 prefixEnd_2814712 481766719992698886685127 := by
  unfold tailWord_2814712
  simp only [CollatzResearch.WordTrace]
  refine ⟨51330490289393306691535195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68440653719191075588713593 51330490289393306691535195)
  ·
    refine ⟨76995735434089960037302793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51330490289393306691535195 76995735434089960037302793)
    ·
      refine ⟨57746801575567470027977095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76995735434089960037302793 57746801575567470027977095)
      ·
        refine ⟨86620202363351205041965643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57746801575567470027977095 86620202363351205041965643)
        ·
          refine ⟨129930303545026807562948465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86620202363351205041965643 129930303545026807562948465)
          ·
            refine ⟨97447727658770105672211349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129930303545026807562948465 97447727658770105672211349)
            ·
              refine ⟨4567862234004848703384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97447727658770105672211349 4567862234004848703384907)
              ·
                refine ⟨6851793351007273055077361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567862234004848703384907 6851793351007273055077361)
                ·
                  refine ⟨5138845013255454791308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851793351007273055077361 5138845013255454791308021)
                  ·
                    refine ⟨481766719992698886685127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5138845013255454791308021 481766719992698886685127)
                    ·
                      rfl

theorem cell23_2814712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_2814712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814712 prefixEnd_2814712 := by exact prefixLift 2814712
  have htrace : WordTrace (prefixWord ++ tailWord_2814712) baseStart_2814712 baseEnd_2814712 := by
    simpa [prefixWord, tailWord_2814712, baseEnd_2814712] using wordTrace_append hprefix tailTrace_2814712
  have hstable : (prefixWord ++ tailWord_2814712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814712).length < 2 ^ (prefixWord ++ tailWord_2814712).sum := by decide
  have hdescent : baseEnd_2814712 < baseStart_2814712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_2814715 : Nat := 118140960795 + 2814715 * 2 ^ 59
def prefixEnd_2814715 : Nat := 4983230072969 + 3 ^ 40 * 2814715 * 2
def baseEnd_2814715 : Nat := 1445301700420060148317867

theorem tailTrace_2814715 : CollatzResearch.WordTrace tailWord_2814715 prefixEnd_2814715 1445301700420060148317867 := by
  unfold tailWord_2814715
  simp only [CollatzResearch.WordTrace]
  refine ⟨102661089997775744895429599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68440726665183829930286399 102661089997775744895429599)
  ·
    refine ⟨153991634996663617343144399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102661089997775744895429599 153991634996663617343144399)
    ·
      refine ⟨230987452494995426014716599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153991634996663617343144399 230987452494995426014716599)
      ·
        refine ⟨346481178742493139022074899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230987452494995426014716599 346481178742493139022074899)
        ·
          refine ⟨519721768113739708533112349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346481178742493139022074899 519721768113739708533112349)
          ·
            refine ⟨194895663042652390699917131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519721768113739708533112349 194895663042652390699917131)
            ·
              refine ⟨292343494563978586049875697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194895663042652390699917131 292343494563978586049875697)
              ·
                refine ⟨219257620922983939537406773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292343494563978586049875697 219257620922983939537406773)
                ·
                  refine ⟨20555401961529744331631885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219257620922983939537406773 20555401961529744331631885)
                  ·
                    refine ⟨7708275735573654124361957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20555401961529744331631885 7708275735573654124361957)
                    ·
                      refine ⟨1445301700420060148317867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7708275735573654124361957 1445301700420060148317867)
                      ·
                        rfl

theorem cell23_2814715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_2814715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814715 prefixEnd_2814715 := by exact prefixLift 2814715
  have htrace : WordTrace (prefixWord ++ tailWord_2814715) baseStart_2814715 baseEnd_2814715 := by
    simpa [prefixWord, tailWord_2814715, baseEnd_2814715] using wordTrace_append hprefix tailTrace_2814715
  have hstable : (prefixWord ++ tailWord_2814715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814715).length < 2 ^ (prefixWord ++ tailWord_2814715).sum := by decide
  have hdescent : baseEnd_2814715 < baseStart_2814715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814735 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_2814735 : Nat := 118140960795 + 2814735 * 2 ^ 59
def prefixEnd_2814735 : Nat := 4983230072969 + 3 ^ 40 * 2814735 * 2
def baseEnd_2814735 : Nat := 1445311970033150070067775

theorem tailTrace_2814735 : CollatzResearch.WordTrace tailWord_2814735 prefixEnd_2814735 1445311970033150070067775 := by
  unfold tailWord_2814735
  simp only [CollatzResearch.WordTrace]
  refine ⟨102661819457703288311157659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68441212971802192207438439 102661819457703288311157659)
  ·
    refine ⟨153992729186554932466736489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102661819457703288311157659 153992729186554932466736489)
    ·
      refine ⟨115494546889916199350052367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153992729186554932466736489 115494546889916199350052367)
      ·
        refine ⟨173241820334874299025078551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115494546889916199350052367 173241820334874299025078551)
        ·
          refine ⟨259862730502311448537617827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173241820334874299025078551 259862730502311448537617827)
          ·
            refine ⟨389794095753467172806426741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259862730502311448537617827 389794095753467172806426741)
            ·
              refine ⟨36543196476887547450602507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389794095753467172806426741 36543196476887547450602507)
              ·
                refine ⟨54814794715331321175903761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36543196476887547450602507 54814794715331321175903761)
                ·
                  refine ⟨41111096036498490881927821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54814794715331321175903761 41111096036498490881927821)
                  ·
                    refine ⟨15416661013686934080722933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41111096036498490881927821 15416661013686934080722933)
                    ·
                      refine ⟨1445311970033150070067775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15416661013686934080722933 1445311970033150070067775)
                      ·
                        rfl

theorem cell23_2814735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_2814735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814735 prefixEnd_2814735 := by exact prefixLift 2814735
  have htrace : WordTrace (prefixWord ++ tailWord_2814735) baseStart_2814735 baseEnd_2814735 := by
    simpa [prefixWord, tailWord_2814735, baseEnd_2814735] using wordTrace_append hprefix tailTrace_2814735
  have hstable : (prefixWord ++ tailWord_2814735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814735).length < 2 ^ (prefixWord ++ tailWord_2814735).sum := by decide
  have hdescent : baseEnd_2814735 < baseStart_2814735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814745 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2814745 : Nat := 118140960795 + 2814745 * 2 ^ 59
def prefixEnd_2814745 : Nat := 4983230072969 + 3 ^ 40 * 2814745 * 2
def baseEnd_2814745 : Nat := 1445317104839695030942729

theorem tailTrace_2814745 : CollatzResearch.WordTrace tailWord_2814745 prefixEnd_2814745 1445317104839695030942729 := by
  unfold tailWord_2814745
  simp only [CollatzResearch.WordTrace]
  refine ⟨102662184187667060019021689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68441456125111373346014459 102662184187667060019021689)
  ·
    refine ⟨76996638140750295014266267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102662184187667060019021689 76996638140750295014266267)
    ·
      refine ⟨115494957211125442521399401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76996638140750295014266267 115494957211125442521399401)
      ·
        refine ⟨86621217908344081891049551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115494957211125442521399401 86621217908344081891049551)
        ·
          refine ⟨129931826862516122836574327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86621217908344081891049551 129931826862516122836574327)
          ·
            refine ⟨194897740293774184254861491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129931826862516122836574327 194897740293774184254861491)
            ·
              refine ⟨292346610440661276382292237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194897740293774184254861491 292346610440661276382292237)
              ·
                refine ⟨109629978915247978643359589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292346610440661276382292237 109629978915247978643359589)
                ·
                  refine ⟨20555621046608995995629923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109629978915247978643359589 20555621046608995995629923)
                  ·
                    refine ⟨30833431569913493993444885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20555621046608995995629923 30833431569913493993444885)
                    ·
                      refine ⟨1445317104839695030942729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30833431569913493993444885 1445317104839695030942729)
                      ·
                        rfl

theorem cell23_2814745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2814745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814745 prefixEnd_2814745 := by exact prefixLift 2814745
  have htrace : WordTrace (prefixWord ++ tailWord_2814745) baseStart_2814745 baseEnd_2814745 := by
    simpa [prefixWord, tailWord_2814745, baseEnd_2814745] using wordTrace_append hprefix tailTrace_2814745
  have hstable : (prefixWord ++ tailWord_2814745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814745).length < 2 ^ (prefixWord ++ tailWord_2814745).sum := by decide
  have hdescent : baseEnd_2814745 < baseStart_2814745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814755 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 10]
def baseStart_2814755 : Nat := 118140960795 + 2814755 * 2 ^ 59
def prefixEnd_2814755 : Nat := 4983230072969 + 3 ^ 40 * 2814755 * 2
def baseEnd_2814755 : Nat := 160591359960693332424187

theorem tailTrace_2814755 : CollatzResearch.WordTrace tailWord_2814755 prefixEnd_2814755 160591359960693332424187 := by
  unfold tailWord_2814755
  simp only [CollatzResearch.WordTrace]
  refine ⟨102662548917630831726885719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68441699278420554484590479 102662548917630831726885719)
  ·
    refine ⟨153993823376446247590328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102662548917630831726885719 153993823376446247590328579)
    ·
      refine ⟨230990735064669371385492869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153993823376446247590328579 230990735064669371385492869)
      ·
        refine ⟨43310762824625507134779913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230990735064669371385492869 43310762824625507134779913)
        ·
          refine ⟨32483072118469130351084935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43310762824625507134779913 32483072118469130351084935)
          ·
            refine ⟨48724608177703695526627403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32483072118469130351084935 48724608177703695526627403)
            ·
              refine ⟨73086912266555543289941105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48724608177703695526627403 73086912266555543289941105)
              ·
                refine ⟨54815184199916657467455829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73086912266555543289941105 54815184199916657467455829)
                ·
                  refine ⟨160591359960693332424187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54815184199916657467455829 160591359960693332424187)
                  ·
                    rfl

theorem cell23_2814755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 10].length) (baseStart_2814755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814755 prefixEnd_2814755 := by exact prefixLift 2814755
  have htrace : WordTrace (prefixWord ++ tailWord_2814755) baseStart_2814755 baseEnd_2814755 := by
    simpa [prefixWord, tailWord_2814755, baseEnd_2814755] using wordTrace_append hprefix tailTrace_2814755
  have hstable : (prefixWord ++ tailWord_2814755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814755).length < 2 ^ (prefixWord ++ tailWord_2814755).sum := by decide
  have hdescent : baseEnd_2814755 < baseStart_2814755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814766 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_2814766 : Nat := 118140960795 + 2814766 * 2 ^ 59
def prefixEnd_2814766 : Nat := 4983230072969 + 3 ^ 40 * 2814766 * 2
def baseEnd_2814766 : Nat := 1445327887933439448780133

theorem tailTrace_2814766 : CollatzResearch.WordTrace tailWord_2814766 prefixEnd_2814766 1445327887933439448780133 := by
  unfold tailWord_2814766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832868765073872575692019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68441966747060653737024101 12832868765073872575692019)
  ·
    refine ⟨19249303147610808863538029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12832868765073872575692019 19249303147610808863538029)
    ·
      refine ⟨7218488680354053323826761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19249303147610808863538029 7218488680354053323826761)
      ·
        refine ⟨5413866510265539992870071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7218488680354053323826761 5413866510265539992870071)
        ·
          refine ⟨8120799765398309989305107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413866510265539992870071 8120799765398309989305107)
          ·
            refine ⟨12181199648097464983957661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120799765398309989305107 12181199648097464983957661)
            ·
              refine ⟨4567949868036549368984123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12181199648097464983957661 4567949868036549368984123)
              ·
                refine ⟨6851924802054824053476185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567949868036549368984123 6851924802054824053476185)
                ·
                  refine ⟨5138943601541118040107139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851924802054824053476185 5138943601541118040107139)
                  ·
                    refine ⟨7708415402311677060160709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138943601541118040107139 7708415402311677060160709)
                    ·
                      refine ⟨1445327887933439448780133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7708415402311677060160709 1445327887933439448780133)
                      ·
                        rfl

theorem cell23_2814766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_2814766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814766 prefixEnd_2814766 := by exact prefixLift 2814766
  have htrace : WordTrace (prefixWord ++ tailWord_2814766) baseStart_2814766 baseEnd_2814766 := by
    simpa [prefixWord, tailWord_2814766, baseEnd_2814766] using wordTrace_append hprefix tailTrace_2814766
  have hstable : (prefixWord ++ tailWord_2814766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814766).length < 2 ^ (prefixWord ++ tailWord_2814766).sum := by decide
  have hdescent : baseEnd_2814766 < baseStart_2814766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814776 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 1, 4]
def baseStart_2814776 : Nat := 118140960795 + 2814776 * 2 ^ 59
def prefixEnd_2814776 : Nat := 4983230072969 + 3 ^ 40 * 2814776 * 2
def baseEnd_2814776 : Nat := 481777674246661469885029

theorem tailTrace_2814776 : CollatzResearch.WordTrace tailWord_2814776 prefixEnd_2814776 481777674246661469885029 := by
  unfold tailWord_2814776
  simp only [CollatzResearch.WordTrace]
  refine ⟨51331657425277376156700091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68442209900369834875600121 51331657425277376156700091)
  ·
    refine ⟨76997486137916064235050137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51331657425277376156700091 76997486137916064235050137)
    ·
      refine ⟨57748114603437048176287603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76997486137916064235050137 57748114603437048176287603)
      ·
        refine ⟨86622171905155572264431405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57748114603437048176287603 86622171905155572264431405)
        ·
          refine ⟨32483314464433339599161777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86622171905155572264431405 32483314464433339599161777)
          ·
            refine ⟨24362485848325004699371333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32483314464433339599161777 24362485848325004699371333)
            ·
              refine ⟨4567966096560938381132125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24362485848325004699371333 4567966096560938381132125)
              ·
                refine ⟨1712987286210351892924547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567966096560938381132125 1712987286210351892924547)
                ·
                  refine ⟨2569480929315527839386821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712987286210351892924547 2569480929315527839386821)
                  ·
                    refine ⟨481777674246661469885029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2569480929315527839386821 481777674246661469885029)
                    ·
                      rfl

theorem cell23_2814776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_2814776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2814776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2814776 prefixEnd_2814776 := by exact prefixLift 2814776
  have htrace : WordTrace (prefixWord ++ tailWord_2814776) baseStart_2814776 baseEnd_2814776 := by
    simpa [prefixWord, tailWord_2814776, baseEnd_2814776] using wordTrace_append hprefix tailTrace_2814776
  have hstable : (prefixWord ++ tailWord_2814776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814776).length < 2 ^ (prefixWord ++ tailWord_2814776).sum := by decide
  have hdescent : baseEnd_2814776 < baseStart_2814776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
