import V185TrunkScan23Chunk0143

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_851055 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_851055 : Nat := 118140960795 + 851055 * 2 ^ 59
def prefixEnd_851055 : Nat := 4983230072969 + 3 ^ 40 * 851055 * 2
def baseEnd_851055 : Nat := 437000278412272977098575

theorem tailTrace_851055 : CollatzResearch.WordTrace tailWord_851055 prefixEnd_851055 437000278412272977098575 := by
  unfold tailWord_851055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31040525931780558467314619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20693683954520372311543079 31040525931780558467314619)
  ·
    refine ⟨46560788897670837700971929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31040525931780558467314619 46560788897670837700971929)
    ·
      refine ⟨34920591673253128275728947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46560788897670837700971929 34920591673253128275728947)
      ·
        refine ⟨52380887509879692413593421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34920591673253128275728947 52380887509879692413593421)
        ·
          refine ⟨19642832816204884655097533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52380887509879692413593421 19642832816204884655097533)
          ·
            refine ⟨7366062306076831745661575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19642832816204884655097533 7366062306076831745661575)
            ·
              refine ⟨11049093459115247618492363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7366062306076831745661575 11049093459115247618492363)
              ·
                refine ⟨16573640188672871427738545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11049093459115247618492363 16573640188672871427738545)
                ·
                  refine ⟨12430230141504653570803909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16573640188672871427738545 12430230141504653570803909)
                  ·
                    refine ⟨2330668151532122544525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12430230141504653570803909 2330668151532122544525733)
                    ·
                      refine ⟨437000278412272977098575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2330668151532122544525733 437000278412272977098575)
                      ·
                        rfl

theorem cell23_851055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_851055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851055 prefixEnd_851055 := by exact prefixLift 851055
  have htrace : WordTrace (prefixWord ++ tailWord_851055) baseStart_851055 baseEnd_851055 := by
    simpa [prefixWord, tailWord_851055, baseEnd_851055] using wordTrace_append hprefix tailTrace_851055
  have hstable : (prefixWord ++ tailWord_851055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851055).length < 2 ^ (prefixWord ++ tailWord_851055).sum := by decide
  have hdescent : baseEnd_851055 < baseStart_851055 := by decide
  rcases family_descends (prefixWord ++ tailWord_851055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851082 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_851082 : Nat := 118140960795 + 851082 * 2 ^ 59
def prefixEnd_851082 : Nat := 4983230072969 + 3 ^ 40 * 851082 * 2
def baseEnd_851082 : Nat := 48557126932216041273439

theorem tailTrace_851082 : CollatzResearch.WordTrace tailWord_851082 prefixEnd_851082 48557126932216041273439 := by
  unfold tailWord_851082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7760377675670685519636875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20694340468455161385698333 7760377675670685519636875)
  ·
    refine ⟨11640566513506028279455313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7760377675670685519636875 11640566513506028279455313)
    ·
      refine ⟨8730424885129521209591485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11640566513506028279455313 8730424885129521209591485)
      ·
        refine ⟨3273909331923570453596807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8730424885129521209591485 3273909331923570453596807)
        ·
          refine ⟨4910863997885355680395211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273909331923570453596807 4910863997885355680395211)
          ·
            refine ⟨7366295996828033520592817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4910863997885355680395211 7366295996828033520592817)
            ·
              refine ⟨5524721997621025140444613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7366295996828033520592817 5524721997621025140444613)
              ·
                refine ⟨1035885374553942213833365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5524721997621025140444613 1035885374553942213833365)
                ·
                  refine ⟨48557126932216041273439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1035885374553942213833365 48557126932216041273439)
                  ·
                    rfl

theorem cell23_851082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_851082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851082 prefixEnd_851082 := by exact prefixLift 851082
  have htrace : WordTrace (prefixWord ++ tailWord_851082) baseStart_851082 baseEnd_851082 := by
    simpa [prefixWord, tailWord_851082, baseEnd_851082] using wordTrace_append hprefix tailTrace_851082
  have hstable : (prefixWord ++ tailWord_851082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851082).length < 2 ^ (prefixWord ++ tailWord_851082).sum := by decide
  have hdescent : baseEnd_851082 < baseStart_851082 := by decide
  rcases family_descends (prefixWord ++ tailWord_851082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851086 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_851086 : Nat := 118140960795 + 851086 * 2 ^ 59
def prefixEnd_851086 : Nat := 4983230072969 + 3 ^ 40 * 851086 * 2
def baseEnd_851086 : Nat := 145672065437520785270311

theorem tailTrace_851086 : CollatzResearch.WordTrace tailWord_851086 prefixEnd_851086 145672065437520785270311 := by
  unfold tailWord_851086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880207074333531345211639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20694437729778833841128741 3880207074333531345211639)
  ·
    refine ⟨5820310611500297017817459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3880207074333531345211639 5820310611500297017817459)
    ·
      refine ⟨8730465917250445526726189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5820310611500297017817459 8730465917250445526726189)
      ·
        refine ⟨3273924718968917072522321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8730465917250445526726189 3273924718968917072522321)
        ·
          refine ⟨2455443539226687804391741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3273924718968917072522321 2455443539226687804391741)
          ·
            refine ⟨920791327210007926646903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2455443539226687804391741 920791327210007926646903)
            ·
              refine ⟨1381186990815011889970355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920791327210007926646903 1381186990815011889970355)
              ·
                refine ⟨2071780486222517834955533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381186990815011889970355 2071780486222517834955533)
                ·
                  refine ⟨776917682333444188108325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2071780486222517834955533 776917682333444188108325)
                  ·
                    refine ⟨145672065437520785270311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776917682333444188108325 145672065437520785270311)
                    ·
                      rfl

theorem cell23_851086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_851086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851086 prefixEnd_851086 := by exact prefixLift 851086
  have htrace : WordTrace (prefixWord ++ tailWord_851086) baseStart_851086 baseEnd_851086 := by
    simpa [prefixWord, tailWord_851086, baseEnd_851086] using wordTrace_append hprefix tailTrace_851086
  have hstable : (prefixWord ++ tailWord_851086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851086).length < 2 ^ (prefixWord ++ tailWord_851086).sum := by decide
  have hdescent : baseEnd_851086 < baseStart_851086 := by decide
  rcases family_descends (prefixWord ++ tailWord_851086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851119 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 2, 3, 2]
def baseStart_851119 : Nat := 118140960795 + 851119 * 2 ^ 59
def prefixEnd_851119 : Nat := 4983230072969 + 3 ^ 40 * 851119 * 2
def baseEnd_851119 : Nat := 437033141174160726698281

theorem tailTrace_851119 : CollatzResearch.WordTrace tailWord_851119 prefixEnd_851119 437033141174160726698281 := by
  unfold tailWord_851119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31042860203548697397644411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20695240135699131598429607 31042860203548697397644411)
  ·
    refine ⟨46564290305323046096466617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31042860203548697397644411 46564290305323046096466617)
    ·
      refine ⟨34923217728992284572349963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46564290305323046096466617 34923217728992284572349963)
      ·
        refine ⟨52384826593488426858524945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34923217728992284572349963 52384826593488426858524945)
        ·
          refine ⟨39288619945116320143893709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52384826593488426858524945 39288619945116320143893709)
          ·
            refine ⟨14733232479418620053960141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39288619945116320143893709 14733232479418620053960141)
            ·
              refine ⟨5524962179781982520235053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14733232479418620053960141 5524962179781982520235053)
              ·
                refine ⟨2071860817418243445088145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5524962179781982520235053 2071860817418243445088145)
                ·
                  refine ⟨1553895613063682583816109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2071860817418243445088145 1553895613063682583816109)
                  ·
                    refine ⟨582710854898880968931041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1553895613063682583816109 582710854898880968931041)
                    ·
                      refine ⟨437033141174160726698281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582710854898880968931041 437033141174160726698281)
                      ·
                        rfl

theorem cell23_851119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3, 2].length) (baseStart_851119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851119 prefixEnd_851119 := by exact prefixLift 851119
  have htrace : WordTrace (prefixWord ++ tailWord_851119) baseStart_851119 baseEnd_851119 := by
    simpa [prefixWord, tailWord_851119, baseEnd_851119] using wordTrace_append hprefix tailTrace_851119
  have hstable : (prefixWord ++ tailWord_851119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851119).length < 2 ^ (prefixWord ++ tailWord_851119).sum := by decide
  have hdescent : baseEnd_851119 < baseStart_851119 := by decide
  rcases family_descends (prefixWord ++ tailWord_851119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851159 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 2, 4]
def baseStart_851159 : Nat := 118140960795 + 851159 * 2 ^ 59
def prefixEnd_851159 : Nat := 4983230072969 + 3 ^ 40 * 851159 * 2
def baseEnd_851159 : Nat := 145684560133446856732699

theorem tailTrace_851159 : CollatzResearch.WordTrace tailWord_851159 prefixEnd_851159 145684560133446856732699 := by
  unfold tailWord_851159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31044319123403784229100531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20696212748935856152733687 31044319123403784229100531)
  ·
    refine ⟨46566478685105676343650797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31044319123403784229100531 46566478685105676343650797)
    ·
      refine ⟨17462429506914628628869049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46566478685105676343650797 17462429506914628628869049)
      ·
        refine ⟨13096822130185971471651787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17462429506914628628869049 13096822130185971471651787)
        ·
          refine ⟨19645233195278957207477681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13096822130185971471651787 19645233195278957207477681)
          ·
            refine ⟨14733924896459217905608261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19645233195278957207477681 14733924896459217905608261)
            ·
              refine ⟨2762610918086103357301549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14733924896459217905608261 2762610918086103357301549)
              ·
                refine ⟨1035979094282288758988081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2762610918086103357301549 1035979094282288758988081)
                ·
                  refine ⟨776984320711716569241061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1035979094282288758988081 776984320711716569241061)
                  ·
                    refine ⟨145684560133446856732699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776984320711716569241061 145684560133446856732699)
                    ·
                      rfl

theorem cell23_851159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_851159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851159 prefixEnd_851159 := by exact prefixLift 851159
  have htrace : WordTrace (prefixWord ++ tailWord_851159) baseStart_851159 baseEnd_851159 := by
    simpa [prefixWord, tailWord_851159, baseEnd_851159] using wordTrace_append hprefix tailTrace_851159
  have hstable : (prefixWord ++ tailWord_851159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851159).length < 2 ^ (prefixWord ++ tailWord_851159).sum := by decide
  have hdescent : baseEnd_851159 < baseStart_851159 := by decide
  rcases family_descends (prefixWord ++ tailWord_851159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851169 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_851169 : Nat := 118140960795 + 851169 * 2 ^ 59
def prefixEnd_851169 : Nat := 4983230072969 + 3 ^ 40 * 851169 * 2
def baseEnd_851169 : Nat := 437058815206885531073051

theorem tailTrace_851169 : CollatzResearch.WordTrace tailWord_851169 prefixEnd_851169 437058815206885531073051 := by
  unfold tailWord_851169
  simp only [CollatzResearch.WordTrace]
  refine ⟨31044683853367555936964561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20696455902245037291309707 31044683853367555936964561)
  ·
    refine ⟨23283512890025666952723421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31044683853367555936964561 23283512890025666952723421)
    ·
      refine ⟨8731317333759625107271283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23283512890025666952723421 8731317333759625107271283)
      ·
        refine ⟨13096976000639437660906925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731317333759625107271283 13096976000639437660906925)
        ·
          refine ⟨4911366000239789122840097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13096976000639437660906925 4911366000239789122840097)
          ·
            refine ⟨3683524500179841842130073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911366000239789122840097 3683524500179841842130073)
            ·
              refine ⟨2762643375134881381597555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683524500179841842130073 2762643375134881381597555)
              ·
                refine ⟨4143965062702322072396333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762643375134881381597555 4143965062702322072396333)
                ·
                  refine ⟨1553986898513370777148625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4143965062702322072396333 1553986898513370777148625)
                  ·
                    refine ⟨1165490173885028082861469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1553986898513370777148625 1165490173885028082861469)
                    ·
                      refine ⟨437058815206885531073051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1165490173885028082861469 437058815206885531073051)
                      ·
                        rfl

theorem cell23_851169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_851169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851169 prefixEnd_851169 := by exact prefixLift 851169
  have htrace : WordTrace (prefixWord ++ tailWord_851169) baseStart_851169 baseEnd_851169 := by
    simpa [prefixWord, tailWord_851169, baseEnd_851169] using wordTrace_append hprefix tailTrace_851169
  have hstable : (prefixWord ++ tailWord_851169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851169).length < 2 ^ (prefixWord ++ tailWord_851169).sum := by decide
  have hdescent : baseEnd_851169 < baseStart_851169 := by decide
  rcases family_descends (prefixWord ++ tailWord_851169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851183 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 1, 1, 4]
def baseStart_851183 : Nat := 118140960795 + 851183 * 2 ^ 59
def prefixEnd_851183 : Nat := 4983230072969 + 3 ^ 40 * 851183 * 2
def baseEnd_851183 : Nat := 437066003936048476297987

theorem tailTrace_851183 : CollatzResearch.WordTrace tailWord_851183 prefixEnd_851183 437066003936048476297987 := by
  unfold tailWord_851183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31045194475316836327974203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20696796316877890885316135 31045194475316836327974203)
  ·
    refine ⟨46567791712975254491961305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31045194475316836327974203 46567791712975254491961305)
    ·
      refine ⟨34925843784731440868970979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46567791712975254491961305 34925843784731440868970979)
      ·
        refine ⟨52388765677097161303456469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34925843784731440868970979 52388765677097161303456469)
        ·
          refine ⟨1227861695556964718049761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52388765677097161303456469 1227861695556964718049761)
          ·
            refine ⟨920896271667723538537321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1227861695556964718049761 920896271667723538537321)
            ·
              refine ⟨690672203750792653902991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920896271667723538537321 690672203750792653902991)
              ·
                refine ⟨1036008305626188980854487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690672203750792653902991 1036008305626188980854487)
                ·
                  refine ⟨1554012458439283471281731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036008305626188980854487 1554012458439283471281731)
                  ·
                    refine ⟨2331018687658925206922597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554012458439283471281731 2331018687658925206922597)
                    ·
                      refine ⟨437066003936048476297987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2331018687658925206922597 437066003936048476297987)
                      ·
                        rfl

theorem cell23_851183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 1, 4].length) (baseStart_851183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851183 prefixEnd_851183 := by exact prefixLift 851183
  have htrace : WordTrace (prefixWord ++ tailWord_851183) baseStart_851183 baseEnd_851183 := by
    simpa [prefixWord, tailWord_851183, baseEnd_851183] using wordTrace_append hprefix tailTrace_851183
  have hstable : (prefixWord ++ tailWord_851183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851183).length < 2 ^ (prefixWord ++ tailWord_851183).sum := by decide
  have hdescent : baseEnd_851183 < baseStart_851183 := by decide
  rcases family_descends (prefixWord ++ tailWord_851183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851229 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_851229 : Nat := 118140960795 + 851229 * 2 ^ 59
def prefixEnd_851229 : Nat := 4983230072969 + 3 ^ 40 * 851229 * 2
def baseEnd_851229 : Nat := 437089624046155296322775

theorem tailTrace_851229 : CollatzResearch.WordTrace tailWord_851229 prefixEnd_851229 437089624046155296322775 := by
  unfold tailWord_851229
  simp only [CollatzResearch.WordTrace]
  refine ⟨31046872233150186184148741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20697914822100124122765827 31046872233150186184148741)
  ·
    refine ⟨5821288543715659909527889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31046872233150186184148741 5821288543715659909527889)
    ·
      refine ⟨4365966407786744932145917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5821288543715659909527889 4365966407786744932145917)
      ·
        refine ⟨1637237402920029349554719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4365966407786744932145917 1637237402920029349554719)
        ·
          refine ⟨2455856104380044024332079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637237402920029349554719 2455856104380044024332079)
          ·
            refine ⟨3683784156570066036498119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455856104380044024332079 3683784156570066036498119)
            ·
              refine ⟨5525676234855099054747179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683784156570066036498119 5525676234855099054747179)
              ·
                refine ⟨8288514352282648582120769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525676234855099054747179 8288514352282648582120769)
                ·
                  refine ⟨6216385764211986436590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8288514352282648582120769 6216385764211986436590577)
                  ·
                    refine ⟨4662289323158989827442933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216385764211986436590577 4662289323158989827442933)
                    ·
                      refine ⟨437089624046155296322775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4662289323158989827442933 437089624046155296322775)
                      ·
                        rfl

theorem cell23_851229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_851229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851229 prefixEnd_851229 := by exact prefixLift 851229
  have htrace : WordTrace (prefixWord ++ tailWord_851229) baseStart_851229 baseEnd_851229 := by
    simpa [prefixWord, tailWord_851229, baseEnd_851229] using wordTrace_append hprefix tailTrace_851229
  have hstable : (prefixWord ++ tailWord_851229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851229).length < 2 ^ (prefixWord ++ tailWord_851229).sum := by decide
  have hdescent : baseEnd_851229 < baseStart_851229 := by decide
  rcases family_descends (prefixWord ++ tailWord_851229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851234 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_851234 : Nat := 118140960795 + 851234 * 2 ^ 59
def prefixEnd_851234 : Nat := 4983230072969 + 3 ^ 40 * 851234 * 2
def baseEnd_851234 : Nat := 437092191449427776760253

theorem tailTrace_851234 : CollatzResearch.WordTrace tailWord_851234 prefixEnd_851234 437092191449427776760253 := by
  unfold tailWord_851234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761763649533018009520189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20698036398754714692053837 7761763649533018009520189)
  ·
    refine ⟨2910661368574881753570071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7761763649533018009520189 2910661368574881753570071)
    ·
      refine ⟨4365992052862322630355107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910661368574881753570071 4365992052862322630355107)
      ·
        refine ⟨6548988079293483945532661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365992052862322630355107 6548988079293483945532661)
        ·
          refine ⟨613967632433764119893687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6548988079293483945532661 613967632433764119893687)
          ·
            refine ⟨920951448650646179840531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613967632433764119893687 920951448650646179840531)
            ·
              refine ⟨1381427172975969269760797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920951448650646179840531 1381427172975969269760797)
              ·
                refine ⟨518035189865988476160299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381427172975969269760797 518035189865988476160299)
                ·
                  refine ⟨777052784798982714240449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518035189865988476160299 777052784798982714240449)
                  ·
                    refine ⟨582789588599237035680337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 777052784798982714240449 582789588599237035680337)
                    ·
                      refine ⟨437092191449427776760253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582789588599237035680337 437092191449427776760253)
                      ·
                        rfl

theorem cell23_851234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_851234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851234 prefixEnd_851234 := by exact prefixLift 851234
  have htrace : WordTrace (prefixWord ++ tailWord_851234) baseStart_851234 baseEnd_851234 := by
    simpa [prefixWord, tailWord_851234, baseEnd_851234] using wordTrace_append hprefix tailTrace_851234
  have hstable : (prefixWord ++ tailWord_851234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851234).length < 2 ^ (prefixWord ++ tailWord_851234).sum := by decide
  have hdescent : baseEnd_851234 < baseStart_851234 := by decide
  rcases family_descends (prefixWord ++ tailWord_851234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851359 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_851359 : Nat := 118140960795 + 851359 * 2 ^ 59
def prefixEnd_851359 : Nat := 4983230072969 + 3 ^ 40 * 851359 * 2
def baseEnd_851359 : Nat := 437156376531239787697177

theorem tailTrace_851359 : CollatzResearch.WordTrace tailWord_851359 prefixEnd_851359 437156376531239787697177 := by
  unfold tailWord_851359
  simp only [CollatzResearch.WordTrace]
  refine ⟨31051613722679218386381131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701075815119478924254087 31051613722679218386381131)
  ·
    refine ⟨46577420584018827579571697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31051613722679218386381131 46577420584018827579571697)
    ·
      refine ⟨34933065438014120684678773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46577420584018827579571697 34933065438014120684678773)
      ·
        refine ⟨3274974884813823814188635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34933065438014120684678773 3274974884813823814188635)
        ·
          refine ⟨4912462327220735721282953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274974884813823814188635 4912462327220735721282953)
          ·
            refine ⟨3684346745415551790962215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4912462327220735721282953 3684346745415551790962215)
            ·
              refine ⟨5526520118123327686443323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684346745415551790962215 5526520118123327686443323)
              ·
                refine ⟨8289780177184991529664985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526520118123327686443323 8289780177184991529664985)
                ·
                  refine ⟨6217335132888743647248739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289780177184991529664985 6217335132888743647248739)
                  ·
                    refine ⟨9326002699333115470873109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217335132888743647248739 9326002699333115470873109)
                    ·
                      refine ⟨437156376531239787697177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9326002699333115470873109 437156376531239787697177)
                      ·
                        rfl

theorem cell23_851359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_851359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851359 prefixEnd_851359 := by exact prefixLift 851359
  have htrace : WordTrace (prefixWord ++ tailWord_851359) baseStart_851359 baseEnd_851359 := by
    simpa [prefixWord, tailWord_851359, baseEnd_851359] using wordTrace_append hprefix tailTrace_851359
  have hstable : (prefixWord ++ tailWord_851359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851359).length < 2 ^ (prefixWord ++ tailWord_851359).sum := by decide
  have hdescent : baseEnd_851359 < baseStart_851359 := by decide
  rcases family_descends (prefixWord ++ tailWord_851359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851373 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_851373 : Nat := 118140960795 + 851373 * 2 ^ 59
def prefixEnd_851373 : Nat := 4983230072969 + 3 ^ 40 * 851373 * 2
def baseEnd_851373 : Nat := 145721188420134244307371

theorem tailTrace_851373 : CollatzResearch.WordTrace tailWord_851373 prefixEnd_851373 145721188420134244307371 := by
  unfold tailWord_851373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052124344628498777390773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701416229752332518260515 31052124344628498777390773)
  ·
    refine ⟨2911136657308921760380385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31052124344628498777390773 2911136657308921760380385)
    ·
      refine ⟨2183352492981691320285289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911136657308921760380385 2183352492981691320285289)
      ·
        refine ⟨1637514369736268490213967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183352492981691320285289 1637514369736268490213967)
        ·
          refine ⟨2456271554604402735320951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637514369736268490213967 2456271554604402735320951)
          ·
            refine ⟨3684407331906604102981427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456271554604402735320951 3684407331906604102981427)
            ·
              refine ⟨5526610997859906154472141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684407331906604102981427 5526610997859906154472141)
              ·
                refine ⟨2072479124197464807927053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5526610997859906154472141 2072479124197464807927053)
                ·
                  refine ⟨777179671574049302972645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2072479124197464807927053 777179671574049302972645)
                  ·
                    refine ⟨145721188420134244307371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777179671574049302972645 145721188420134244307371)
                    ·
                      rfl

theorem cell23_851373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_851373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851373 prefixEnd_851373 := by exact prefixLift 851373
  have htrace : WordTrace (prefixWord ++ tailWord_851373) baseStart_851373 baseEnd_851373 := by
    simpa [prefixWord, tailWord_851373, baseEnd_851373] using wordTrace_append hprefix tailTrace_851373
  have hstable : (prefixWord ++ tailWord_851373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851373).length < 2 ^ (prefixWord ++ tailWord_851373).sum := by decide
  have hdescent : baseEnd_851373 < baseStart_851373 := by decide
  rcases family_descends (prefixWord ++ tailWord_851373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851389 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_851389 : Nat := 118140960795 + 851389 * 2 ^ 59
def prefixEnd_851389 : Nat := 4983230072969 + 3 ^ 40 * 851389 * 2
def baseEnd_851389 : Nat := 437171780950874670322039

theorem tailTrace_851389 : CollatzResearch.WordTrace tailWord_851389 prefixEnd_851389 437171780950874670322039 := by
  unfold tailWord_851389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052707912570533509973221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701805275047022339982147 31052707912570533509973221)
  ·
    refine ⟨5822382733606975033119979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31052707912570533509973221 5822382733606975033119979)
    ·
      refine ⟨8733574100410462549679969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5822382733606975033119979 8733574100410462549679969)
      ·
        refine ⟨6550180575307846912259977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8733574100410462549679969 6550180575307846912259977)
        ·
          refine ⟨4912635431480885184194983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6550180575307846912259977 4912635431480885184194983)
          ·
            refine ⟨7368953147221327776292475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912635431480885184194983 7368953147221327776292475)
            ·
              refine ⟨11053429720831991664438713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368953147221327776292475 11053429720831991664438713)
              ·
                refine ⟨8290072290623993748329035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11053429720831991664438713 8290072290623993748329035)
                ·
                  refine ⟨12435108435935990622493553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290072290623993748329035 12435108435935990622493553)
                  ·
                    refine ⟨9326331326951992966870165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435108435935990622493553 9326331326951992966870165)
                    ·
                      refine ⟨437171780950874670322039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9326331326951992966870165 437171780950874670322039)
                      ·
                        rfl

theorem cell23_851389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_851389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851389 prefixEnd_851389 := by exact prefixLift 851389
  have htrace : WordTrace (prefixWord ++ tailWord_851389) baseStart_851389 baseEnd_851389 := by
    simpa [prefixWord, tailWord_851389, baseEnd_851389] using wordTrace_append hprefix tailTrace_851389
  have hstable : (prefixWord ++ tailWord_851389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851389).length < 2 ^ (prefixWord ++ tailWord_851389).sum := by decide
  have hdescent : baseEnd_851389 < baseStart_851389 := by decide
  rcases family_descends (prefixWord ++ tailWord_851389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851416 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_851416 : Nat := 118140960795 + 851416 * 2 ^ 59
def prefixEnd_851416 : Nat := 4983230072969 + 3 ^ 40 * 851416 * 2
def baseEnd_851416 : Nat := 145728548309515354894805

theorem tailTrace_851416 : CollatzResearch.WordTrace tailWord_851416 prefixEnd_851416 145728548309515354894805 := by
  unfold tailWord_851416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526846341736358560603051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20702461788981811414137401 15526846341736358560603051)
  ·
    refine ⟨23290269512604537840904577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15526846341736358560603051 23290269512604537840904577)
    ·
      refine ⟨17467702134453403380678433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23290269512604537840904577 17467702134453403380678433)
      ·
        refine ⟨13100776600840052535508825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17467702134453403380678433 13100776600840052535508825)
        ·
          refine ⟨9825582450630039401631619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13100776600840052535508825 9825582450630039401631619)
          ·
            refine ⟨14738373675945059102447429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825582450630039401631619 14738373675945059102447429)
            ·
              refine ⟨2763445064239698581708893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14738373675945059102447429 2763445064239698581708893)
              ·
                refine ⟨1036291899089886968140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2763445064239698581708893 1036291899089886968140835)
                ·
                  refine ⟨1554437848634830452211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036291899089886968140835 1554437848634830452211253)
                  ·
                    refine ⟨145728548309515354894805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1554437848634830452211253 145728548309515354894805)
                    ·
                      rfl

theorem cell23_851416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_851416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851416 prefixEnd_851416 := by exact prefixLift 851416
  have htrace : WordTrace (prefixWord ++ tailWord_851416) baseStart_851416 baseEnd_851416 := by
    simpa [prefixWord, tailWord_851416, baseEnd_851416] using wordTrace_append hprefix tailTrace_851416
  have hstable : (prefixWord ++ tailWord_851416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851416).length < 2 ^ (prefixWord ++ tailWord_851416).sum := by decide
  have hdescent : baseEnd_851416 < baseStart_851416 := by decide
  rcases family_descends (prefixWord ++ tailWord_851416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851423 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 2, 3, 2]
def baseStart_851423 : Nat := 118140960795 + 851423 * 2 ^ 59
def prefixEnd_851423 : Nat := 4983230072969 + 3 ^ 40 * 851423 * 2
def baseEnd_851423 : Nat := 437189239293127537296883

theorem tailTrace_851423 : CollatzResearch.WordTrace tailWord_851423 prefixEnd_851423 437189239293127537296883 := by
  unfold tailWord_851423
  simp only [CollatzResearch.WordTrace]
  refine ⟨31053947994447357316710923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20702631996298238211140615 31053947994447357316710923)
  ·
    refine ⟨46580921991671035975066385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31053947994447357316710923 46580921991671035975066385)
    ·
      refine ⟨34935691493753276981299789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46580921991671035975066385 34935691493753276981299789)
      ·
        refine ⟨13100884310157478867987421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34935691493753276981299789 13100884310157478867987421)
        ·
          refine ⟨4912831616309054575495283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13100884310157478867987421 4912831616309054575495283)
          ·
            refine ⟨7369247424463581863242925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912831616309054575495283 7369247424463581863242925)
            ·
              refine ⟨2763467784173843198716097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7369247424463581863242925 2763467784173843198716097)
              ·
                refine ⟨2072600838130382399037073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763467784173843198716097 2072600838130382399037073)
                ·
                  refine ⟨1554450628597786799277805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072600838130382399037073 1554450628597786799277805)
                  ·
                    refine ⟨582918985724170049729177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554450628597786799277805 582918985724170049729177)
                    ·
                      refine ⟨437189239293127537296883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582918985724170049729177 437189239293127537296883)
                      ·
                        rfl

theorem cell23_851423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_851423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851423 prefixEnd_851423 := by exact prefixLift 851423
  have htrace : WordTrace (prefixWord ++ tailWord_851423) baseStart_851423 baseEnd_851423 := by
    simpa [prefixWord, tailWord_851423, baseEnd_851423] using wordTrace_append hprefix tailTrace_851423
  have hstable : (prefixWord ++ tailWord_851423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851423).length < 2 ^ (prefixWord ++ tailWord_851423).sum := by decide
  have hdescent : baseEnd_851423 < baseStart_851423 := by decide
  rcases family_descends (prefixWord ++ tailWord_851423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851436 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_851436 : Nat := 118140960795 + 851436 * 2 ^ 59
def prefixEnd_851436 : Nat := 4983230072969 + 3 ^ 40 * 851436 * 2
def baseEnd_851436 : Nat := 437195914541635986434323

theorem tailTrace_851436 : CollatzResearch.WordTrace tailWord_851436 prefixEnd_851436 437195914541635986434323 := by
  unfold tailWord_851436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15527211071700130268467081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20702948095600173691289441 15527211071700130268467081)
  ·
    refine ⟨11645408303775097701350311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15527211071700130268467081 11645408303775097701350311)
    ·
      refine ⟨17468112455662646552025467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11645408303775097701350311 17468112455662646552025467)
      ·
        refine ⟨26202168683493969828038201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17468112455662646552025467 26202168683493969828038201)
        ·
          refine ⟨19651626512620477371028651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26202168683493969828038201 19651626512620477371028651)
          ·
            refine ⟨29477439768930716056542977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19651626512620477371028651 29477439768930716056542977)
            ·
              refine ⟨22108079826698037042407233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29477439768930716056542977 22108079826698037042407233)
              ·
                refine ⟨16581059870023527781805425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22108079826698037042407233 16581059870023527781805425)
                ·
                  refine ⟨12435794902517645836354069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581059870023527781805425 12435794902517645836354069)
                  ·
                    refine ⟨582927886055514648579097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12435794902517645836354069 582927886055514648579097)
                    ·
                      refine ⟨437195914541635986434323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582927886055514648579097 437195914541635986434323)
                      ·
                        rfl

theorem cell23_851436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_851436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851436 prefixEnd_851436 := by exact prefixLift 851436
  have htrace : WordTrace (prefixWord ++ tailWord_851436) baseStart_851436 baseEnd_851436 := by
    simpa [prefixWord, tailWord_851436, baseEnd_851436] using wordTrace_append hprefix tailTrace_851436
  have hstable : (prefixWord ++ tailWord_851436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851436).length < 2 ^ (prefixWord ++ tailWord_851436).sum := by decide
  have hdescent : baseEnd_851436 < baseStart_851436 := by decide
  rcases family_descends (prefixWord ++ tailWord_851436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851437 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 6]
def baseStart_851437 : Nat := 118140960795 + 851437 * 2 ^ 59
def prefixEnd_851437 : Nat := 4983230072969 + 3 ^ 40 * 851437 * 2
def baseEnd_851437 : Nat := 48577380891365609169091

theorem tailTrace_851437 : CollatzResearch.WordTrace tailWord_851437 prefixEnd_851437 48577380891365609169091 := by
  unfold tailWord_851437
  simp only [CollatzResearch.WordTrace]
  refine ⟨31054458616396637707720565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20702972410931091805147043 31054458616396637707720565)
  ·
    refine ⟨2911355495287184785098803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31054458616396637707720565 2911355495287184785098803)
    ·
      refine ⟨4367033242930777177648205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911355495287184785098803 4367033242930777177648205)
      ·
        refine ⟨1637637466099041441618077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4367033242930777177648205 1637637466099041441618077)
        ·
          refine ⟨614114049787140540606779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1637637466099041441618077 614114049787140540606779)
          ·
            refine ⟨921171074680710810910169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614114049787140540606779 921171074680710810910169)
            ·
              refine ⟨690878306010533108182627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921171074680710810910169 690878306010533108182627)
              ·
                refine ⟨1036317459015799662273941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690878306010533108182627 1036317459015799662273941)
                ·
                  refine ⟨48577380891365609169091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1036317459015799662273941 48577380891365609169091)
                  ·
                    rfl

theorem cell23_851437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_851437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851437 prefixEnd_851437 := by exact prefixLift 851437
  have htrace : WordTrace (prefixWord ++ tailWord_851437) baseStart_851437 baseEnd_851437 := by
    simpa [prefixWord, tailWord_851437, baseEnd_851437] using wordTrace_append hprefix tailTrace_851437
  have hstable : (prefixWord ++ tailWord_851437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851437).length < 2 ^ (prefixWord ++ tailWord_851437).sum := by decide
  have hdescent : baseEnd_851437 < baseStart_851437 := by decide
  rcases family_descends (prefixWord ++ tailWord_851437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851453 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_851453 : Nat := 118140960795 + 851453 * 2 ^ 59
def prefixEnd_851453 : Nat := 4983230072969 + 3 ^ 40 * 851453 * 2
def baseEnd_851453 : Nat := 437204643712762419921745

theorem tailTrace_851453 : CollatzResearch.WordTrace tailWord_851453 prefixEnd_851453 437204643712762419921745 := by
  unfold tailWord_851453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055042184338672440303013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20703361456225781626868675 31055042184338672440303013)
  ·
    refine ⟨5822820409563501082556815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31055042184338672440303013 5822820409563501082556815)
    ·
      refine ⟨8734230614345251623835223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5822820409563501082556815 8734230614345251623835223)
      ·
        refine ⟨13101345921517877435752835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734230614345251623835223 13101345921517877435752835)
        ·
          refine ⟨19652018882276816153629253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101345921517877435752835 19652018882276816153629253)
          ·
            refine ⟨3684753540426903028805485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19652018882276816153629253 3684753540426903028805485)
            ·
              refine ⟨1381782577660088635802057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3684753540426903028805485 1381782577660088635802057)
              ·
                refine ⟨1036336933245066476851543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381782577660088635802057 1036336933245066476851543)
                ·
                  refine ⟨1554505399867599715277315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036336933245066476851543 1554505399867599715277315)
                  ·
                    refine ⟨2331758099801399572915973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554505399867599715277315 2331758099801399572915973)
                    ·
                      refine ⟨437204643712762419921745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2331758099801399572915973 437204643712762419921745)
                      ·
                        rfl

theorem cell23_851453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_851453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851453 prefixEnd_851453 := by exact prefixLift 851453
  have htrace : WordTrace (prefixWord ++ tailWord_851453) baseStart_851453 baseEnd_851453 := by
    simpa [prefixWord, tailWord_851453, baseEnd_851453] using wordTrace_append hprefix tailTrace_851453
  have hstable : (prefixWord ++ tailWord_851453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851453).length < 2 ^ (prefixWord ++ tailWord_851453).sum := by decide
  have hdescent : baseEnd_851453 < baseStart_851453 := by decide
  rcases family_descends (prefixWord ++ tailWord_851453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851466 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_851466 : Nat := 118140960795 + 851466 * 2 ^ 59
def prefixEnd_851466 : Nat := 4983230072969 + 3 ^ 40 * 851466 * 2
def baseEnd_851466 : Nat := 437211318961270869059185

theorem tailTrace_851466 : CollatzResearch.WordTrace tailWord_851466 prefixEnd_851466 437211318961270869059185 := by
  unfold tailWord_851466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763879083322893915131563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20703677555527717107017501 7763879083322893915131563)
  ·
    refine ⟨11645818624984340872697345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7763879083322893915131563 11645818624984340872697345)
    ·
      refine ⟨8734363968738255654523009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11645818624984340872697345 8734363968738255654523009)
      ·
        refine ⟨6550772976553691740892257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8734363968738255654523009 6550772976553691740892257)
        ·
          refine ⟨4913079732415268805669193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6550772976553691740892257 4913079732415268805669193)
          ·
            refine ⟨3684809799311451604251895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4913079732415268805669193 3684809799311451604251895)
            ·
              refine ⟨5527214698967177406377843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684809799311451604251895 5527214698967177406377843)
              ·
                refine ⟨8290822048450766109566765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527214698967177406377843 8290822048450766109566765)
                ·
                  refine ⟨3109058268169037291087537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8290822048450766109566765 3109058268169037291087537)
                  ·
                    refine ⟨2331793701126777968315653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109058268169037291087537 2331793701126777968315653)
                    ·
                      refine ⟨437211318961270869059185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2331793701126777968315653 437211318961270869059185)
                      ·
                        rfl

theorem cell23_851466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_851466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851466 prefixEnd_851466 := by exact prefixLift 851466
  have htrace : WordTrace (prefixWord ++ tailWord_851466) baseStart_851466 baseEnd_851466 := by
    simpa [prefixWord, tailWord_851466, baseEnd_851466] using wordTrace_append hprefix tailTrace_851466
  have hstable : (prefixWord ++ tailWord_851466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851466).length < 2 ^ (prefixWord ++ tailWord_851466).sum := by decide
  have hdescent : baseEnd_851466 < baseStart_851466 := by decide
  rcases family_descends (prefixWord ++ tailWord_851466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851476 : List Nat := [2, 4, 3, 1, 13]
def baseStart_851476 : Nat := 118140960795 + 851476 * 2 ^ 59
def prefixEnd_851476 : Nat := 4983230072969 + 3 ^ 40 * 851476 * 2
def baseEnd_851476 : Nat := 599748221903725418291

theorem tailTrace_851476 : CollatzResearch.WordTrace tailWord_851476 prefixEnd_851476 599748221903725418291 := by
  unfold tailWord_851476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15527940531627673684195141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20703920708836898245593521 15527940531627673684195141)
  ·
    refine ⟨2911488849680188815786589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15527940531627673684195141 2911488849680188815786589)
    ·
      refine ⟨1091808318630070805919971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2911488849680188815786589 1091808318630070805919971)
      ·
        refine ⟨1637712477945106208879957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091808318630070805919971 1637712477945106208879957)
        ·
          refine ⟨599748221903725418291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1637712477945106208879957 599748221903725418291)
          ·
            rfl

theorem cell23_851476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 13].length) (baseStart_851476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851476 prefixEnd_851476 := by exact prefixLift 851476
  have htrace : WordTrace (prefixWord ++ tailWord_851476) baseStart_851476 baseEnd_851476 := by
    simpa [prefixWord, tailWord_851476, baseEnd_851476] using wordTrace_append hprefix tailTrace_851476
  have hstable : (prefixWord ++ tailWord_851476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851476).length < 2 ^ (prefixWord ++ tailWord_851476).sum := by decide
  have hdescent : baseEnd_851476 < baseStart_851476 := by decide
  rcases family_descends (prefixWord ++ tailWord_851476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851480 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_851480 : Nat := 118140960795 + 851480 * 2 ^ 59
def prefixEnd_851480 : Nat := 4983230072969 + 3 ^ 40 * 851480 * 2
def baseEnd_851480 : Nat := 145739502563477938094707

theorem tailTrace_851480 : CollatzResearch.WordTrace tailWord_851480 prefixEnd_851480 145739502563477938094707 := by
  unfold tailWord_851480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528013477620428025767947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20704017970160570701023929 15528013477620428025767947)
  ·
    refine ⟨23292020216430642038651921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15528013477620428025767947 23292020216430642038651921)
    ·
      refine ⟨17469015162322981528988941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23292020216430642038651921 17469015162322981528988941)
      ·
        refine ⟨6550880685871118073370853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17469015162322981528988941 6550880685871118073370853)
        ·
          refine ⟨1228290128600834638757035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6550880685871118073370853 1228290128600834638757035)
          ·
            refine ⟨1842435192901251958135553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228290128600834638757035 1842435192901251958135553)
            ·
              refine ⟨1381826394675938968601665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1842435192901251958135553 1381826394675938968601665)
              ·
                refine ⟨1036369796006954226451249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381826394675938968601665 1036369796006954226451249)
                ·
                  refine ⟨777277347005215669838437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036369796006954226451249 777277347005215669838437)
                  ·
                    refine ⟨145739502563477938094707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777277347005215669838437 145739502563477938094707)
                    ·
                      rfl

theorem cell23_851480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_851480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851480 prefixEnd_851480 := by exact prefixLift 851480
  have htrace : WordTrace (prefixWord ++ tailWord_851480) baseStart_851480 baseEnd_851480 := by
    simpa [prefixWord, tailWord_851480, baseEnd_851480] using wordTrace_append hprefix tailTrace_851480
  have hstable : (prefixWord ++ tailWord_851480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851480).length < 2 ^ (prefixWord ++ tailWord_851480).sum := by decide
  have hdescent : baseEnd_851480 < baseStart_851480 := by decide
  rcases family_descends (prefixWord ++ tailWord_851480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851499 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_851499 : Nat := 118140960795 + 851499 * 2 ^ 59
def prefixEnd_851499 : Nat := 4983230072969 + 3 ^ 40 * 851499 * 2
def baseEnd_851499 : Nat := 437228263822869239946533

theorem tailTrace_851499 : CollatzResearch.WordTrace tailWord_851499 prefixEnd_851499 437228263822869239946533 := by
  unfold tailWord_851499
  simp only [CollatzResearch.WordTrace]
  refine ⟨31056719942172022296477551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20704479961448014864318367 31056719942172022296477551)
  ·
    refine ⟨46585079913258033444716327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31056719942172022296477551 46585079913258033444716327)
    ·
      refine ⟨69877619869887050167074491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46585079913258033444716327 69877619869887050167074491)
      ·
        refine ⟨104816429804830575250611737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69877619869887050167074491 104816429804830575250611737)
        ·
          refine ⟨78612322353622931437958803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104816429804830575250611737 78612322353622931437958803)
          ·
            refine ⟨117918483530434397156938205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78612322353622931437958803 117918483530434397156938205)
            ·
              refine ⟨44219431323912898933851827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117918483530434397156938205 44219431323912898933851827)
              ·
                refine ⟨66329146985869348400777741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44219431323912898933851827 66329146985869348400777741)
                ·
                  refine ⟨24873430119701005650291653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66329146985869348400777741 24873430119701005650291653)
                  ·
                    refine ⟨4663768147443938559429685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24873430119701005650291653 4663768147443938559429685)
                    ·
                      refine ⟨437228263822869239946533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4663768147443938559429685 437228263822869239946533)
                      ·
                        rfl

theorem cell23_851499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_851499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851499 prefixEnd_851499 := by exact prefixLift 851499
  have htrace : WordTrace (prefixWord ++ tailWord_851499) baseStart_851499 baseEnd_851499 := by
    simpa [prefixWord, tailWord_851499, baseEnd_851499] using wordTrace_append hprefix tailTrace_851499
  have hstable : (prefixWord ++ tailWord_851499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851499).length < 2 ^ (prefixWord ++ tailWord_851499).sum := by decide
  have hdescent : baseEnd_851499 < baseStart_851499 := by decide
  rcases family_descends (prefixWord ++ tailWord_851499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851510 : List Nat := [5, 1, 2, 1, 3, 1, 3, 7]
def baseStart_851510 : Nat := 118140960795 + 851510 * 2 ^ 59
def prefixEnd_851510 : Nat := 4983230072969 + 3 ^ 40 * 851510 * 2
def baseEnd_851510 : Nat := 16193848596669210996629

theorem tailTrace_851510 : CollatzResearch.WordTrace tailWord_851510 prefixEnd_851510 16193848596669210996629 := by
  unfold tailWord_851510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941070071570760698445499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20704747430088114116751989 1941070071570760698445499)
  ·
    refine ⟨2911605107356141047668249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941070071570760698445499 2911605107356141047668249)
    ·
      refine ⟨2183703830517105785751187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911605107356141047668249 2183703830517105785751187)
      ·
        refine ⟨3275555745775658678626781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183703830517105785751187 3275555745775658678626781)
        ·
          refine ⟨1228333404665872004485043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3275555745775658678626781 1228333404665872004485043)
          ·
            refine ⟨1842500106998808006727565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228333404665872004485043 1842500106998808006727565)
            ·
              refine ⟨690937540124553002522837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842500106998808006727565 690937540124553002522837)
              ·
                refine ⟨16193848596669210996629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 690937540124553002522837 16193848596669210996629)
                ·
                  rfl

theorem cell23_851510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_851510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851510 prefixEnd_851510 := by exact prefixLift 851510
  have htrace : WordTrace (prefixWord ++ tailWord_851510) baseStart_851510 baseEnd_851510 := by
    simpa [prefixWord, tailWord_851510, baseEnd_851510] using wordTrace_append hprefix tailTrace_851510
  have hstable : (prefixWord ++ tailWord_851510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851510).length < 2 ^ (prefixWord ++ tailWord_851510).sum := by decide
  have hdescent : baseEnd_851510 < baseStart_851510 := by decide
  rcases family_descends (prefixWord ++ tailWord_851510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851530 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_851530 : Nat := 118140960795 + 851530 * 2 ^ 59
def prefixEnd_851530 : Nat := 4983230072969 + 3 ^ 40 * 851530 * 2
def baseEnd_851530 : Nat := 437244181723158618658891

theorem tailTrace_851530 : CollatzResearch.WordTrace tailWord_851530 prefixEnd_851530 437244181723158618658891 := by
  unfold tailWord_851530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764462651264928647714011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20705233736706476393904029 7764462651264928647714011)
  ·
    refine ⟨11646693976897392971571017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764462651264928647714011 11646693976897392971571017)
    ·
      refine ⟨8735020482673044728678263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11646693976897392971571017 8735020482673044728678263)
      ·
        refine ⟨13102530724009567093017395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735020482673044728678263 13102530724009567093017395)
        ·
          refine ⟨19653796086014350639526093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13102530724009567093017395 19653796086014350639526093)
          ·
            refine ⟨7370173532255381489822285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19653796086014350639526093 7370173532255381489822285)
            ·
              refine ⟨2763815074595768058683357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7370173532255381489822285 2763815074595768058683357)
              ·
                refine ⟨1036430652973413022006259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2763815074595768058683357 1036430652973413022006259)
                ·
                  refine ⟨1554645979460119533009389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036430652973413022006259 1554645979460119533009389)
                  ·
                    refine ⟨582992242297544824878521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1554645979460119533009389 582992242297544824878521)
                    ·
                      refine ⟨437244181723158618658891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 582992242297544824878521 437244181723158618658891)
                      ·
                        rfl

theorem cell23_851530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_851530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851530 prefixEnd_851530 := by exact prefixLift 851530
  have htrace : WordTrace (prefixWord ++ tailWord_851530) baseStart_851530 baseEnd_851530 := by
    simpa [prefixWord, tailWord_851530, baseEnd_851530] using wordTrace_append hprefix tailTrace_851530
  have hstable : (prefixWord ++ tailWord_851530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851530).length < 2 ^ (prefixWord ++ tailWord_851530).sum := by decide
  have hdescent : baseEnd_851530 < baseStart_851530 := by decide
  rcases family_descends (prefixWord ++ tailWord_851530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851546 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_851546 : Nat := 118140960795 + 851546 * 2 ^ 59
def prefixEnd_851546 : Nat := 4983230072969 + 3 ^ 40 * 851546 * 2
def baseEnd_851546 : Nat := 437252397413630556058817

theorem tailTrace_851546 : CollatzResearch.WordTrace tailWord_851546 prefixEnd_851546 437252397413630556058817 := by
  unfold tailWord_851546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764608543250437330859623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20705622782001166215625661 7764608543250437330859623)
  ·
    refine ⟨11646912814875655996289435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764608543250437330859623 11646912814875655996289435)
    ·
      refine ⟨17470369222313483994434153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11646912814875655996289435 17470369222313483994434153)
      ·
        refine ⟨13102776916735112995825615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17470369222313483994434153 13102776916735112995825615)
        ·
          refine ⟨19654165375102669493738423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13102776916735112995825615 19654165375102669493738423)
          ·
            refine ⟨29481248062654004240607635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654165375102669493738423 29481248062654004240607635)
            ·
              refine ⟨44221872093981006360911453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29481248062654004240607635 44221872093981006360911453)
              ·
                refine ⟨16583202035242877385341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44221872093981006360911453 16583202035242877385341795)
                ·
                  refine ⟨24874803052864316078012693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16583202035242877385341795 24874803052864316078012693)
                  ·
                    refine ⟨1166006393103014816156845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24874803052864316078012693 1166006393103014816156845)
                    ·
                      refine ⟨437252397413630556058817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166006393103014816156845 437252397413630556058817)
                      ·
                        rfl

theorem cell23_851546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_851546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851546 prefixEnd_851546 := by exact prefixLift 851546
  have htrace : WordTrace (prefixWord ++ tailWord_851546) baseStart_851546 baseEnd_851546 := by
    simpa [prefixWord, tailWord_851546, baseEnd_851546] using wordTrace_append hprefix tailTrace_851546
  have hstable : (prefixWord ++ tailWord_851546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851546).length < 2 ^ (prefixWord ++ tailWord_851546).sum := by decide
  have hdescent : baseEnd_851546 < baseStart_851546 := by decide
  rcases family_descends (prefixWord ++ tailWord_851546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851654 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_851654 : Nat := 118140960795 + 851654 * 2 ^ 59
def prefixEnd_851654 : Nat := 4983230072969 + 3 ^ 40 * 851654 * 2
def baseEnd_851654 : Nat := 437307853324316133508321

theorem tailTrace_851654 : CollatzResearch.WordTrace tailWord_851654 prefixEnd_851654 437307853324316133508321 := by
  unfold tailWord_851654
  simp only [CollatzResearch.WordTrace]
  refine ⟨970699164269077617761563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20708248837740322512246677 970699164269077617761563)
  ·
    refine ⟨1456048746403616426642345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 970699164269077617761563 1456048746403616426642345)
    ·
      refine ⟨1092036559802712319981759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456048746403616426642345 1092036559802712319981759)
      ·
        refine ⟨1638054839704068479972639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092036559802712319981759 1638054839704068479972639)
        ·
          refine ⟨2457082259556102719958959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638054839704068479972639 2457082259556102719958959)
          ·
            refine ⟨3685623389334154079938439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457082259556102719958959 3685623389334154079938439)
            ·
              refine ⟨5528435084001231119907659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685623389334154079938439 5528435084001231119907659)
              ·
                refine ⟨8292652626001846679861489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528435084001231119907659 8292652626001846679861489)
                ·
                  refine ⟨6219489469501385009896117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292652626001846679861489 6219489469501385009896117)
                  ·
                    refine ⟨583077137765754844677761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6219489469501385009896117 583077137765754844677761)
                    ·
                      refine ⟨437307853324316133508321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583077137765754844677761 437307853324316133508321)
                      ·
                        rfl

theorem cell23_851654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_851654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851654 prefixEnd_851654 := by exact prefixLift 851654
  have htrace : WordTrace (prefixWord ++ tailWord_851654) baseStart_851654 baseEnd_851654 := by
    simpa [prefixWord, tailWord_851654, baseEnd_851654] using wordTrace_append hprefix tailTrace_851654
  have hstable : (prefixWord ++ tailWord_851654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851654).length < 2 ^ (prefixWord ++ tailWord_851654).sum := by decide
  have hdescent : baseEnd_851654 < baseStart_851654 := by decide
  rcases family_descends (prefixWord ++ tailWord_851654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851673 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 6]
def baseStart_851673 : Nat := 118140960795 + 851673 * 2 ^ 59
def prefixEnd_851673 : Nat := 4983230072969 + 3 ^ 40 * 851673 * 2
def baseEnd_851673 : Nat := 48590845495194617685637

theorem tailTrace_851673 : CollatzResearch.WordTrace tailWord_851673 prefixEnd_851673 48590845495194617685637 := by
  unfold tailWord_851673
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063066243541650013311673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20708710829027766675541115 31063066243541650013311673)
  ·
    refine ⟨23297299682656237509983755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31063066243541650013311673 23297299682656237509983755)
    ·
      refine ⟨34945949523984356264975633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23297299682656237509983755 34945949523984356264975633)
      ·
        refine ⟨26209462142988267198731725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34945949523984356264975633 26209462142988267198731725)
        ·
          refine ⟨9828548303620600199524397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26209462142988267198731725 9828548303620600199524397)
          ·
            refine ⟨3685705613857725074821649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9828548303620600199524397 3685705613857725074821649)
            ·
              refine ⟨2764279210393293806116237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685705613857725074821649 2764279210393293806116237)
              ·
                refine ⟨1036604703897485177293589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2764279210393293806116237 1036604703897485177293589)
                ·
                  refine ⟨48590845495194617685637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1036604703897485177293589 48590845495194617685637)
                  ·
                    rfl

theorem cell23_851673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_851673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851673 prefixEnd_851673 := by exact prefixLift 851673
  have htrace : WordTrace (prefixWord ++ tailWord_851673) baseStart_851673 baseEnd_851673 := by
    simpa [prefixWord, tailWord_851673, baseEnd_851673] using wordTrace_append hprefix tailTrace_851673
  have hstable : (prefixWord ++ tailWord_851673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851673).length < 2 ^ (prefixWord ++ tailWord_851673).sum := by decide
  have hdescent : baseEnd_851673 < baseStart_851673 := by decide
  rcases family_descends (prefixWord ++ tailWord_851673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851687 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_851687 : Nat := 118140960795 + 851687 * 2 ^ 59
def prefixEnd_851687 : Nat := 4983230072969 + 3 ^ 40 * 851687 * 2
def baseEnd_851687 : Nat := 437324798185914504395669

theorem tailTrace_851687 : CollatzResearch.WordTrace tailWord_851687 prefixEnd_851687 437324798185914504395669 := by
  unfold tailWord_851687
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063576865490930404321315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20709051243660620269547543 31063576865490930404321315)
  ·
    refine ⟨46595365298236395606481973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063576865490930404321315 46595365298236395606481973)
    ·
      refine ⟨4368315496709662088107685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46595365298236395606481973 4368315496709662088107685)
      ·
        refine ⟨819059155633061641520191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4368315496709662088107685 819059155633061641520191)
        ·
          refine ⟨1228588733449592462280287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819059155633061641520191 1228588733449592462280287)
          ·
            refine ⟨1842883100174388693420431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228588733449592462280287 1842883100174388693420431)
            ·
              refine ⟨2764324650261583040130647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842883100174388693420431 2764324650261583040130647)
              ·
                refine ⟨4146486975392374560195971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764324650261583040130647 4146486975392374560195971)
                ·
                  refine ⟨6219730463088561840293957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146486975392374560195971 6219730463088561840293957)
                  ·
                    refine ⟨1166199461829105345055117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219730463088561840293957 1166199461829105345055117)
                    ·
                      refine ⟨437324798185914504395669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166199461829105345055117 437324798185914504395669)
                      ·
                        rfl

theorem cell23_851687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_851687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851687 prefixEnd_851687 := by exact prefixLift 851687
  have htrace : WordTrace (prefixWord ++ tailWord_851687) baseStart_851687 baseEnd_851687 := by
    simpa [prefixWord, tailWord_851687, baseEnd_851687] using wordTrace_append hprefix tailTrace_851687
  have hstable : (prefixWord ++ tailWord_851687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851687).length < 2 ^ (prefixWord ++ tailWord_851687).sum := by decide
  have hdescent : baseEnd_851687 < baseStart_851687 := by decide
  rcases family_descends (prefixWord ++ tailWord_851687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851723 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4]
def baseStart_851723 : Nat := 118140960795 + 851723 * 2 ^ 59
def prefixEnd_851723 : Nat := 4983230072969 + 3 ^ 40 * 851723 * 2
def baseEnd_851723 : Nat := 437343283489476363545503

theorem tailTrace_851723 : CollatzResearch.WordTrace tailWord_851723 prefixEnd_851723 437343283489476363545503 := by
  unfold tailWord_851723
  simp only [CollatzResearch.WordTrace]
  refine ⟨31064889893360508552631823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20709926595573672368421215 31064889893360508552631823)
  ·
    refine ⟨46597334840040762828947735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31064889893360508552631823 46597334840040762828947735)
    ·
      refine ⟨69896002260061144243421603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46597334840040762828947735 69896002260061144243421603)
      ·
        refine ⟨104844003390091716365132405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69896002260061144243421603 104844003390091716365132405)
        ·
          refine ⟨9829125317821098409231163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104844003390091716365132405 9829125317821098409231163)
          ·
            refine ⟨14743687976731647613846745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829125317821098409231163 14743687976731647613846745)
            ·
              refine ⟨11057765982548735710385059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14743687976731647613846745 11057765982548735710385059)
              ·
                refine ⟨16586648973823103565577589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057765982548735710385059 16586648973823103565577589)
                ·
                  refine ⟨1554998341295915959272899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16586648973823103565577589 1554998341295915959272899)
                  ·
                    refine ⟨2332497511943873938909349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554998341295915959272899 2332497511943873938909349)
                    ·
                      refine ⟨437343283489476363545503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2332497511943873938909349 437343283489476363545503)
                      ·
                        rfl

theorem cell23_851723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_851723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851723 prefixEnd_851723 := by exact prefixLift 851723
  have htrace : WordTrace (prefixWord ++ tailWord_851723) baseStart_851723 baseEnd_851723 := by
    simpa [prefixWord, tailWord_851723, baseEnd_851723] using wordTrace_append hprefix tailTrace_851723
  have hstable : (prefixWord ++ tailWord_851723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851723).length < 2 ^ (prefixWord ++ tailWord_851723).sum := by decide
  have hdescent : baseEnd_851723 < baseStart_851723 := by decide
  rcases family_descends (prefixWord ++ tailWord_851723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851740 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_851740 : Nat := 118140960795 + 851740 * 2 ^ 59
def prefixEnd_851740 : Nat := 4983230072969 + 3 ^ 40 * 851740 * 2
def baseEnd_851740 : Nat := 437352012660602797032925

theorem tailTrace_851740 : CollatzResearch.WordTrace tailWord_851740 prefixEnd_851740 437352012660602797032925 := by
  unfold tailWord_851740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532754967149460228000337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20710339956199280304000449 15532754967149460228000337)
  ·
    refine ⟨11649566225362095171000253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15532754967149460228000337 11649566225362095171000253)
    ·
      refine ⟨4368587334510785689125095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11649566225362095171000253 4368587334510785689125095)
      ·
        refine ⟨6552881001766178533687643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368587334510785689125095 6552881001766178533687643)
        ·
          refine ⟨9829321502649267800531465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552881001766178533687643 9829321502649267800531465)
          ·
            refine ⟨7371991126986950850398599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829321502649267800531465 7371991126986950850398599)
            ·
              refine ⟨11057986690480426275597899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371991126986950850398599 11057986690480426275597899)
              ·
                refine ⟨16586980035720639413396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057986690480426275597899 16586980035720639413396849)
                ·
                  refine ⟨12440235026790479560047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586980035720639413396849 12440235026790479560047637)
                  ·
                    refine ⟨583136016880803729377233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12440235026790479560047637 583136016880803729377233)
                    ·
                      refine ⟨437352012660602797032925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583136016880803729377233 437352012660602797032925)
                      ·
                        rfl

theorem cell23_851740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_851740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851740 prefixEnd_851740 := by exact prefixLift 851740
  have htrace : WordTrace (prefixWord ++ tailWord_851740) baseStart_851740 baseEnd_851740 := by
    simpa [prefixWord, tailWord_851740, baseEnd_851740] using wordTrace_append hprefix tailTrace_851740
  have hstable : (prefixWord ++ tailWord_851740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851740).length < 2 ^ (prefixWord ++ tailWord_851740).sum := by decide
  have hdescent : baseEnd_851740 < baseStart_851740 := by decide
  rcases family_descends (prefixWord ++ tailWord_851740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851743 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_851743 : Nat := 118140960795 + 851743 * 2 ^ 59
def prefixEnd_851743 : Nat := 4983230072969 + 3 ^ 40 * 851743 * 2
def baseEnd_851743 : Nat := 437353553102566285295411

theorem tailTrace_851743 : CollatzResearch.WordTrace tailWord_851743 prefixEnd_851743 437353553102566285295411 := by
  unfold tailWord_851743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31065619353288051968359883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20710412902192034645573255 31065619353288051968359883)
  ·
    refine ⟨46598429029932077952539825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31065619353288051968359883 46598429029932077952539825)
    ·
      refine ⟨34948821772449058464404869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46598429029932077952539825 34948821772449058464404869)
      ·
        refine ⟨6552904082334198462075913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34948821772449058464404869 6552904082334198462075913)
        ·
          refine ⟨4914678061750648846556935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6552904082334198462075913 4914678061750648846556935)
          ·
            refine ⟨7372017092625973269835403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914678061750648846556935 7372017092625973269835403)
            ·
              refine ⟨11058025638938959904753105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372017092625973269835403 11058025638938959904753105)
              ·
                refine ⟨8293519229204219928564829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058025638938959904753105 8293519229204219928564829)
                ·
                  refine ⟨3110069710951582473211811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8293519229204219928564829 3110069710951582473211811)
                  ·
                    refine ⟨4665104566427373709817717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3110069710951582473211811 4665104566427373709817717)
                    ·
                      refine ⟨437353553102566285295411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4665104566427373709817717 437353553102566285295411)
                      ·
                        rfl

theorem cell23_851743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_851743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851743 prefixEnd_851743 := by exact prefixLift 851743
  have htrace : WordTrace (prefixWord ++ tailWord_851743) baseStart_851743 baseEnd_851743 := by
    simpa [prefixWord, tailWord_851743, baseEnd_851743] using wordTrace_append hprefix tailTrace_851743
  have hstable : (prefixWord ++ tailWord_851743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851743).length < 2 ^ (prefixWord ++ tailWord_851743).sum := by decide
  have hdescent : baseEnd_851743 < baseStart_851743 := by decide
  rcases family_descends (prefixWord ++ tailWord_851743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851784 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_851784 : Nat := 118140960795 + 851784 * 2 ^ 59
def prefixEnd_851784 : Nat := 4983230072969 + 3 ^ 40 * 851784 * 2
def baseEnd_851784 : Nat := 145791535269800208294241

theorem tailTrace_851784 : CollatzResearch.WordTrace tailWord_851784 prefixEnd_851784 145791535269800208294241 := by
  unfold tailWord_851784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533557373069757985301203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20711409830759677313734937 15533557373069757985301203)
  ·
    refine ⟨23300336059604636977951805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15533557373069757985301203 23300336059604636977951805)
    ·
      refine ⟨8737626022351738866731927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23300336059604636977951805 8737626022351738866731927)
      ·
        refine ⟨13106439033527608300097891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8737626022351738866731927 13106439033527608300097891)
        ·
          refine ⟨19659658550291412450146837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13106439033527608300097891 19659658550291412450146837)
          ·
            refine ⟨921546494544909958600633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19659658550291412450146837 921546494544909958600633)
            ·
              refine ⟨691159870908682468950475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921546494544909958600633 691159870908682468950475)
              ·
                refine ⟨1036739806363023703425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691159870908682468950475 1036739806363023703425713)
                ·
                  refine ⟨777554854772267777569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036739806363023703425713 777554854772267777569285)
                  ·
                    refine ⟨145791535269800208294241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777554854772267777569285 145791535269800208294241)
                    ·
                      rfl

theorem cell23_851784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_851784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851784 prefixEnd_851784 := by exact prefixLift 851784
  have htrace : WordTrace (prefixWord ++ tailWord_851784) baseStart_851784 baseEnd_851784 := by
    simpa [prefixWord, tailWord_851784, baseEnd_851784] using wordTrace_append hprefix tailTrace_851784
  have hstable : (prefixWord ++ tailWord_851784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851784).length < 2 ^ (prefixWord ++ tailWord_851784).sum := by decide
  have hdescent : baseEnd_851784 < baseStart_851784 := by decide
  rcases family_descends (prefixWord ++ tailWord_851784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851794 : List Nat := [3, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_851794 : Nat := 118140960795 + 851794 * 2 ^ 59
def prefixEnd_851794 : Nat := 4983230072969 + 3 ^ 40 * 851794 * 2
def baseEnd_851794 : Nat := 437379740615945585757677

theorem tailTrace_851794 : CollatzResearch.WordTrace tailWord_851794 prefixEnd_851794 437379740615945585757677 := by
  unfold tailWord_851794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766869869025821919616609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20711652984068858452310957 7766869869025821919616609)
  ·
    refine ⟨5825152401769366439712457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7766869869025821919616609 5825152401769366439712457)
    ·
      refine ⟨4368864301327024829784343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5825152401769366439712457 4368864301327024829784343)
      ·
        refine ⟨6553296451990537244676515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368864301327024829784343 6553296451990537244676515)
        ·
          refine ⟨9829944677985805867014773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553296451990537244676515 9829944677985805867014773)
          ·
            refine ⟨921557313561169300032635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9829944677985805867014773 921557313561169300032635)
            ·
              refine ⟨1382335970341753950048953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921557313561169300032635 1382335970341753950048953)
              ·
                refine ⟨1036751977756315462536715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382335970341753950048953 1036751977756315462536715)
                ·
                  refine ⟨1555127966634473193805073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036751977756315462536715 1555127966634473193805073)
                  ·
                    refine ⟨1166345974975854895353805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555127966634473193805073 1166345974975854895353805)
                    ·
                      refine ⟨437379740615945585757677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166345974975854895353805 437379740615945585757677)
                      ·
                        rfl

theorem cell23_851794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_851794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851794 prefixEnd_851794 := by exact prefixLift 851794
  have htrace : WordTrace (prefixWord ++ tailWord_851794) baseStart_851794 baseEnd_851794 := by
    simpa [prefixWord, tailWord_851794, baseEnd_851794] using wordTrace_append hprefix tailTrace_851794
  have hstable : (prefixWord ++ tailWord_851794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851794).length < 2 ^ (prefixWord ++ tailWord_851794).sum := by decide
  have hdescent : baseEnd_851794 < baseStart_851794 := by decide
  rcases family_descends (prefixWord ++ tailWord_851794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851817 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 1, 3, 2]
def baseStart_851817 : Nat := 118140960795 + 851817 * 2 ^ 59
def prefixEnd_851817 : Nat := 4983230072969 + 3 ^ 40 * 851817 * 2
def baseEnd_851817 : Nat := 437391550670998995770071

theorem tailTrace_851817 : CollatzResearch.WordTrace tailWord_851817 prefixEnd_851817 437391550670998995770071 := by
  unfold tailWord_851817
  simp only [CollatzResearch.WordTrace]
  refine ⟨31068318355019962606553705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20712212236679975071035803 31068318355019962606553705)
  ·
    refine ⟨23301238766264971954915279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31068318355019962606553705 23301238766264971954915279)
    ·
      refine ⟨34951858149397457932372919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23301238766264971954915279 34951858149397457932372919)
      ·
        refine ⟨52427787224096186898559379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34951858149397457932372919 52427787224096186898559379)
        ·
          refine ⟨78641680836144280347839069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52427787224096186898559379 78641680836144280347839069)
          ·
            refine ⟨29490630313554105130439651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78641680836144280347839069 29490630313554105130439651)
            ·
              refine ⟨44235945470331157695659477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29490630313554105130439651 44235945470331157695659477)
              ·
                refine ⟨1036779971960886508492019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44235945470331157695659477 1036779971960886508492019)
                ·
                  refine ⟨1555169957941329762738029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036779971960886508492019 1555169957941329762738029)
                  ·
                    refine ⟨583188734227998661026761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555169957941329762738029 583188734227998661026761)
                    ·
                      refine ⟨437391550670998995770071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583188734227998661026761 437391550670998995770071)
                      ·
                        rfl

theorem cell23_851817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3, 2].length) (baseStart_851817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851817 prefixEnd_851817 := by exact prefixLift 851817
  have htrace : WordTrace (prefixWord ++ tailWord_851817) baseStart_851817 baseEnd_851817 := by
    simpa [prefixWord, tailWord_851817, baseEnd_851817] using wordTrace_append hprefix tailTrace_851817
  have hstable : (prefixWord ++ tailWord_851817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851817).length < 2 ^ (prefixWord ++ tailWord_851817).sum := by decide
  have hdescent : baseEnd_851817 < baseStart_851817 := by decide
  rcases family_descends (prefixWord ++ tailWord_851817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851862 : List Nat := [5, 3, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_851862 : Nat := 118140960795 + 851862 * 2 ^ 59
def prefixEnd_851862 : Nat := 4983230072969 + 3 ^ 40 * 851862 * 2
def baseEnd_851862 : Nat := 437414657300451319707365

theorem tailTrace_851862 : CollatzResearch.WordTrace tailWord_851862 prefixEnd_851862 437414657300451319707365 := by
  unfold tailWord_851862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941872477491058455746365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20713306426571290194627893 1941872477491058455746365)
  ·
    refine ⟨728202179059146920904887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1941872477491058455746365 728202179059146920904887)
    ·
      refine ⟨1092303268588720381357331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728202179059146920904887 1092303268588720381357331)
      ·
        refine ⟨1638454902883080572035997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092303268588720381357331 1638454902883080572035997)
        ·
          refine ⟨614420588581155214513499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1638454902883080572035997 614420588581155214513499)
          ·
            refine ⟨921630882871732821770249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614420588581155214513499 921630882871732821770249)
            ·
              refine ⟨691223162153799616327687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921630882871732821770249 691223162153799616327687)
              ·
                refine ⟨1036834743230699424491531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691223162153799616327687 1036834743230699424491531)
                ·
                  refine ⟨1555252114846049136737297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036834743230699424491531 1555252114846049136737297)
                  ·
                    refine ⟨1166439086134536852552973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555252114846049136737297 1166439086134536852552973)
                    ·
                      refine ⟨437414657300451319707365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166439086134536852552973 437414657300451319707365)
                      ·
                        rfl

theorem cell23_851862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_851862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851862 prefixEnd_851862 := by exact prefixLift 851862
  have htrace : WordTrace (prefixWord ++ tailWord_851862) baseStart_851862 baseEnd_851862 := by
    simpa [prefixWord, tailWord_851862, baseEnd_851862] using wordTrace_append hprefix tailTrace_851862
  have hstable : (prefixWord ++ tailWord_851862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851862).length < 2 ^ (prefixWord ++ tailWord_851862).sum := by decide
  have hdescent : baseEnd_851862 < baseStart_851862 := by decide
  rcases family_descends (prefixWord ++ tailWord_851862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851868 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_851868 : Nat := 118140960795 + 851868 * 2 ^ 59
def prefixEnd_851868 : Nat := 4983230072969 + 3 ^ 40 * 851868 * 2
def baseEnd_851868 : Nat := 437417738184378296232337

theorem tailTrace_851868 : CollatzResearch.WordTrace tailWord_851868 prefixEnd_851868 437417738184378296232337 := by
  unfold tailWord_851868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535089238917599158330129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20713452318556798877773505 15535089238917599158330129)
  ·
    refine ⟨11651316929188199368747597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15535089238917599158330129 11651316929188199368747597)
    ·
      refine ⟨4369243848445574763280349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11651316929188199368747597 4369243848445574763280349)
      ·
        refine ⟨1638466443167090536230131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4369243848445574763280349 1638466443167090536230131)
        ·
          refine ⟨2457699664750635804345197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638466443167090536230131 2457699664750635804345197)
          ·
            refine ⟨921637374281488426629449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2457699664750635804345197 921637374281488426629449)
            ·
              refine ⟨691228030711116319972087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921637374281488426629449 691228030711116319972087)
              ·
                refine ⟨1036842046066674479958131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691228030711116319972087 1036842046066674479958131)
                ·
                  refine ⟨1555263069100011719937197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036842046066674479958131 1555263069100011719937197)
                  ·
                    refine ⟨583223650912504394976449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1555263069100011719937197 583223650912504394976449)
                    ·
                      refine ⟨437417738184378296232337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583223650912504394976449 437417738184378296232337)
                      ·
                        rfl

theorem cell23_851868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_851868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851868 prefixEnd_851868 := by exact prefixLift 851868
  have htrace : WordTrace (prefixWord ++ tailWord_851868) baseStart_851868 baseEnd_851868 := by
    simpa [prefixWord, tailWord_851868, baseEnd_851868] using wordTrace_append hprefix tailTrace_851868
  have hstable : (prefixWord ++ tailWord_851868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851868).length < 2 ^ (prefixWord ++ tailWord_851868).sum := by decide
  have hdescent : baseEnd_851868 < baseStart_851868 := by decide
  rcases family_descends (prefixWord ++ tailWord_851868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851883 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 5, 7]
def baseStart_851883 : Nat := 118140960795 + 851883 * 2 ^ 59
def prefixEnd_851883 : Nat := 4983230072969 + 3 ^ 40 * 851883 * 2
def baseEnd_851883 : Nat := 145808480131398579181589

theorem tailTrace_851883 : CollatzResearch.WordTrace tailWord_851883 prefixEnd_851883 145808480131398579181589 := by
  unfold tailWord_851883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31070725572780855878456303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20713817048520570585637535 31070725572780855878456303)
  ·
    refine ⟨46606088359171283817684455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31070725572780855878456303 46606088359171283817684455)
    ·
      refine ⟨69909132538756925726526683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46606088359171283817684455 69909132538756925726526683)
      ·
        refine ⟨104863698808135388589790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69909132538756925726526683 104863698808135388589790025)
        ·
          refine ⟨78647774106101541442342519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104863698808135388589790025 78647774106101541442342519)
          ·
            refine ⟨117971661159152312163513779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78647774106101541442342519 117971661159152312163513779)
            ·
              refine ⟨176957491738728468245270669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117971661159152312163513779 176957491738728468245270669)
              ·
                refine ⟨66359059402023175591976501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176957491738728468245270669 66359059402023175591976501)
                ·
                  refine ⟨6221161818939672711747797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66359059402023175591976501 6221161818939672711747797)
                  ·
                    refine ⟨145808480131398579181589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6221161818939672711747797 145808480131398579181589)
                    ·
                      rfl

theorem cell23_851883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_851883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851883 prefixEnd_851883 := by exact prefixLift 851883
  have htrace : WordTrace (prefixWord ++ tailWord_851883) baseStart_851883 baseEnd_851883 := by
    simpa [prefixWord, tailWord_851883, baseEnd_851883] using wordTrace_append hprefix tailTrace_851883
  have hstable : (prefixWord ++ tailWord_851883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851883).length < 2 ^ (prefixWord ++ tailWord_851883).sum := by decide
  have hdescent : baseEnd_851883 < baseStart_851883 := by decide
  rcases family_descends (prefixWord ++ tailWord_851883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851920 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_851920 : Nat := 118140960795 + 851920 * 2 ^ 59
def prefixEnd_851920 : Nat := 4983230072969 + 3 ^ 40 * 851920 * 2
def baseEnd_851920 : Nat := 437444439178412092782097

theorem tailTrace_851920 : CollatzResearch.WordTrace tailWord_851920 prefixEnd_851920 437444439178412092782097 := by
  unfold tailWord_851920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536037536823405598776607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20714716715764540798368809 15536037536823405598776607)
  ·
    refine ⟨23304056305235108398164911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15536037536823405598776607 23304056305235108398164911)
    ·
      refine ⟨34956084457852662597247367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23304056305235108398164911 34956084457852662597247367)
      ·
        refine ⟨52434126686778993895871051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34956084457852662597247367 52434126686778993895871051)
        ·
          refine ⟨78651190030168490843806577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52434126686778993895871051 78651190030168490843806577)
          ·
            refine ⟨58988392522626368132854933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78651190030168490843806577 58988392522626368132854933)
            ·
              refine ⟨2765080899498111006227575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58988392522626368132854933 2765080899498111006227575)
              ·
                refine ⟨4147621349247166509341363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765080899498111006227575 4147621349247166509341363)
                ·
                  refine ⟨6221432023870749764012045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147621349247166509341363 6221432023870749764012045)
                  ·
                    refine ⟨2333037008951531161504517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6221432023870749764012045 2333037008951531161504517)
                    ·
                      refine ⟨437444439178412092782097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2333037008951531161504517 437444439178412092782097)
                      ·
                        rfl

theorem cell23_851920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_851920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851920 prefixEnd_851920 := by exact prefixLift 851920
  have htrace : WordTrace (prefixWord ++ tailWord_851920) baseStart_851920 baseEnd_851920 := by
    simpa [prefixWord, tailWord_851920, baseEnd_851920] using wordTrace_append hprefix tailTrace_851920
  have hstable : (prefixWord ++ tailWord_851920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851920).length < 2 ^ (prefixWord ++ tailWord_851920).sum := by decide
  have hdescent : baseEnd_851920 < baseStart_851920 := by decide
  rcases family_descends (prefixWord ++ tailWord_851920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851937 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_851937 : Nat := 118140960795 + 851937 * 2 ^ 59
def prefixEnd_851937 : Nat := 4983230072969 + 3 ^ 40 * 851937 * 2
def baseEnd_851937 : Nat := 437453168349538526269519

theorem tailTrace_851937 : CollatzResearch.WordTrace tailWord_851937 prefixEnd_851937 437453168349538526269519 := by
  unfold tailWord_851937
  simp only [CollatzResearch.WordTrace]
  refine ⟨31072695114585223100922065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20715130076390148733948043 31072695114585223100922065)
  ·
    refine ⟨23304521335938917325691549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31072695114585223100922065 23304521335938917325691549)
    ·
      refine ⟨8739195500977093997134331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23304521335938917325691549 8739195500977093997134331)
      ·
        refine ⟨13108793251465640995701497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739195500977093997134331 13108793251465640995701497)
        ·
          refine ⟨9831594938599230746776123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108793251465640995701497 9831594938599230746776123)
          ·
            refine ⟨14747392407898846120164185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831594938599230746776123 14747392407898846120164185)
            ·
              refine ⟨11060544305924134590123139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747392407898846120164185 11060544305924134590123139)
              ·
                refine ⟨16590816458886201885184709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060544305924134590123139 16590816458886201885184709)
                ·
                  refine ⟨3110778086041162853472133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16590816458886201885184709 3110778086041162853472133)
                  ·
                    refine ⟨583270891132718035026025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3110778086041162853472133 583270891132718035026025)
                    ·
                      refine ⟨437453168349538526269519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583270891132718035026025 437453168349538526269519)
                      ·
                        rfl

theorem cell23_851937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_851937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851937 prefixEnd_851937 := by exact prefixLift 851937
  have htrace : WordTrace (prefixWord ++ tailWord_851937) baseStart_851937 baseEnd_851937 := by
    simpa [prefixWord, tailWord_851937, baseEnd_851937] using wordTrace_append hprefix tailTrace_851937
  have hstable : (prefixWord ++ tailWord_851937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851937).length < 2 ^ (prefixWord ++ tailWord_851937).sum := by decide
  have hdescent : baseEnd_851937 < baseStart_851937 := by decide
  rcases family_descends (prefixWord ++ tailWord_851937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851938 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_851938 : Nat := 118140960795 + 851938 * 2 ^ 59
def prefixEnd_851938 : Nat := 4983230072969 + 3 ^ 40 * 851938 * 2
def baseEnd_851938 : Nat := 48605964647799224706335

theorem tailTrace_851938 : CollatzResearch.WordTrace tailWord_851938 prefixEnd_851938 48605964647799224706335 := by
  unfold tailWord_851938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768182896895400067927117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20715154391721066847805645 7768182896895400067927117)
  ·
    refine ⟨2913068586335775025472669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7768182896895400067927117 2913068586335775025472669)
    ·
      refine ⟨1092400719875915634552251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2913068586335775025472669 1092400719875915634552251)
      ·
        refine ⟨1638601079813873451828377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092400719875915634552251 1638601079813873451828377)
        ·
          refine ⟨1228950809860405088871283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1638601079813873451828377 1228950809860405088871283)
          ·
            refine ⟨1843426214790607633306925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228950809860405088871283 1843426214790607633306925)
            ·
              refine ⟨691284830546477862490097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1843426214790607633306925 691284830546477862490097)
              ·
                refine ⟨518463622909858396867573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691284830546477862490097 518463622909858396867573)
                ·
                  refine ⟨48605964647799224706335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518463622909858396867573 48605964647799224706335)
                  ·
                    rfl

theorem cell23_851938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_851938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_851938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_851938 prefixEnd_851938 := by exact prefixLift 851938
  have htrace : WordTrace (prefixWord ++ tailWord_851938) baseStart_851938 baseEnd_851938 := by
    simpa [prefixWord, tailWord_851938, baseEnd_851938] using wordTrace_append hprefix tailTrace_851938
  have hstable : (prefixWord ++ tailWord_851938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851938).length < 2 ^ (prefixWord ++ tailWord_851938).sum := by decide
  have hdescent : baseEnd_851938 < baseStart_851938 := by decide
  rcases family_descends (prefixWord ++ tailWord_851938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852027 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 6, 2]
def baseStart_852027 : Nat := 118140960795 + 852027 * 2 ^ 59
def prefixEnd_852027 : Nat := 4983230072969 + 3 ^ 40 * 852027 * 2
def baseEnd_852027 : Nat := 437499381608443174144105

theorem tailTrace_852027 : CollatzResearch.WordTrace tailWord_852027 prefixEnd_852027 437499381608443174144105 := by
  unfold tailWord_852027
  simp only [CollatzResearch.WordTrace]
  refine ⟨31075977684259168471698335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20717318456172778981132223 31075977684259168471698335)
  ·
    refine ⟨46613966526388752707547503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31075977684259168471698335 46613966526388752707547503)
    ·
      refine ⟨69920949789583129061321255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46613966526388752707547503 69920949789583129061321255)
      ·
        refine ⟨104881424684374693591981883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69920949789583129061321255 104881424684374693591981883)
        ·
          refine ⟨157322137026562040387972825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104881424684374693591981883 157322137026562040387972825)
          ·
            refine ⟨117991602769921530290979619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157322137026562040387972825 117991602769921530290979619)
            ·
              refine ⟨176987404154882295436469429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117991602769921530290979619 176987404154882295436469429)
              ·
                refine ⟨16592569139520215197169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176987404154882295436469429 16592569139520215197169009)
                ·
                  refine ⟨12444426854640161397876757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16592569139520215197169009 12444426854640161397876757)
                  ·
                    refine ⟨583332508811257565525473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12444426854640161397876757 583332508811257565525473)
                    ·
                      refine ⟨437499381608443174144105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583332508811257565525473 437499381608443174144105)
                      ·
                        rfl

theorem cell23_852027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6, 2].length) (baseStart_852027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852027 prefixEnd_852027 := by exact prefixLift 852027
  have htrace : WordTrace (prefixWord ++ tailWord_852027) baseStart_852027 baseEnd_852027 := by
    simpa [prefixWord, tailWord_852027, baseEnd_852027] using wordTrace_append hprefix tailTrace_852027
  have hstable : (prefixWord ++ tailWord_852027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852027).length < 2 ^ (prefixWord ++ tailWord_852027).sum := by decide
  have hdescent : baseEnd_852027 < baseStart_852027 := by decide
  rcases family_descends (prefixWord ++ tailWord_852027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852037 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_852037 : Nat := 118140960795 + 852037 * 2 ^ 59
def prefixEnd_852037 : Nat := 4983230072969 + 3 ^ 40 * 852037 * 2
def baseEnd_852037 : Nat := 145834838804996045006353

theorem tailTrace_852037 : CollatzResearch.WordTrace tailWord_852037 prefixEnd_852037 145834838804996045006353 := by
  unfold tailWord_852037
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076342414222940179562365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20717561609481960119708243 31076342414222940179562365)
  ·
    refine ⟨11653628405333602567335887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31076342414222940179562365 11653628405333602567335887)
    ·
      refine ⟨17480442608000403851003831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11653628405333602567335887 17480442608000403851003831)
      ·
        refine ⟨26220663912000605776505747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17480442608000403851003831 26220663912000605776505747)
        ·
          refine ⟨39330995868000908664758621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26220663912000605776505747 39330995868000908664758621)
          ·
            refine ⟨14749123450500340749284483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39330995868000908664758621 14749123450500340749284483)
            ·
              refine ⟨22123685175750511123926725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14749123450500340749284483 22123685175750511123926725)
              ·
                refine ⟨4148190970453220835736261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22123685175750511123926725 4148190970453220835736261)
                ·
                  refine ⟨777785806959978906700549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4148190970453220835736261 777785806959978906700549)
                  ·
                    refine ⟨145834838804996045006353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777785806959978906700549 145834838804996045006353)
                    ·
                      rfl

theorem cell23_852037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_852037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852037 prefixEnd_852037 := by exact prefixLift 852037
  have htrace : WordTrace (prefixWord ++ tailWord_852037) baseStart_852037 baseEnd_852037 := by
    simpa [prefixWord, tailWord_852037, baseEnd_852037] using wordTrace_append hprefix tailTrace_852037
  have hstable : (prefixWord ++ tailWord_852037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852037).length < 2 ^ (prefixWord ++ tailWord_852037).sum := by decide
  have hdescent : baseEnd_852037 < baseStart_852037 := by decide
  rcases family_descends (prefixWord ++ tailWord_852037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852071 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 2, 4]
def baseStart_852071 : Nat := 118140960795 + 852071 * 2 ^ 59
def prefixEnd_852071 : Nat := 4983230072969 + 3 ^ 40 * 852071 * 2
def baseEnd_852071 : Nat := 145840658252413667331301

theorem tailTrace_852071 : CollatzResearch.WordTrace tailWord_852071 prefixEnd_852071 145840658252413667331301 := by
  unfold tailWord_852071
  simp only [CollatzResearch.WordTrace]
  refine ⟨31077582496099763986300067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20718388330733175990866711 31077582496099763986300067)
  ·
    refine ⟨46616373744149645979450101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31077582496099763986300067 46616373744149645979450101)
    ·
      refine ⟨4370285038514029310573447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46616373744149645979450101 4370285038514029310573447)
      ·
        refine ⟨6555427557771043965860171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370285038514029310573447 6555427557771043965860171)
        ·
          refine ⟨9833141336656565948790257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555427557771043965860171 9833141336656565948790257)
          ·
            refine ⟨7374856002492424461592693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9833141336656565948790257 7374856002492424461592693)
            ·
              refine ⟨691392750233664793274315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7374856002492424461592693 691392750233664793274315)
              ·
                refine ⟨1037089125350497189911473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691392750233664793274315 1037089125350497189911473)
                ·
                  refine ⟨777816844012872892433605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037089125350497189911473 777816844012872892433605)
                  ·
                    refine ⟨145840658252413667331301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777816844012872892433605 145840658252413667331301)
                    ·
                      rfl

theorem cell23_852071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_852071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852071 prefixEnd_852071 := by exact prefixLift 852071
  have htrace : WordTrace (prefixWord ++ tailWord_852071) baseStart_852071 baseEnd_852071 := by
    simpa [prefixWord, tailWord_852071, baseEnd_852071] using wordTrace_append hprefix tailTrace_852071
  have hstable : (prefixWord ++ tailWord_852071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852071).length < 2 ^ (prefixWord ++ tailWord_852071).sum := by decide
  have hdescent : baseEnd_852071 < baseStart_852071 := by decide
  rcases family_descends (prefixWord ++ tailWord_852071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852074 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_852074 : Nat := 118140960795 + 852074 * 2 ^ 59
def prefixEnd_852074 : Nat := 4983230072969 + 3 ^ 40 * 852074 * 2
def baseEnd_852074 : Nat := 437523515199204490256389

theorem tailTrace_852074 : CollatzResearch.WordTrace tailWord_852074 prefixEnd_852074 437523515199204490256389 := by
  unfold tailWord_852074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769422978772223874664819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20718461276725930332439517 7769422978772223874664819)
  ·
    refine ⟨11654134468158335811997229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769422978772223874664819 11654134468158335811997229)
    ·
      refine ⟨4370300425559375929498961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11654134468158335811997229 4370300425559375929498961)
      ·
        refine ⟨3277725319169531947124221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4370300425559375929498961 3277725319169531947124221)
        ·
          refine ⟨1229146994688574480171583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3277725319169531947124221 1229146994688574480171583)
          ·
            refine ⟨1843720492032861720257375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229146994688574480171583 1843720492032861720257375)
            ·
              refine ⟨2765580738049292580386063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843720492032861720257375 2765580738049292580386063)
              ·
                refine ⟨4148371107073938870579095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765580738049292580386063 4148371107073938870579095)
                ·
                  refine ⟨6222556660610908305868643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148371107073938870579095 6222556660610908305868643)
                  ·
                    refine ⟨9333834990916362458802965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222556660610908305868643 9333834990916362458802965)
                    ·
                      refine ⟨437523515199204490256389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9333834990916362458802965 437523515199204490256389)
                      ·
                        rfl

theorem cell23_852074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_852074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852074 prefixEnd_852074 := by exact prefixLift 852074
  have htrace : WordTrace (prefixWord ++ tailWord_852074) baseStart_852074 baseEnd_852074 := by
    simpa [prefixWord, tailWord_852074, baseEnd_852074] using wordTrace_append hprefix tailTrace_852074
  have hstable : (prefixWord ++ tailWord_852074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852074).length < 2 ^ (prefixWord ++ tailWord_852074).sum := by decide
  have hdescent : baseEnd_852074 < baseStart_852074 := by decide
  rcases family_descends (prefixWord ++ tailWord_852074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852117 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_852117 : Nat := 118140960795 + 852117 * 2 ^ 59
def prefixEnd_852117 : Nat := 4983230072969 + 3 ^ 40 * 852117 * 2
def baseEnd_852117 : Nat := 437545594867347822018691

theorem tailTrace_852117 : CollatzResearch.WordTrace tailWord_852117 prefixEnd_852117 437545594867347822018691 := by
  unfold tailWord_852117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079260253933113842474605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20719506835955409228316403 31079260253933113842474605)
  ·
    refine ⟨11654722595224917690927977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31079260253933113842474605 11654722595224917690927977)
    ·
      refine ⟨8741041946418688268195983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11654722595224917690927977 8741041946418688268195983)
      ·
        refine ⟨13111562919628032402293975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8741041946418688268195983 13111562919628032402293975)
        ·
          refine ⟨19667344379442048603440963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13111562919628032402293975 19667344379442048603440963)
          ·
            refine ⟨29501016569163072905161445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667344379442048603440963 29501016569163072905161445)
            ·
              refine ⟨5531440606718076169717771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29501016569163072905161445 5531440606718076169717771)
              ·
                refine ⟨8297160910077114254576657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531440606718076169717771 8297160910077114254576657)
                ·
                  refine ⟨6222870682557835690932493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8297160910077114254576657 6222870682557835690932493)
                  ·
                    refine ⟨2333576505959188384099685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6222870682557835690932493 2333576505959188384099685)
                    ·
                      refine ⟨437545594867347822018691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2333576505959188384099685 437545594867347822018691)
                      ·
                        rfl

theorem cell23_852117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_852117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852117 prefixEnd_852117 := by exact prefixLift 852117
  have htrace : WordTrace (prefixWord ++ tailWord_852117) baseStart_852117 baseEnd_852117 := by
    simpa [prefixWord, tailWord_852117, baseEnd_852117] using wordTrace_append hprefix tailTrace_852117
  have hstable : (prefixWord ++ tailWord_852117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852117).length < 2 ^ (prefixWord ++ tailWord_852117).sum := by decide
  have hdescent : baseEnd_852117 < baseStart_852117 := by decide
  rcases family_descends (prefixWord ++ tailWord_852117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852128 : List Nat := [2, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3]
def baseStart_852128 : Nat := 118140960795 + 852128 * 2 ^ 59
def prefixEnd_852128 : Nat := 4983230072969 + 3 ^ 40 * 852128 * 2
def baseEnd_852128 : Nat := 437551243154547278981141

theorem tailTrace_852128 : CollatzResearch.WordTrace tailWord_852128 prefixEnd_852128 437551243154547278981141 := by
  unfold tailWord_852128
  simp only [CollatzResearch.WordTrace]
  refine ⟨15539830728446631360562519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20719774304595508480750025 15539830728446631360562519)
  ·
    refine ⟨23309746092669947040843779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15539830728446631360562519 23309746092669947040843779)
    ·
      refine ⟨34964619139004920561265669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23309746092669947040843779 34964619139004920561265669)
      ·
        refine ⟨6555866088563422605237313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34964619139004920561265669 6555866088563422605237313)
        ·
          refine ⟨4916899566422566953927985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6555866088563422605237313 4916899566422566953927985)
          ·
            refine ⟨3687674674816925215445989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916899566422566953927985 3687674674816925215445989)
            ·
              refine ⟨691439001528173477896123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3687674674816925215445989 691439001528173477896123)
              ·
                refine ⟨1037158502292260216844185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691439001528173477896123 1037158502292260216844185)
                ·
                  refine ⟨777868876719195162633139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037158502292260216844185 777868876719195162633139)
                  ·
                    refine ⟨1166803315078792743949709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 777868876719195162633139 1166803315078792743949709)
                    ·
                      refine ⟨437551243154547278981141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166803315078792743949709 437551243154547278981141)
                      ·
                        rfl

theorem cell23_852128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_852128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852128 prefixEnd_852128 := by exact prefixLift 852128
  have htrace : WordTrace (prefixWord ++ tailWord_852128) baseStart_852128 baseEnd_852128 := by
    simpa [prefixWord, tailWord_852128, baseEnd_852128] using wordTrace_append hprefix tailTrace_852128
  have hstable : (prefixWord ++ tailWord_852128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852128).length < 2 ^ (prefixWord ++ tailWord_852128).sum := by decide
  have hdescent : baseEnd_852128 < baseStart_852128 := by decide
  rcases family_descends (prefixWord ++ tailWord_852128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852147 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_852147 : Nat := 118140960795 + 852147 * 2 ^ 59
def prefixEnd_852147 : Nat := 4983230072969 + 3 ^ 40 * 852147 * 2
def baseEnd_852147 : Nat := 437560999286982704643553

theorem tailTrace_852147 : CollatzResearch.WordTrace tailWord_852147 prefixEnd_852147 437560999286982704643553 := by
  unfold tailWord_852147
  simp only [CollatzResearch.WordTrace]
  refine ⟨31080354443824428966066695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20720236295882952644044463 31080354443824428966066695)
  ·
    refine ⟨46620531665736643449100043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31080354443824428966066695 46620531665736643449100043)
    ·
      refine ⟨69930797498604965173650065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46620531665736643449100043 69930797498604965173650065)
      ·
        refine ⟨52448098123953723880237549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69930797498604965173650065 52448098123953723880237549)
        ·
          refine ⟨19668036796482646455089081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52448098123953723880237549 19668036796482646455089081)
          ·
            refine ⟨14751027597361984841316811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19668036796482646455089081 14751027597361984841316811)
            ·
              refine ⟨22126541396042977261975217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14751027597361984841316811 22126541396042977261975217)
              ·
                refine ⟨16594906047032232946481413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22126541396042977261975217 16594906047032232946481413)
                ·
                  refine ⟨3111544883818543677465265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16594906047032232946481413 3111544883818543677465265)
                  ·
                    refine ⟨2333658662863907758098949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111544883818543677465265 2333658662863907758098949)
                    ·
                      refine ⟨437560999286982704643553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2333658662863907758098949 437560999286982704643553)
                      ·
                        rfl

theorem cell23_852147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_852147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852147 prefixEnd_852147 := by exact prefixLift 852147
  have htrace : WordTrace (prefixWord ++ tailWord_852147) baseStart_852147 baseEnd_852147 := by
    simpa [prefixWord, tailWord_852147, baseEnd_852147] using wordTrace_append hprefix tailTrace_852147
  have hstable : (prefixWord ++ tailWord_852147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852147).length < 2 ^ (prefixWord ++ tailWord_852147).sum := by decide
  have hdescent : baseEnd_852147 < baseStart_852147 := by decide
  rcases family_descends (prefixWord ++ tailWord_852147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852151 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_852151 : Nat := 118140960795 + 852151 * 2 ^ 59
def prefixEnd_852151 : Nat := 4983230072969 + 3 ^ 40 * 852151 * 2
def baseEnd_852151 : Nat := 437563053209600688993535

theorem tailTrace_852151 : CollatzResearch.WordTrace tailWord_852151 prefixEnd_852151 437563053209600688993535 := by
  unfold tailWord_852151
  simp only [CollatzResearch.WordTrace]
  refine ⟨31080500335809937649212307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20720333557206625099474871 31080500335809937649212307)
  ·
    refine ⟨46620750503714906473818461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31080500335809937649212307 46620750503714906473818461)
    ·
      refine ⟨17482781438893089927681923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46620750503714906473818461 17482781438893089927681923)
      ·
        refine ⟨26224172158339634891522885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17482781438893089927681923 26224172158339634891522885)
        ·
          refine ⟨4917032279688681542160541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26224172158339634891522885 4917032279688681542160541)
          ·
            refine ⟨1843887104883255578310203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4917032279688681542160541 1843887104883255578310203)
            ·
              refine ⟨2765830657324883367465305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843887104883255578310203 2765830657324883367465305)
              ·
                refine ⟨2074372992993662525598979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765830657324883367465305 2074372992993662525598979)
                ·
                  refine ⟨3111559489490493788398469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074372992993662525598979 3111559489490493788398469)
                  ·
                    refine ⟨583417404279467585324713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111559489490493788398469 583417404279467585324713)
                    ·
                      refine ⟨437563053209600688993535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583417404279467585324713 437563053209600688993535)
                      ·
                        rfl

theorem cell23_852151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_852151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852151 prefixEnd_852151 := by exact prefixLift 852151
  have htrace : WordTrace (prefixWord ++ tailWord_852151) baseStart_852151 baseEnd_852151 := by
    simpa [prefixWord, tailWord_852151, baseEnd_852151] using wordTrace_append hprefix tailTrace_852151
  have hstable : (prefixWord ++ tailWord_852151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852151).length < 2 ^ (prefixWord ++ tailWord_852151).sum := by decide
  have hdescent : baseEnd_852151 < baseStart_852151 := by decide
  rcases family_descends (prefixWord ++ tailWord_852151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852162 : List Nat := [3, 5, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_852162 : Nat := 118140960795 + 852162 * 2 ^ 59
def prefixEnd_852162 : Nat := 4983230072969 + 3 ^ 40 * 852162 * 2
def baseEnd_852162 : Nat := 437568701496800145955985

theorem tailTrace_852162 : CollatzResearch.WordTrace tailWord_852162 prefixEnd_852162 437568701496800145955985 := by
  unfold tailWord_852162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770225384692521631965685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20720601025846724351908493 7770225384692521631965685)
  ·
    refine ⟨728458629814923902996783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7770225384692521631965685 728458629814923902996783)
    ·
      refine ⟨1092687944722385854495175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728458629814923902996783 1092687944722385854495175)
      ·
        refine ⟨1639031917083578781742763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092687944722385854495175 1639031917083578781742763)
        ·
          refine ⟨2458547875625368172614145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639031917083578781742763 2458547875625368172614145)
          ·
            refine ⟨1843910906719026129460609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458547875625368172614145 1843910906719026129460609)
            ·
              refine ⟨1382933180039269597095457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843910906719026129460609 1382933180039269597095457)
              ·
                refine ⟨1037199885029452197821593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382933180039269597095457 1037199885029452197821593)
                ·
                  refine ⟨777899913772089148366195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037199885029452197821593 777899913772089148366195)
                  ·
                    refine ⟨1166849870658133722549293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 777899913772089148366195 1166849870658133722549293)
                    ·
                      refine ⟨437568701496800145955985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166849870658133722549293 437568701496800145955985)
                      ·
                        rfl

theorem cell23_852162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_852162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852162 prefixEnd_852162 := by exact prefixLift 852162
  have htrace : WordTrace (prefixWord ++ tailWord_852162) baseStart_852162 baseEnd_852162 := by
    simpa [prefixWord, tailWord_852162, baseEnd_852162] using wordTrace_append hprefix tailTrace_852162
  have hstable : (prefixWord ++ tailWord_852162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852162).length < 2 ^ (prefixWord ++ tailWord_852162).sum := by decide
  have hdescent : baseEnd_852162 < baseStart_852162 := by decide
  rcases family_descends (prefixWord ++ tailWord_852162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852181 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_852181 : Nat := 118140960795 + 852181 * 2 ^ 59
def prefixEnd_852181 : Nat := 4983230072969 + 3 ^ 40 * 852181 * 2
def baseEnd_852181 : Nat := 437578457629235571618397

theorem tailTrace_852181 : CollatzResearch.WordTrace tailWord_852181 prefixEnd_852181 437578457629235571618397 := by
  unfold tailWord_852181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081594525701252772804397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20721063017134168515202931 31081594525701252772804397)
  ·
    refine ⟨11655597947137969789801649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31081594525701252772804397 11655597947137969789801649)
    ·
      refine ⟨8741698460353477342351237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11655597947137969789801649 8741698460353477342351237)
      ·
        refine ⟨1639068461316277001690857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8741698460353477342351237 1639068461316277001690857)
        ·
          refine ⟨1229301345987207751268143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1639068461316277001690857 1229301345987207751268143)
          ·
            refine ⟨1843952018980811626902215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229301345987207751268143 1843952018980811626902215)
            ·
              refine ⟨2765928028471217440353323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843952018980811626902215 2765928028471217440353323)
              ·
                refine ⟨4148892042706826160529985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765928028471217440353323 4148892042706826160529985)
                ·
                  refine ⟨3111669032030119620397489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148892042706826160529985 3111669032030119620397489)
                  ·
                    refine ⟨2333751774022589715298117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111669032030119620397489 2333751774022589715298117)
                    ·
                      refine ⟨437578457629235571618397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2333751774022589715298117 437578457629235571618397)
                      ·
                        rfl

theorem cell23_852181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_852181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852181 prefixEnd_852181 := by exact prefixLift 852181
  have htrace : WordTrace (prefixWord ++ tailWord_852181) baseStart_852181 baseEnd_852181 := by
    simpa [prefixWord, tailWord_852181, baseEnd_852181] using wordTrace_append hprefix tailTrace_852181
  have hstable : (prefixWord ++ tailWord_852181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852181).length < 2 ^ (prefixWord ++ tailWord_852181).sum := by decide
  have hdescent : baseEnd_852181 < baseStart_852181 := by decide
  rcases family_descends (prefixWord ++ tailWord_852181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852184 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_852184 : Nat := 118140960795 + 852184 * 2 ^ 59
def prefixEnd_852184 : Nat := 4983230072969 + 3 ^ 40 * 852184 * 2
def baseEnd_852184 : Nat := 437579998071199059880883

theorem tailTrace_852184 : CollatzResearch.WordTrace tailWord_852184 prefixEnd_852184 437579998071199059880883 := by
  unfold tailWord_852184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540851972345192142581803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20721135963126922856775737 15540851972345192142581803)
  ·
    refine ⟨23311277958517788213872705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15540851972345192142581803 23311277958517788213872705)
    ·
      refine ⟨17483458468888341160404529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23311277958517788213872705 17483458468888341160404529)
      ·
        refine ⟨13112593851666255870303397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17483458468888341160404529 13112593851666255870303397)
        ·
          refine ⟨2458611347187422975681887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13112593851666255870303397 2458611347187422975681887)
          ·
            refine ⟨3687917020781134463522831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458611347187422975681887 3687917020781134463522831)
            ·
              refine ⟨5531875531171701695284247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687917020781134463522831 5531875531171701695284247)
              ·
                refine ⟨8297813296757552542926371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531875531171701695284247 8297813296757552542926371)
                ·
                  refine ⟨12446719945136328814389557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297813296757552542926371 12446719945136328814389557)
                  ·
                    refine ⟨1166879994856530826349021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12446719945136328814389557 1166879994856530826349021)
                    ·
                      refine ⟨437579998071199059880883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1166879994856530826349021 437579998071199059880883)
                      ·
                        rfl

theorem cell23_852184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_852184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852184 prefixEnd_852184 := by exact prefixLift 852184
  have htrace : WordTrace (prefixWord ++ tailWord_852184) baseStart_852184 baseEnd_852184 := by
    simpa [prefixWord, tailWord_852184, baseEnd_852184] using wordTrace_append hprefix tailTrace_852184
  have hstable : (prefixWord ++ tailWord_852184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852184).length < 2 ^ (prefixWord ++ tailWord_852184).sum := by decide
  have hdescent : baseEnd_852184 < baseStart_852184 := by decide
  rcases family_descends (prefixWord ++ tailWord_852184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852187 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 6, 5]
def baseStart_852187 : Nat := 118140960795 + 852187 * 2 ^ 59
def prefixEnd_852187 : Nat := 4983230072969 + 3 ^ 40 * 852187 * 2
def baseEnd_852187 : Nat := 145860512837720849381123

theorem tailTrace_852187 : CollatzResearch.WordTrace tailWord_852187 prefixEnd_852187 145860512837720849381123 := by
  unfold tailWord_852187
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081813363679515797522815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20721208909119677198348543 31081813363679515797522815)
  ·
    refine ⟨46622720045519273696284223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31081813363679515797522815 46622720045519273696284223)
    ·
      refine ⟨69934080068278910544426335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46622720045519273696284223 69934080068278910544426335)
      ·
        refine ⟨104901120102418365816639503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69934080068278910544426335 104901120102418365816639503)
        ·
          refine ⟨157351680153627548724959255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104901120102418365816639503 157351680153627548724959255)
          ·
            refine ⟨236027520230441323087438883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157351680153627548724959255 236027520230441323087438883)
            ·
              refine ⟨354041280345661984631158325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236027520230441323087438883 354041280345661984631158325)
              ·
                refine ⟨33191370032405811059171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354041280345661984631158325 33191370032405811059171093)
                ·
                  refine ⟨1555845470269022393398645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33191370032405811059171093 1555845470269022393398645)
                  ·
                    refine ⟨145860512837720849381123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1555845470269022393398645 145860512837720849381123)
                    ·
                      rfl

theorem cell23_852187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].length) (baseStart_852187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852187 prefixEnd_852187 := by exact prefixLift 852187
  have htrace : WordTrace (prefixWord ++ tailWord_852187) baseStart_852187 baseEnd_852187 := by
    simpa [prefixWord, tailWord_852187, baseEnd_852187] using wordTrace_append hprefix tailTrace_852187
  have hstable : (prefixWord ++ tailWord_852187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852187).length < 2 ^ (prefixWord ++ tailWord_852187).sum := by decide
  have hdescent : baseEnd_852187 < baseStart_852187 := by decide
  rcases family_descends (prefixWord ++ tailWord_852187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852214 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_852214 : Nat := 118140960795 + 852214 * 2 ^ 59
def prefixEnd_852214 : Nat := 4983230072969 + 3 ^ 40 * 852214 * 2
def baseEnd_852214 : Nat := 437595402490833942505745

theorem tailTrace_852214 : CollatzResearch.WordTrace tailWord_852214 prefixEnd_852214 437595402490833942505745 := by
  unfold tailWord_852214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942674883411356213047231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20721865423054466272503797 1942674883411356213047231)
  ·
    refine ⟨2914012325117034319570847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1942674883411356213047231 2914012325117034319570847)
    ·
      refine ⟨4371018487675551479356271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914012325117034319570847 4371018487675551479356271)
      ·
        refine ⟨6556527731513327219034407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371018487675551479356271 6556527731513327219034407)
        ·
          refine ⟨9834791597269990828551611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6556527731513327219034407 9834791597269990828551611)
          ·
            refine ⟨14752187395904986242827417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9834791597269990828551611 14752187395904986242827417)
            ·
              refine ⟨11064140546928739682120563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14752187395904986242827417 11064140546928739682120563)
              ·
                refine ⟨16596210820393109523180845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11064140546928739682120563 16596210820393109523180845)
                ·
                  refine ⟨6223579057647416071192817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16596210820393109523180845 6223579057647416071192817)
                  ·
                    refine ⟨4667684293235562053394613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6223579057647416071192817 4667684293235562053394613)
                    ·
                      refine ⟨437595402490833942505745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4667684293235562053394613 437595402490833942505745)
                      ·
                        rfl

theorem cell23_852214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_852214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852214 prefixEnd_852214 := by exact prefixLift 852214
  have htrace : WordTrace (prefixWord ++ tailWord_852214) baseStart_852214 baseEnd_852214 := by
    simpa [prefixWord, tailWord_852214, baseEnd_852214] using wordTrace_append hprefix tailTrace_852214
  have hstable : (prefixWord ++ tailWord_852214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852214).length < 2 ^ (prefixWord ++ tailWord_852214).sum := by decide
  have hdescent : baseEnd_852214 < baseStart_852214 := by decide
  rcases family_descends (prefixWord ++ tailWord_852214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852224 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_852224 : Nat := 118140960795 + 852224 * 2 ^ 59
def prefixEnd_852224 : Nat := 4983230072969 + 3 ^ 40 * 852224 * 2
def baseEnd_852224 : Nat := 437600537297378903380699

theorem tailTrace_852224 : CollatzResearch.WordTrace tailWord_852224 prefixEnd_852224 437600537297378903380699 := by
  unfold tailWord_852224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541581432272735558309863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20722108576363647411079817 15541581432272735558309863)
  ·
    refine ⟨23312372148409103337464795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15541581432272735558309863 23312372148409103337464795)
    ·
      refine ⟨34968558222613655006197193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23312372148409103337464795 34968558222613655006197193)
      ·
        refine ⟨26226418666960241254647895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34968558222613655006197193 26226418666960241254647895)
        ·
          refine ⟨39339628000440361881971843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26226418666960241254647895 39339628000440361881971843)
          ·
            refine ⟨59009442000660542822957765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39339628000440361881971843 59009442000660542822957765)
            ·
              refine ⟨11064270375123851779304581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59009442000660542822957765 11064270375123851779304581)
              ·
                refine ⟨2074550695335722208619609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11064270375123851779304581 2074550695335722208619609)
                ·
                  refine ⟨1555913021501791656464707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074550695335722208619609 1555913021501791656464707)
                  ·
                    refine ⟨2333869532252687484697061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555913021501791656464707 2333869532252687484697061)
                    ·
                      refine ⟨437600537297378903380699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2333869532252687484697061 437600537297378903380699)
                      ·
                        rfl

theorem cell23_852224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_852224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852224 prefixEnd_852224 := by exact prefixLift 852224
  have htrace : WordTrace (prefixWord ++ tailWord_852224) baseStart_852224 baseEnd_852224 := by
    simpa [prefixWord, tailWord_852224, baseEnd_852224] using wordTrace_append hprefix tailTrace_852224
  have hstable : (prefixWord ++ tailWord_852224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852224).length < 2 ^ (prefixWord ++ tailWord_852224).sum := by decide
  have hdescent : baseEnd_852224 < baseStart_852224 := by decide
  rcases family_descends (prefixWord ++ tailWord_852224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852241 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_852241 : Nat := 118140960795 + 852241 * 2 ^ 59
def prefixEnd_852241 : Nat := 4983230072969 + 3 ^ 40 * 852241 * 2
def baseEnd_852241 : Nat := 437609266468505336868121

theorem tailTrace_852241 : CollatzResearch.WordTrace tailWord_852241 prefixEnd_852241 437609266468505336868121 := by
  unfold tailWord_852241
  simp only [CollatzResearch.WordTrace]
  refine ⟨31083782905483883019988577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722521936989255346659051 31083782905483883019988577)
  ·
    refine ⟨23312837179112912264991433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31083782905483883019988577 23312837179112912264991433)
    ·
      refine ⟨17484627884334684198743575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23312837179112912264991433 17484627884334684198743575)
      ·
        refine ⟨26226941826502026298115363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17484627884334684198743575 26226941826502026298115363)
        ·
          refine ⟨39340412739753039447173045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26226941826502026298115363 39340412739753039447173045)
          ·
            refine ⟨3688163694351847448172473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39340412739753039447173045 3688163694351847448172473)
            ·
              refine ⟨2766122770763885586129355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688163694351847448172473 2766122770763885586129355)
              ·
                refine ⟨4149184156145828379194033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766122770763885586129355 4149184156145828379194033)
                ·
                  refine ⟨3111888117109371284395525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149184156145828379194033 3111888117109371284395525)
                  ·
                    refine ⟨583479021958007115824161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3111888117109371284395525 583479021958007115824161)
                    ·
                      refine ⟨437609266468505336868121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583479021958007115824161 437609266468505336868121)
                      ·
                        rfl

theorem cell23_852241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_852241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852241 prefixEnd_852241 := by exact prefixLift 852241
  have htrace : WordTrace (prefixWord ++ tailWord_852241) baseStart_852241 baseEnd_852241 := by
    simpa [prefixWord, tailWord_852241, baseEnd_852241] using wordTrace_append hprefix tailTrace_852241
  have hstable : (prefixWord ++ tailWord_852241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852241).length < 2 ^ (prefixWord ++ tailWord_852241).sum := by decide
  have hdescent : baseEnd_852241 < baseStart_852241 := by decide
  rcases family_descends (prefixWord ++ tailWord_852241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852268 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_852268 : Nat := 118140960795 + 852268 * 2 ^ 59
def prefixEnd_852268 : Nat := 4983230072969 + 3 ^ 40 * 852268 * 2
def baseEnd_852268 : Nat := 145874376815392243743499

theorem tailTrace_852268 : CollatzResearch.WordTrace tailWord_852268 prefixEnd_852268 145874376815392243743499 := by
  unfold tailWord_852268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15542383838193033315610729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20723178450924044420814305 15542383838193033315610729)
  ·
    refine ⟨11656787878644774986708047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15542383838193033315610729 11656787878644774986708047)
    ·
      refine ⟨17485181817967162480062071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656787878644774986708047 17485181817967162480062071)
      ·
        refine ⟨26227772726950743720093107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17485181817967162480062071 26227772726950743720093107)
        ·
          refine ⟨39341659090426115580139661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26227772726950743720093107 39341659090426115580139661)
          ·
            refine ⟨14753122158909793342552373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39341659090426115580139661 14753122158909793342552373)
            ·
              refine ⟨1383105202397793125864285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14753122158909793342552373 1383105202397793125864285)
              ·
                refine ⟨518664450899172422199107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1383105202397793125864285 518664450899172422199107)
                ·
                  refine ⟨777996676348758633298661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518664450899172422199107 777996676348758633298661)
                  ·
                    refine ⟨145874376815392243743499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777996676348758633298661 145874376815392243743499)
                    ·
                      rfl

theorem cell23_852268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_852268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852268 prefixEnd_852268 := by exact prefixLift 852268
  have htrace : WordTrace (prefixWord ++ tailWord_852268) baseStart_852268 baseEnd_852268 := by
    simpa [prefixWord, tailWord_852268, baseEnd_852268] using wordTrace_append hprefix tailTrace_852268
  have hstable : (prefixWord ++ tailWord_852268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852268).length < 2 ^ (prefixWord ++ tailWord_852268).sum := by decide
  have hdescent : baseEnd_852268 < baseStart_852268 := by decide
  rcases family_descends (prefixWord ++ tailWord_852268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852361 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_852361 : Nat := 118140960795 + 852361 * 2 ^ 59
def prefixEnd_852361 : Nat := 4983230072969 + 3 ^ 40 * 852361 * 2
def baseEnd_852361 : Nat := 437670884147044867367569

theorem tailTrace_852361 : CollatzResearch.WordTrace tailWord_852361 prefixEnd_852361 437670884147044867367569 := by
  unfold tailWord_852361
  simp only [CollatzResearch.WordTrace]
  refine ⟨31088159665049143514356937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20725439776699429009571291 31088159665049143514356937)
  ·
    refine ⟨23316119748786857635767703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31088159665049143514356937 23316119748786857635767703)
    ·
      refine ⟨34974179623180286453651555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23316119748786857635767703 34974179623180286453651555)
      ·
        refine ⟨52461269434770429680477333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34974179623180286453651555 52461269434770429680477333)
        ·
          refine ⟨2459122004754863891272375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52461269434770429680477333 2459122004754863891272375)
          ·
            refine ⟨3688683007132295836908563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459122004754863891272375 3688683007132295836908563)
            ·
              refine ⟨5533024510698443755362845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688683007132295836908563 5533024510698443755362845)
              ·
                refine ⟨2074884191511916408261067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5533024510698443755362845 2074884191511916408261067)
                ·
                  refine ⟨3112326287267874612391601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074884191511916408261067 3112326287267874612391601)
                  ·
                    refine ⟨2334244715450905959293701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112326287267874612391601 2334244715450905959293701)
                    ·
                      refine ⟨437670884147044867367569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2334244715450905959293701 437670884147044867367569)
                      ·
                        rfl

theorem cell23_852361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_852361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852361 prefixEnd_852361 := by exact prefixLift 852361
  have htrace : WordTrace (prefixWord ++ tailWord_852361) baseStart_852361 baseEnd_852361 := by
    simpa [prefixWord, tailWord_852361, baseEnd_852361] using wordTrace_append hprefix tailTrace_852361
  have hstable : (prefixWord ++ tailWord_852361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852361).length < 2 ^ (prefixWord ++ tailWord_852361).sum := by decide
  have hdescent : baseEnd_852361 < baseStart_852361 := by decide
  rcases family_descends (prefixWord ++ tailWord_852361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852382 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_852382 : Nat := 118140960795 + 852382 * 2 ^ 59
def prefixEnd_852382 : Nat := 4983230072969 + 3 ^ 40 * 852382 * 2
def baseEnd_852382 : Nat := 437681667240789285204973

theorem tailTrace_852382 : CollatzResearch.WordTrace tailWord_852382 prefixEnd_852382 437681667240789285204973 := by
  unfold tailWord_852382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886115699746633012608925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20725950398648709400580933 3886115699746633012608925)
  ·
    refine ⟨1457293387404987379728347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3886115699746633012608925 1457293387404987379728347)
    ·
      refine ⟨2185940081107481069592521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457293387404987379728347 2185940081107481069592521)
      ·
        refine ⟨1639455060830610802194391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185940081107481069592521 1639455060830610802194391)
        ·
          refine ⟨2459182591245916203291587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639455060830610802194391 2459182591245916203291587)
          ·
            refine ⟨3688773886868874304937381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459182591245916203291587 3688773886868874304937381)
            ·
              refine ⟨691645103787913932175759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3688773886868874304937381 691645103787913932175759)
              ·
                refine ⟨1037467655681870898263639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691645103787913932175759 1037467655681870898263639)
                ·
                  refine ⟨1556201483522806347395459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037467655681870898263639 1556201483522806347395459)
                  ·
                    refine ⟨2334302225284209521093189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556201483522806347395459 2334302225284209521093189)
                    ·
                      refine ⟨437681667240789285204973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2334302225284209521093189 437681667240789285204973)
                      ·
                        rfl

theorem cell23_852382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_852382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852382 prefixEnd_852382 := by exact prefixLift 852382
  have htrace : WordTrace (prefixWord ++ tailWord_852382) baseStart_852382 baseEnd_852382 := by
    simpa [prefixWord, tailWord_852382, baseEnd_852382] using wordTrace_append hprefix tailTrace_852382
  have hstable : (prefixWord ++ tailWord_852382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852382).length < 2 ^ (prefixWord ++ tailWord_852382).sum := by decide
  have hdescent : baseEnd_852382 < baseStart_852382 := by decide
  rcases family_descends (prefixWord ++ tailWord_852382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852392 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_852392 : Nat := 118140960795 + 852392 * 2 ^ 59
def prefixEnd_852392 : Nat := 4983230072969 + 3 ^ 40 * 852392 * 2
def baseEnd_852392 : Nat := 145895600682444748693309

theorem tailTrace_852392 : CollatzResearch.WordTrace tailWord_852392 prefixEnd_852392 145895600682444748693309 := by
  unfold tailWord_852392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544645163968417904367715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20726193551957890539156953 15544645163968417904367715)
  ·
    refine ⟨23316967745952626856551573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544645163968417904367715 23316967745952626856551573)
    ·
      refine ⟨1092982863091529383900855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23316967745952626856551573 1092982863091529383900855)
      ·
        refine ⟨1639474294637294075851283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092982863091529383900855 1639474294637294075851283)
        ·
          refine ⟨2459211441955941113776925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639474294637294075851283 2459211441955941113776925)
          ·
            refine ⟨922204290733477917666347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2459211441955941113776925 922204290733477917666347)
            ·
              refine ⟨1383306436100216876499521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922204290733477917666347 1383306436100216876499521)
              ·
                refine ⟨1037479827075162657374641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383306436100216876499521 1037479827075162657374641)
                ·
                  refine ⟨778109870306371993030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037479827075162657374641 778109870306371993030981)
                  ·
                    refine ⟨145895600682444748693309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778109870306371993030981 145895600682444748693309)
                    ·
                      rfl

theorem cell23_852392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_852392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852392 prefixEnd_852392 := by exact prefixLift 852392
  have htrace : WordTrace (prefixWord ++ tailWord_852392) baseStart_852392 baseEnd_852392 := by
    simpa [prefixWord, tailWord_852392, baseEnd_852392] using wordTrace_append hprefix tailTrace_852392
  have hstable : (prefixWord ++ tailWord_852392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852392).length < 2 ^ (prefixWord ++ tailWord_852392).sum := by decide
  have hdescent : baseEnd_852392 < baseStart_852392 := by decide
  rcases family_descends (prefixWord ++ tailWord_852392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852441 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_852441 : Nat := 118140960795 + 852441 * 2 ^ 59
def prefixEnd_852441 : Nat := 4983230072969 + 3 ^ 40 * 852441 * 2
def baseEnd_852441 : Nat := 437711962599404554367201

theorem tailTrace_852441 : CollatzResearch.WordTrace tailWord_852441 prefixEnd_852441 437711962599404554367201 := by
  unfold tailWord_852441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31091077504759317177269177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20727385003172878118179451 31091077504759317177269177)
  ·
    refine ⟨23318308128569487882951883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31091077504759317177269177 23318308128569487882951883)
    ·
      refine ⟨34977462192854231824427825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23318308128569487882951883 34977462192854231824427825)
      ·
        refine ⟨26233096644640673868320869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34977462192854231824427825 26233096644640673868320869)
        ·
          refine ⟨4918705620870126350310163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26233096644640673868320869 4918705620870126350310163)
          ·
            refine ⟨7378058431305189525465245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918705620870126350310163 7378058431305189525465245)
            ·
              refine ⟨2766771911739446072049467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7378058431305189525465245 2766771911739446072049467)
              ·
                refine ⟨4150157867609169108074201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766771911739446072049467 4150157867609169108074201)
                ·
                  refine ⟨3112618400706876831055651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150157867609169108074201 3112618400706876831055651)
                  ·
                    refine ⟨4668927601060315246583477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3112618400706876831055651 4668927601060315246583477)
                    ·
                      refine ⟨437711962599404554367201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4668927601060315246583477 437711962599404554367201)
                      ·
                        rfl

theorem cell23_852441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_852441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852441 prefixEnd_852441 := by exact prefixLift 852441
  have htrace : WordTrace (prefixWord ++ tailWord_852441) baseStart_852441 baseEnd_852441 := by
    simpa [prefixWord, tailWord_852441, baseEnd_852441] using wordTrace_append hprefix tailTrace_852441
  have hstable : (prefixWord ++ tailWord_852441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852441).length < 2 ^ (prefixWord ++ tailWord_852441).sum := by decide
  have hdescent : baseEnd_852441 < baseStart_852441 := by decide
  rcases family_descends (prefixWord ++ tailWord_852441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852455 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_852455 : Nat := 118140960795 + 852455 * 2 ^ 59
def prefixEnd_852455 : Nat := 4983230072969 + 3 ^ 40 * 852455 * 2
def baseEnd_852455 : Nat := 437719151328567499592137

theorem tailTrace_852455 : CollatzResearch.WordTrace tailWord_852455 prefixEnd_852455 437719151328567499592137 := by
  unfold tailWord_852455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31091588126708597568278819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20727725417805731712185879 31091588126708597568278819)
  ·
    refine ⟨46637382190062896352418229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31091588126708597568278819 46637382190062896352418229)
    ·
      refine ⟨4372254580318396533039209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46637382190062896352418229 4372254580318396533039209)
      ·
        refine ⟨3279190935238797399779407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372254580318396533039209 3279190935238797399779407)
        ·
          refine ⟨4918786402858196099669111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279190935238797399779407 4918786402858196099669111)
          ·
            refine ⟨7378179604287294149503667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918786402858196099669111 7378179604287294149503667)
            ·
              refine ⟨11067269406430941224255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378179604287294149503667 11067269406430941224255501)
              ·
                refine ⟨4150226027411602959095813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11067269406430941224255501 4150226027411602959095813)
                ·
                  refine ⟨778167380139675554830465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4150226027411602959095813 778167380139675554830465)
                  ·
                    refine ⟨583625535104756666122849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778167380139675554830465 583625535104756666122849)
                    ·
                      refine ⟨437719151328567499592137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583625535104756666122849 437719151328567499592137)
                      ·
                        rfl

theorem cell23_852455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_852455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852455 prefixEnd_852455 := by exact prefixLift 852455
  have htrace : WordTrace (prefixWord ++ tailWord_852455) baseStart_852455 baseEnd_852455 := by
    simpa [prefixWord, tailWord_852455, baseEnd_852455] using wordTrace_append hprefix tailTrace_852455
  have hstable : (prefixWord ++ tailWord_852455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852455).length < 2 ^ (prefixWord ++ tailWord_852455).sum := by decide
  have hdescent : baseEnd_852455 < baseStart_852455 := by decide
  rcases family_descends (prefixWord ++ tailWord_852455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852466 : List Nat := [3, 2, 1, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_852466 : Nat := 118140960795 + 852466 * 2 ^ 59
def prefixEnd_852466 : Nat := 4983230072969 + 3 ^ 40 * 852466 * 2
def baseEnd_852466 : Nat := 437724799615766956554587

theorem tailTrace_852466 : CollatzResearch.WordTrace tailWord_852466 prefixEnd_852466 437724799615766956554587 := by
  unfold tailWord_852466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772997332417186611732313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20727992886445830964619501 7772997332417186611732313)
  ·
    refine ⟨5829747999312889958799235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7772997332417186611732313 5829747999312889958799235)
    ·
      refine ⟨8744621998969334938198853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829747999312889958799235 8744621998969334938198853)
      ·
        refine ⟨1639616624806750300912285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8744621998969334938198853 1639616624806750300912285)
        ·
          refine ⟨614856234302531362842107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1639616624806750300912285 614856234302531362842107)
          ·
            refine ⟨922284351453797044263161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614856234302531362842107 922284351453797044263161)
            ·
              refine ⟨691713263590347783197371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922284351453797044263161 691713263590347783197371)
              ·
                refine ⟨1037569895385521674796057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691713263590347783197371 1037569895385521674796057)
                ·
                  refine ⟨778177421539141256097043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037569895385521674796057 778177421539141256097043)
                  ·
                    refine ⟨1167266132308711884145565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 778177421539141256097043 1167266132308711884145565)
                    ·
                      refine ⟨437724799615766956554587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1167266132308711884145565 437724799615766956554587)
                      ·
                        rfl

theorem cell23_852466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_852466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852466 prefixEnd_852466 := by exact prefixLift 852466
  have htrace : WordTrace (prefixWord ++ tailWord_852466) baseStart_852466 baseEnd_852466 := by
    simpa [prefixWord, tailWord_852466, baseEnd_852466] using wordTrace_append hprefix tailTrace_852466
  have hstable : (prefixWord ++ tailWord_852466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852466).length < 2 ^ (prefixWord ++ tailWord_852466).sum := by decide
  have hdescent : baseEnd_852466 < baseStart_852466 := by decide
  rcases family_descends (prefixWord ++ tailWord_852466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852471 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_852471 : Nat := 118140960795 + 852471 * 2 ^ 59
def prefixEnd_852471 : Nat := 4983230072969 + 3 ^ 40 * 852471 * 2
def baseEnd_852471 : Nat := 437727367019039436992063

theorem tailTrace_852471 : CollatzResearch.WordTrace tailWord_852471 prefixEnd_852471 437727367019039436992063 := by
  unfold tailWord_852471
  simp only [CollatzResearch.WordTrace]
  refine ⟨31092171694650632300861267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20728114463100421533907511 31092171694650632300861267)
  ·
    refine ⟨46638257541975948451291901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31092171694650632300861267 46638257541975948451291901)
    ·
      refine ⟨17489346578240980669234463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46638257541975948451291901 17489346578240980669234463)
      ·
        refine ⟨26234019867361471003851695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489346578240980669234463 26234019867361471003851695)
        ·
          refine ⟨39351029801042206505777543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234019867361471003851695 39351029801042206505777543)
          ·
            refine ⟨59026544701563309758666315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39351029801042206505777543 59026544701563309758666315)
            ·
              refine ⟨88539817052344964637999473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59026544701563309758666315 88539817052344964637999473)
              ·
                refine ⟨66404862789258723478499605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88539817052344964637999473 66404862789258723478499605)
                ·
                  refine ⟨3112727943246502663054669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66404862789258723478499605 3112727943246502663054669)
                  ·
                    refine ⟨1167272978717438498645501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112727943246502663054669 1167272978717438498645501)
                    ·
                      refine ⟨437727367019039436992063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1167272978717438498645501 437727367019039436992063)
                      ·
                        rfl

theorem cell23_852471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_852471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852471 prefixEnd_852471 := by exact prefixLift 852471
  have htrace : WordTrace (prefixWord ++ tailWord_852471) baseStart_852471 baseEnd_852471 := by
    simpa [prefixWord, tailWord_852471, baseEnd_852471] using wordTrace_append hprefix tailTrace_852471
  have hstable : (prefixWord ++ tailWord_852471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852471).length < 2 ^ (prefixWord ++ tailWord_852471).sum := by decide
  have hdescent : baseEnd_852471 < baseStart_852471 := by decide
  rcases family_descends (prefixWord ++ tailWord_852471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852501 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_852501 : Nat := 118140960795 + 852501 * 2 ^ 59
def prefixEnd_852501 : Nat := 4983230072969 + 3 ^ 40 * 852501 * 2
def baseEnd_852501 : Nat := 437742771438674319616925

theorem tailTrace_852501 : CollatzResearch.WordTrace tailWord_852501 prefixEnd_852501 437742771438674319616925 := by
  unfold tailWord_852501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093265884541947424453357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20728843923027964949635571 31093265884541947424453357)
  ·
    refine ⟨11659974706703230284170009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31093265884541947424453357 11659974706703230284170009)
    ·
      refine ⟨8744981030027422713127507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11659974706703230284170009 8744981030027422713127507)
      ·
        refine ⟨13117471545041134069691261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744981030027422713127507 13117471545041134069691261)
        ·
          refine ⟨4919051829390425276134223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13117471545041134069691261 4919051829390425276134223)
          ·
            refine ⟨7378577744085637914201335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919051829390425276134223 7378577744085637914201335)
            ·
              refine ⟨11067866616128456871302003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378577744085637914201335 11067866616128456871302003)
              ·
                refine ⟨16601799924192685306953005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067866616128456871302003 16601799924192685306953005)
                ·
                  refine ⟨6225674971572256990107377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16601799924192685306953005 6225674971572256990107377)
                  ·
                    refine ⟨4669256228679192742580533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225674971572256990107377 4669256228679192742580533)
                    ·
                      refine ⟨437742771438674319616925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4669256228679192742580533 437742771438674319616925)
                      ·
                        rfl

theorem cell23_852501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_852501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852501 prefixEnd_852501 := by exact prefixLift 852501
  have htrace : WordTrace (prefixWord ++ tailWord_852501) baseStart_852501 baseEnd_852501 := by
    simpa [prefixWord, tailWord_852501, baseEnd_852501] using wordTrace_append hprefix tailTrace_852501
  have hstable : (prefixWord ++ tailWord_852501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852501).length < 2 ^ (prefixWord ++ tailWord_852501).sum := by decide
  have hdescent : baseEnd_852501 < baseStart_852501 := by decide
  rcases family_descends (prefixWord ++ tailWord_852501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852508 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_852508 : Nat := 118140960795 + 852508 * 2 ^ 59
def prefixEnd_852508 : Nat := 4983230072969 + 3 ^ 40 * 852508 * 2
def baseEnd_852508 : Nat := 145915455267751930743131

theorem tailTrace_852508 : CollatzResearch.WordTrace tailWord_852508 prefixEnd_852508 145915455267751930743131 := by
  unfold tailWord_852508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546760597758293809979089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20729014130344391746638785 15546760597758293809979089)
  ·
    refine ⟨11660070448318720357484317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15546760597758293809979089 11660070448318720357484317)
    ·
      refine ⟨4372526418119520134056619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11660070448318720357484317 4372526418119520134056619)
      ·
        refine ⟨6558789627179280201084929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372526418119520134056619 6558789627179280201084929)
        ·
          refine ⟨4919092220384460150813697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558789627179280201084929 4919092220384460150813697)
          ·
            refine ⟨3689319165288345113110273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919092220384460150813697 3689319165288345113110273)
            ·
              refine ⟨2766989373966258834832705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689319165288345113110273 2766989373966258834832705)
              ·
                refine ⟨2075242030474694126124529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766989373966258834832705 2075242030474694126124529)
                ·
                  refine ⟨1556431522856020594593397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075242030474694126124529 1556431522856020594593397)
                  ·
                    refine ⟨145915455267751930743131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1556431522856020594593397 145915455267751930743131)
                    ·
                      rfl

theorem cell23_852508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_852508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852508 prefixEnd_852508 := by exact prefixLift 852508
  have htrace : WordTrace (prefixWord ++ tailWord_852508) baseStart_852508 baseEnd_852508 := by
    simpa [prefixWord, tailWord_852508, baseEnd_852508] using wordTrace_append hprefix tailTrace_852508
  have hstable : (prefixWord ++ tailWord_852508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852508).length < 2 ^ (prefixWord ++ tailWord_852508).sum := by decide
  have hdescent : baseEnd_852508 < baseStart_852508 := by decide
  rcases family_descends (prefixWord ++ tailWord_852508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852511 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_852511 : Nat := 118140960795 + 852511 * 2 ^ 59
def prefixEnd_852511 : Nat := 4983230072969 + 3 ^ 40 * 852511 * 2
def baseEnd_852511 : Nat := 437747906245219280491879

theorem tailTrace_852511 : CollatzResearch.WordTrace tailWord_852511 prefixEnd_852511 437747906245219280491879 := by
  unfold tailWord_852511
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093630614505719132317387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20729087076337146088211591 31093630614505719132317387)
  ·
    refine ⟨46640445921758578698476081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31093630614505719132317387 46640445921758578698476081)
    ·
      refine ⟨34980334441318934023857061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46640445921758578698476081 34980334441318934023857061)
      ·
        refine ⟨6558812707747300129473199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34980334441318934023857061 6558812707747300129473199)
        ·
          refine ⟨9838219061620950194209799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558812707747300129473199 9838219061620950194209799)
          ·
            refine ⟨14757328592431425291314699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838219061620950194209799 14757328592431425291314699)
            ·
              refine ⟨22135992888647137936972049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757328592431425291314699 22135992888647137936972049)
              ·
                refine ⟨16601994666485353452729037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22135992888647137936972049 16601994666485353452729037)
                ·
                  refine ⟨6225747999932007544773389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16601994666485353452729037 6225747999932007544773389)
                  ·
                    refine ⟨2334655499974502829290021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6225747999932007544773389 2334655499974502829290021)
                    ·
                      refine ⟨437747906245219280491879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2334655499974502829290021 437747906245219280491879)
                      ·
                        rfl

theorem cell23_852511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_852511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852511 prefixEnd_852511 := by exact prefixLift 852511
  have htrace : WordTrace (prefixWord ++ tailWord_852511) baseStart_852511 baseEnd_852511 := by
    simpa [prefixWord, tailWord_852511, baseEnd_852511] using wordTrace_append hprefix tailTrace_852511
  have hstable : (prefixWord ++ tailWord_852511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852511).length < 2 ^ (prefixWord ++ tailWord_852511).sum := by decide
  have hdescent : baseEnd_852511 < baseStart_852511 := by decide
  rcases family_descends (prefixWord ++ tailWord_852511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852528 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2]
def baseStart_852528 : Nat := 118140960795 + 852528 * 2 ^ 59
def prefixEnd_852528 : Nat := 4983230072969 + 3 ^ 40 * 852528 * 2
def baseEnd_852528 : Nat := 437756635416345713979301

theorem tailTrace_852528 : CollatzResearch.WordTrace tailWord_852528 prefixEnd_852528 437756635416345713979301 := by
  unfold tailWord_852528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547125327722065517843119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20729500436962754023790825 15547125327722065517843119)
  ·
    refine ⟨23320687991583098276764679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547125327722065517843119 23320687991583098276764679)
    ·
      refine ⟨34981031987374647415147019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320687991583098276764679 34981031987374647415147019)
      ·
        refine ⟨52471547981061971122720529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34981031987374647415147019 52471547981061971122720529)
        ·
          refine ⟨39353660985796478342040397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52471547981061971122720529 39353660985796478342040397)
          ·
            refine ⟨14757622869673679378265149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39353660985796478342040397 14757622869673679378265149)
            ·
              refine ⟨5534108576127629766849431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14757622869673679378265149 5534108576127629766849431)
              ·
                refine ⟨8301162864191444650274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534108576127629766849431 8301162864191444650274147)
                ·
                  refine ⟨12451744296287166975411221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301162864191444650274147 12451744296287166975411221)
                  ·
                    refine ⟨583675513888460951972401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12451744296287166975411221 583675513888460951972401)
                    ·
                      refine ⟨437756635416345713979301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583675513888460951972401 437756635416345713979301)
                      ·
                        rfl

theorem cell23_852528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2].length) (baseStart_852528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852528 prefixEnd_852528 := by exact prefixLift 852528
  have htrace : WordTrace (prefixWord ++ tailWord_852528) baseStart_852528 baseEnd_852528 := by
    simpa [prefixWord, tailWord_852528, baseEnd_852528] using wordTrace_append hprefix tailTrace_852528
  have hstable : (prefixWord ++ tailWord_852528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852528).length < 2 ^ (prefixWord ++ tailWord_852528).sum := by decide
  have hdescent : baseEnd_852528 < baseStart_852528 := by decide
  rcases family_descends (prefixWord ++ tailWord_852528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852538 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_852538 : Nat := 118140960795 + 852538 * 2 ^ 59
def prefixEnd_852538 : Nat := 4983230072969 + 3 ^ 40 * 852538 * 2
def baseEnd_852538 : Nat := 145920590074296891618085

theorem tailTrace_852538 : CollatzResearch.WordTrace tailWord_852538 prefixEnd_852538 145920590074296891618085 := by
  unfold tailWord_852538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773653846351975685887567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20729743590271935162366845 7773653846351975685887567)
  ·
    refine ⟨11660480769527963528831351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773653846351975685887567 11660480769527963528831351)
    ·
      refine ⟨17490721154291945293247027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11660480769527963528831351 17490721154291945293247027)
      ·
        refine ⟨26236081731437917939870541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17490721154291945293247027 26236081731437917939870541)
        ·
          refine ⟨9838530649289219227451453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26236081731437917939870541 9838530649289219227451453)
          ·
            refine ⟨3689448993483457210294295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9838530649289219227451453 3689448993483457210294295)
            ·
              refine ⟨5534173490225185815441443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689448993483457210294295 5534173490225185815441443)
              ·
                refine ⟨8301260235337778723162165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534173490225185815441443 8301260235337778723162165)
                ·
                  refine ⟨778243147062916755296453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8301260235337778723162165 778243147062916755296453)
                  ·
                    refine ⟨145920590074296891618085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778243147062916755296453 145920590074296891618085)
                    ·
                      rfl

theorem cell23_852538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_852538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852538 prefixEnd_852538 := by exact prefixLift 852538
  have htrace : WordTrace (prefixWord ++ tailWord_852538) baseStart_852538 baseEnd_852538 := by
    simpa [prefixWord, tailWord_852538, baseEnd_852538] using wordTrace_append hprefix tailTrace_852538
  have hstable : (prefixWord ++ tailWord_852538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852538).length < 2 ^ (prefixWord ++ tailWord_852538).sum := by decide
  have hdescent : baseEnd_852538 < baseStart_852538 := by decide
  rcases family_descends (prefixWord ++ tailWord_852538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852545 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_852545 : Nat := 118140960795 + 852545 * 2 ^ 59
def prefixEnd_852545 : Nat := 4983230072969 + 3 ^ 40 * 852545 * 2
def baseEnd_852545 : Nat := 437765364587472147466723

theorem tailTrace_852545 : CollatzResearch.WordTrace tailWord_852545 prefixEnd_852545 437765364587472147466723 := by
  unfold tailWord_852545
  simp only [CollatzResearch.WordTrace]
  refine ⟨31094870696382542939055089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20729913797588361959370059 31094870696382542939055089)
  ·
    refine ⟨23321153022286907204291317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31094870696382542939055089 23321153022286907204291317)
    ·
      refine ⟨2186358095839397550402311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23321153022286907204291317 2186358095839397550402311)
      ·
        refine ⟨3279537143759096325603467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186358095839397550402311 3279537143759096325603467)
        ·
          refine ⟨4919305715638644488405201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279537143759096325603467 4919305715638644488405201)
          ·
            refine ⟨3689479286728983366303901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919305715638644488405201 3689479286728983366303901)
            ·
              refine ⟨1383554732523368762363963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3689479286728983366303901 1383554732523368762363963)
              ·
                refine ⟨2075332098785053143545945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383554732523368762363963 2075332098785053143545945)
                ·
                  refine ⟨1556499074088789857659459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075332098785053143545945 1556499074088789857659459)
                  ·
                    refine ⟨2334748611133184786489189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556499074088789857659459 2334748611133184786489189)
                    ·
                      refine ⟨437765364587472147466723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2334748611133184786489189 437765364587472147466723)
                      ·
                        rfl

theorem cell23_852545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_852545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852545 prefixEnd_852545 := by exact prefixLift 852545
  have htrace : WordTrace (prefixWord ++ tailWord_852545) baseStart_852545 baseEnd_852545 := by
    simpa [prefixWord, tailWord_852545, baseEnd_852545] using wordTrace_append hprefix tailTrace_852545
  have hstable : (prefixWord ++ tailWord_852545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852545).length < 2 ^ (prefixWord ++ tailWord_852545).sum := by decide
  have hdescent : baseEnd_852545 < baseStart_852545 := by decide
  rcases family_descends (prefixWord ++ tailWord_852545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852555 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 1, 4]
def baseStart_852555 : Nat := 118140960795 + 852555 * 2 ^ 59
def prefixEnd_852555 : Nat := 4983230072969 + 3 ^ 40 * 852555 * 2
def baseEnd_852555 : Nat := 145923499798005702780559

theorem tailTrace_852555 : CollatzResearch.WordTrace tailWord_852555 prefixEnd_852555 145923499798005702780559 := by
  unfold tailWord_852555
  simp only [CollatzResearch.WordTrace]
  refine ⟨31095235426346314646919119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20730156950897543097946079 31095235426346314646919119)
  ·
    refine ⟨46642853139519471970378679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31095235426346314646919119 46642853139519471970378679)
    ·
      refine ⟨69964279709279207955568019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46642853139519471970378679 69964279709279207955568019)
      ·
        refine ⟨104946419563918811933352029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69964279709279207955568019 104946419563918811933352029)
        ·
          refine ⟨39354907336469554475007011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104946419563918811933352029 39354907336469554475007011)
          ·
            refine ⟨59032361004704331712510517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39354907336469554475007011 59032361004704331712510517)
            ·
              refine ⟨5534283844191031098047861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59032361004704331712510517 5534283844191031098047861)
              ·
                refine ⟨518839110392909165441987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5534283844191031098047861 518839110392909165441987)
                ·
                  refine ⟨778258665589363748162981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518839110392909165441987 778258665589363748162981)
                  ·
                    refine ⟨145923499798005702780559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778258665589363748162981 145923499798005702780559)
                    ·
                      rfl

theorem cell23_852555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 1, 4].length) (baseStart_852555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852555 prefixEnd_852555 := by exact prefixLift 852555
  have htrace : WordTrace (prefixWord ++ tailWord_852555) baseStart_852555 baseEnd_852555 := by
    simpa [prefixWord, tailWord_852555, baseEnd_852555] using wordTrace_append hprefix tailTrace_852555
  have hstable : (prefixWord ++ tailWord_852555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852555).length < 2 ^ (prefixWord ++ tailWord_852555).sum := by decide
  have hdescent : baseEnd_852555 < baseStart_852555 := by decide
  rcases family_descends (prefixWord ++ tailWord_852555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852568 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 6]
def baseStart_852568 : Nat := 118140960795 + 852568 * 2 ^ 59
def prefixEnd_852568 : Nat := 4983230072969 + 3 ^ 40 * 852568 * 2
def baseEnd_852568 : Nat := 48641908293613950831013

theorem tailTrace_852568 : CollatzResearch.WordTrace tailWord_852568 prefixEnd_852568 48641908293613950831013 := by
  unfold tailWord_852568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547854787649608933571179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20730473050199478578094905 15547854787649608933571179)
  ·
    refine ⟨23321782181474413400356769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547854787649608933571179 23321782181474413400356769)
    ·
      refine ⟨17491336636105810050267577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23321782181474413400356769 17491336636105810050267577)
      ·
        refine ⟨13118502477079357537700683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17491336636105810050267577 13118502477079357537700683)
        ·
          refine ⟨19677753715619036306551025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13118502477079357537700683 19677753715619036306551025)
          ·
            refine ⟨14758315286714277229913269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19677753715619036306551025 14758315286714277229913269)
            ·
              refine ⟨1383592058129463490304369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14758315286714277229913269 1383592058129463490304369)
              ·
                refine ⟨1037694043597097617728277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383592058129463490304369 1037694043597097617728277)
                ·
                  refine ⟨48641908293613950831013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1037694043597097617728277 48641908293613950831013)
                  ·
                    rfl

theorem cell23_852568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_852568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852568 prefixEnd_852568 := by exact prefixLift 852568
  have htrace : WordTrace (prefixWord ++ tailWord_852568) baseStart_852568 baseEnd_852568 := by
    simpa [prefixWord, tailWord_852568, baseEnd_852568] using wordTrace_append hprefix tailTrace_852568
  have hstable : (prefixWord ++ tailWord_852568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852568).length < 2 ^ (prefixWord ++ tailWord_852568).sum := by decide
  have hdescent : baseEnd_852568 < baseStart_852568 := by decide
  rcases family_descends (prefixWord ++ tailWord_852568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852572 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_852572 : Nat := 118140960795 + 852572 * 2 ^ 59
def prefixEnd_852572 : Nat := 4983230072969 + 3 ^ 40 * 852572 * 2
def baseEnd_852572 : Nat := 145926409521714513943033

theorem tailTrace_852572 : CollatzResearch.WordTrace tailWord_852572 prefixEnd_852572 145926409521714513943033 := by
  unfold tailWord_852572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547927733642363275143985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20730570311523151033525313 15547927733642363275143985)
  ·
    refine ⟨11660945800231772456357989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15547927733642363275143985 11660945800231772456357989)
    ·
      refine ⟨2186427337543457335567123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11660945800231772456357989 2186427337543457335567123)
      ·
        refine ⟨3279641006315186003350685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186427337543457335567123 3279641006315186003350685)
        ·
          refine ⟨1229865377368194751256507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3279641006315186003350685 1229865377368194751256507)
          ·
            refine ⟨1844798066052292126884761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229865377368194751256507 1844798066052292126884761)
            ·
              refine ⟨1383598549539219095163571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844798066052292126884761 1383598549539219095163571)
              ·
                refine ⟨2075397824308828642745357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383598549539219095163571 2075397824308828642745357)
                ·
                  refine ⟨778274184115810741029509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2075397824308828642745357 778274184115810741029509)
                  ·
                    refine ⟨145926409521714513943033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778274184115810741029509 145926409521714513943033)
                    ·
                      rfl

theorem cell23_852572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_852572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852572 prefixEnd_852572 := by exact prefixLift 852572
  have htrace : WordTrace (prefixWord ++ tailWord_852572) baseStart_852572 baseEnd_852572 := by
    simpa [prefixWord, tailWord_852572, baseEnd_852572] using wordTrace_append hprefix tailTrace_852572
  have hstable : (prefixWord ++ tailWord_852572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852572).length < 2 ^ (prefixWord ++ tailWord_852572).sum := by decide
  have hdescent : baseEnd_852572 < baseStart_852572 := by decide
  rcases family_descends (prefixWord ++ tailWord_852572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852591 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_852591 : Nat := 118140960795 + 852591 * 2 ^ 59
def prefixEnd_852591 : Nat := 4983230072969 + 3 ^ 40 * 852591 * 2
def baseEnd_852591 : Nat := 437788984697578967491511

theorem tailTrace_852591 : CollatzResearch.WordTrace tailWord_852591 prefixEnd_852591 437788984697578967491511 := by
  unfold tailWord_852591
  simp only [CollatzResearch.WordTrace]
  refine ⟨31096548454215892795229627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20731032302810595196819751 31096548454215892795229627)
  ·
    refine ⟨46644822681323839192844441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31096548454215892795229627 46644822681323839192844441)
    ·
      refine ⟨34983617010992879394633331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46644822681323839192844441 34983617010992879394633331)
      ·
        refine ⟨52475425516489319091949997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34983617010992879394633331 52475425516489319091949997)
        ·
          refine ⟨19678284568683494659481249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52475425516489319091949997 19678284568683494659481249)
          ·
            refine ⟨14758713426512620994610937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19678284568683494659481249 14758713426512620994610937)
            ·
              refine ⟨11069035069884465745958203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758713426512620994610937 11069035069884465745958203)
              ·
                refine ⟨16603552604826698618937305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069035069884465745958203 16603552604826698618937305)
                ·
                  refine ⟨12452664453620023964202979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16603552604826698618937305 12452664453620023964202979)
                  ·
                    refine ⟨18678996680430035946304469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12452664453620023964202979 18678996680430035946304469)
                    ·
                      refine ⟨437788984697578967491511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18678996680430035946304469 437788984697578967491511)
                      ·
                        rfl

theorem cell23_852591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_852591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852591 prefixEnd_852591 := by exact prefixLift 852591
  have htrace : WordTrace (prefixWord ++ tailWord_852591) baseStart_852591 baseEnd_852591 := by
    simpa [prefixWord, tailWord_852591, baseEnd_852591] using wordTrace_append hprefix tailTrace_852591
  have hstable : (prefixWord ++ tailWord_852591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852591).length < 2 ^ (prefixWord ++ tailWord_852591).sum := by decide
  have hdescent : baseEnd_852591 < baseStart_852591 := by decide
  rcases family_descends (prefixWord ++ tailWord_852591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852622 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_852622 : Nat := 118140960795 + 852622 * 2 ^ 59
def prefixEnd_852622 : Nat := 4983230072969 + 3 ^ 40 * 852622 * 2
def baseEnd_852622 : Nat := 437804902597868346203869

theorem tailTrace_852622 : CollatzResearch.WordTrace tailWord_852622 prefixEnd_852622 437804902597868346203869 := by
  unfold tailWord_852622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887209889637948136201015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20731786078069056726405413 3887209889637948136201015)
  ·
    refine ⟨5830814834456922204301523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887209889637948136201015 5830814834456922204301523)
    ·
      refine ⟨8746222251685383306452285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830814834456922204301523 8746222251685383306452285)
      ·
        refine ⟨3279833344382018739919607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8746222251685383306452285 3279833344382018739919607)
        ·
          refine ⟨4919750016573028109879411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279833344382018739919607 4919750016573028109879411)
          ·
            refine ⟨7379625024859542164819117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919750016573028109879411 7379625024859542164819117)
            ·
              refine ⟨2767359384322328311807169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7379625024859542164819117 2767359384322328311807169)
              ·
                refine ⟨2075519538241746233855377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767359384322328311807169 2075519538241746233855377)
                ·
                  refine ⟨1556639653681309675391533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075519538241746233855377 1556639653681309675391533)
                  ·
                    refine ⟨583739870130491128271825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1556639653681309675391533 583739870130491128271825)
                    ·
                      refine ⟨437804902597868346203869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583739870130491128271825 437804902597868346203869)
                      ·
                        rfl

theorem cell23_852622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_852622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852622 prefixEnd_852622 := by exact prefixLift 852622
  have htrace : WordTrace (prefixWord ++ tailWord_852622) baseStart_852622 baseEnd_852622 := by
    simpa [prefixWord, tailWord_852622, baseEnd_852622] using wordTrace_append hprefix tailTrace_852622
  have hstable : (prefixWord ++ tailWord_852622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852622).length < 2 ^ (prefixWord ++ tailWord_852622).sum := by decide
  have hdescent : baseEnd_852622 < baseStart_852622 := by decide
  rcases family_descends (prefixWord ++ tailWord_852622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852655 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_852655 : Nat := 118140960795 + 852655 * 2 ^ 59
def prefixEnd_852655 : Nat := 4983230072969 + 3 ^ 40 * 852655 * 2
def baseEnd_852655 : Nat := 437821847459466717091217

theorem tailTrace_852655 : CollatzResearch.WordTrace tailWord_852655 prefixEnd_852655 437821847459466717091217 := by
  unfold tailWord_852655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098882725984031725559419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20732588483989354483706279 31098882725984031725559419)
  ·
    refine ⟨46648324088976047588339129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31098882725984031725559419 46648324088976047588339129)
    ·
      refine ⟨34986243066732035691254347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46648324088976047588339129 34986243066732035691254347)
      ·
        refine ⟨52479364600098053536881521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34986243066732035691254347 52479364600098053536881521)
        ·
          refine ⟨39359523450073540152661141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52479364600098053536881521 39359523450073540152661141)
          ·
            refine ⟨1844977661722197194655991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39359523450073540152661141 1844977661722197194655991)
            ·
              refine ⟨2767466492583295791983987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844977661722197194655991 2767466492583295791983987)
              ·
                refine ⟨4151199738874943687975981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767466492583295791983987 4151199738874943687975981)
                ·
                  refine ⟨1556699902078103882990993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151199738874943687975981 1556699902078103882990993)
                  ·
                    refine ⟨1167524926558577912243245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556699902078103882990993 1167524926558577912243245)
                    ·
                      refine ⟨437821847459466717091217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1167524926558577912243245 437821847459466717091217)
                      ·
                        rfl

theorem cell23_852655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_852655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852655 prefixEnd_852655 := by exact prefixLift 852655
  have htrace : WordTrace (prefixWord ++ tailWord_852655) baseStart_852655 baseEnd_852655 := by
    simpa [prefixWord, tailWord_852655, baseEnd_852655] using wordTrace_append hprefix tailTrace_852655
  have hstable : (prefixWord ++ tailWord_852655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852655).length < 2 ^ (prefixWord ++ tailWord_852655).sum := by decide
  have hdescent : baseEnd_852655 < baseStart_852655 := by decide
  rcases family_descends (prefixWord ++ tailWord_852655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852686 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_852686 : Nat := 118140960795 + 852686 * 2 ^ 59
def prefixEnd_852686 : Nat := 4983230072969 + 3 ^ 40 * 852686 * 2
def baseEnd_852686 : Nat := 437837765359756095803575

theorem tailTrace_852686 : CollatzResearch.WordTrace tailWord_852686 prefixEnd_852686 437837765359756095803575 := by
  unfold tailWord_852686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887501673608965502492239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20733342259247816013291941 3887501673608965502492239)
  ·
    refine ⟨5831252510413448253738359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887501673608965502492239 5831252510413448253738359)
    ·
      refine ⟨8746878765620172380607539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831252510413448253738359 8746878765620172380607539)
      ·
        refine ⟨13120318148430258570911309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8746878765620172380607539 13120318148430258570911309)
        ·
          refine ⟨4920119305661346964091741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13120318148430258570911309 4920119305661346964091741)
          ·
            refine ⟨1845044739623005111534403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4920119305661346964091741 1845044739623005111534403)
            ·
              refine ⟨2767567109434507667301605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845044739623005111534403 2767567109434507667301605)
              ·
                refine ⟨518918833018970187619051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2767567109434507667301605 518918833018970187619051)
                ·
                  refine ⟨778378249528455281428577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518918833018970187619051 778378249528455281428577)
                  ·
                    refine ⟨583783687146341461071433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778378249528455281428577 583783687146341461071433)
                    ·
                      refine ⟨437837765359756095803575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 583783687146341461071433 437837765359756095803575)
                      ·
                        rfl

theorem cell23_852686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_852686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852686 prefixEnd_852686 := by exact prefixLift 852686
  have htrace : WordTrace (prefixWord ++ tailWord_852686) baseStart_852686 baseEnd_852686 := by
    simpa [prefixWord, tailWord_852686, baseEnd_852686] using wordTrace_append hprefix tailTrace_852686
  have hstable : (prefixWord ++ tailWord_852686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852686).length < 2 ^ (prefixWord ++ tailWord_852686).sum := by decide
  have hdescent : baseEnd_852686 < baseStart_852686 := by decide
  rcases family_descends (prefixWord ++ tailWord_852686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852692 : List Nat := [2, 4, 1, 3, 2, 2, 1, 8]
def baseStart_852692 : Nat := 118140960795 + 852692 * 2 ^ 59
def prefixEnd_852692 : Nat := 4983230072969 + 3 ^ 40 * 852692 * 2
def baseEnd_852692 : Nat := 16216327638654928604761

theorem tailTrace_852692 : CollatzResearch.WordTrace tailWord_852692 prefixEnd_852692 16216327638654928604761 := by
  unfold tailWord_852692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550116113424993522328165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20733488151233324696437553 15550116113424993522328165)
  ·
    refine ⟨2915646771267186285436531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15550116113424993522328165 2915646771267186285436531)
    ·
      refine ⟨4373470156900779428154797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915646771267186285436531 4373470156900779428154797)
      ·
        refine ⟨1640051308837792285558049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4373470156900779428154797 1640051308837792285558049)
        ·
          refine ⟨1230038481628344214168537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640051308837792285558049 1230038481628344214168537)
          ·
            refine ⟨922528861221258160626403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230038481628344214168537 922528861221258160626403)
            ·
              refine ⟨1383793291831887240939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922528861221258160626403 1383793291831887240939605)
              ·
                refine ⟨16216327638654928604761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1383793291831887240939605 16216327638654928604761)
                ·
                  rfl

theorem cell23_852692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 8].length) (baseStart_852692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852692 prefixEnd_852692 := by exact prefixLift 852692
  have htrace : WordTrace (prefixWord ++ tailWord_852692) baseStart_852692 baseEnd_852692 := by
    simpa [prefixWord, tailWord_852692, baseEnd_852692] using wordTrace_append hprefix tailTrace_852692
  have hstable : (prefixWord ++ tailWord_852692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852692).length < 2 ^ (prefixWord ++ tailWord_852692).sum := by decide
  have hdescent : baseEnd_852692 < baseStart_852692 := by decide
  rcases family_descends (prefixWord ++ tailWord_852692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852728 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_852728 : Nat := 118140960795 + 852728 * 2 ^ 59
def prefixEnd_852728 : Nat := 4983230072969 + 3 ^ 40 * 852728 * 2
def baseEnd_852728 : Nat := 437859331547244931478381

theorem tailTrace_852728 : CollatzResearch.WordTrace tailWord_852728 prefixEnd_852728 437859331547244931478381 := by
  unfold tailWord_852728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550772627359782596483419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20734363503146376795311225 15550772627359782596483419)
  ·
    refine ⟨23326158941039673894725129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15550772627359782596483419 23326158941039673894725129)
    ·
      refine ⟨17494619205779755421043847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23326158941039673894725129 17494619205779755421043847)
      ·
        refine ⟨26241928808669633131565771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17494619205779755421043847 26241928808669633131565771)
        ·
          refine ⟨39362893213004449697348657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26241928808669633131565771 39362893213004449697348657)
          ·
            refine ⟨29522169909753337273011493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39362893213004449697348657 29522169909753337273011493)
            ·
              refine ⟨5535406858078750738689655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29522169909753337273011493 5535406858078750738689655)
              ·
                refine ⟨8303110287118126108034483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535406858078750738689655 8303110287118126108034483)
                ·
                  refine ⟨12454665430677189162051725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303110287118126108034483 12454665430677189162051725)
                  ·
                    refine ⟨4670499536503945935769397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12454665430677189162051725 4670499536503945935769397)
                    ·
                      refine ⟨437859331547244931478381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4670499536503945935769397 437859331547244931478381)
                      ·
                        rfl

theorem cell23_852728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_852728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852728 prefixEnd_852728 := by exact prefixLift 852728
  have htrace : WordTrace (prefixWord ++ tailWord_852728) baseStart_852728 baseEnd_852728 := by
    simpa [prefixWord, tailWord_852728, baseEnd_852728] using wordTrace_append hprefix tailTrace_852728
  have hstable : (prefixWord ++ tailWord_852728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852728).length < 2 ^ (prefixWord ++ tailWord_852728).sum := by decide
  have hdescent : baseEnd_852728 < baseStart_852728 := by decide
  rcases family_descends (prefixWord ++ tailWord_852728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852799 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 5]
def baseStart_852799 : Nat := 118140960795 + 852799 * 2 ^ 59
def prefixEnd_852799 : Nat := 4983230072969 + 3 ^ 40 * 852799 * 2
def baseEnd_852799 : Nat := 48655087630412683743395

theorem tailTrace_852799 : CollatzResearch.WordTrace tailWord_852799 prefixEnd_852799 48655087630412683743395 := by
  unfold tailWord_852799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31104134837462344318801451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20736089891641562879200967 31104134837462344318801451)
  ·
    refine ⟨46656202256193516478202177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31104134837462344318801451 46656202256193516478202177)
    ·
      refine ⟨34992151692145137358651633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46656202256193516478202177 34992151692145137358651633)
      ·
        refine ⟨26244113769108853018988725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34992151692145137358651633 26244113769108853018988725)
        ·
          refine ⟨2460385665853954970530193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26244113769108853018988725 2460385665853954970530193)
          ·
            refine ⟨1845289249390466227897645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2460385665853954970530193 1845289249390466227897645)
            ·
              refine ⟨691983468521424835461617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845289249390466227897645 691983468521424835461617)
              ·
                refine ⟨518987601391068626596213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691983468521424835461617 518987601391068626596213)
                ·
                  refine ⟨48655087630412683743395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518987601391068626596213 48655087630412683743395)
                  ·
                    rfl

theorem cell23_852799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 5].length) (baseStart_852799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852799 prefixEnd_852799 := by exact prefixLift 852799
  have htrace : WordTrace (prefixWord ++ tailWord_852799) baseStart_852799 baseEnd_852799 := by
    simpa [prefixWord, tailWord_852799, baseEnd_852799] using wordTrace_append hprefix tailTrace_852799
  have hstable : (prefixWord ++ tailWord_852799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852799).length < 2 ^ (prefixWord ++ tailWord_852799).sum := by decide
  have hdescent : baseEnd_852799 < baseStart_852799 := by decide
  rcases family_descends (prefixWord ++ tailWord_852799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852832 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_852832 : Nat := 118140960795 + 852832 * 2 ^ 59
def prefixEnd_852832 : Nat := 4983230072969 + 3 ^ 40 * 852832 * 2
def baseEnd_852832 : Nat := 437912733535312524577903

theorem tailTrace_852832 : CollatzResearch.WordTrace tailWord_852832 prefixEnd_852832 437912733535312524577903 := by
  unfold tailWord_852832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15552669223171395477376375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20736892297561860636501833 15552669223171395477376375)
  ·
    refine ⟨23329003834757093216064563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15552669223171395477376375 23329003834757093216064563)
    ·
      refine ⟨34993505752135639824096845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23329003834757093216064563 34993505752135639824096845)
      ·
        refine ⟨13122564657050864934036317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34993505752135639824096845 13122564657050864934036317)
        ·
          refine ⟨4920961746394074350263619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13122564657050864934036317 4920961746394074350263619)
          ·
            refine ⟨7381442619591111525395429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920961746394074350263619 7381442619591111525395429)
            ·
              refine ⟨1384020491173333411011643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7381442619591111525395429 1384020491173333411011643)
              ·
                refine ⟨2076030736760000116517465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384020491173333411011643 2076030736760000116517465)
                ·
                  refine ⟨1557023052570000087388099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076030736760000116517465 1557023052570000087388099)
                  ·
                    refine ⟨2335534578855000131082149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1557023052570000087388099 2335534578855000131082149)
                    ·
                      refine ⟨437912733535312524577903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2335534578855000131082149 437912733535312524577903)
                      ·
                        rfl

theorem cell23_852832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_852832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852832 prefixEnd_852832 := by exact prefixLift 852832
  have htrace : WordTrace (prefixWord ++ tailWord_852832) baseStart_852832 baseEnd_852832 := by
    simpa [prefixWord, tailWord_852832, baseEnd_852832] using wordTrace_append hprefix tailTrace_852832
  have hstable : (prefixWord ++ tailWord_852832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852832).length < 2 ^ (prefixWord ++ tailWord_852832).sum := by decide
  have hdescent : baseEnd_852832 < baseStart_852832 := by decide
  rcases family_descends (prefixWord ++ tailWord_852832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852845 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_852845 : Nat := 118140960795 + 852845 * 2 ^ 59
def prefixEnd_852845 : Nat := 4983230072969 + 3 ^ 40 * 852845 * 2
def baseEnd_852845 : Nat := 437919408783820973715343

theorem tailTrace_852845 : CollatzResearch.WordTrace tailWord_852845 prefixEnd_852845 437919408783820973715343 := by
  unfold tailWord_852845
  simp only [CollatzResearch.WordTrace]
  refine ⟨31105812595295694174975989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20737208396863796116650659 31105812595295694174975989)
  ·
    refine ⟨2916169930808971328903999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31105812595295694174975989 2916169930808971328903999)
    ·
      refine ⟨4374254896213456993355999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2916169930808971328903999 4374254896213456993355999)
      ·
        refine ⟨6561382344320185490033999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374254896213456993355999 6561382344320185490033999)
        ·
          refine ⟨9842073516480278235050999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561382344320185490033999 9842073516480278235050999)
          ·
            refine ⟨14763110274720417352576499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842073516480278235050999 14763110274720417352576499)
            ·
              refine ⟨22144665412080626028864749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14763110274720417352576499 22144665412080626028864749)
              ·
                refine ⟨8304249529530234760824281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22144665412080626028864749 8304249529530234760824281)
                ·
                  refine ⟨6228187147147676070618211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304249529530234760824281 6228187147147676070618211)
                  ·
                    refine ⟨9342280720721514105927317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228187147147676070618211 9342280720721514105927317)
                    ·
                      refine ⟨437919408783820973715343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9342280720721514105927317 437919408783820973715343)
                      ·
                        rfl

theorem cell23_852845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_852845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852845 prefixEnd_852845 := by exact prefixLift 852845
  have htrace : WordTrace (prefixWord ++ tailWord_852845) baseStart_852845 baseEnd_852845 := by
    simpa [prefixWord, tailWord_852845, baseEnd_852845] using wordTrace_append hprefix tailTrace_852845
  have hstable : (prefixWord ++ tailWord_852845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852845).length < 2 ^ (prefixWord ++ tailWord_852845).sum := by decide
  have hdescent : baseEnd_852845 < baseStart_852845 := by decide
  rcases family_descends (prefixWord ++ tailWord_852845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852872 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 6]
def baseStart_852872 : Nat := 118140960795 + 852872 * 2 ^ 59
def prefixEnd_852872 : Nat := 4983230072969 + 3 ^ 40 * 852872 * 2
def baseEnd_852872 : Nat := 48659252529054707564191

theorem tailTrace_852872 : CollatzResearch.WordTrace tailWord_852872 prefixEnd_852872 48659252529054707564191 := by
  unfold tailWord_852872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553398683098938893104435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20737864910798585190805913 15553398683098938893104435)
  ·
    refine ⟨23330098024648408339656653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15553398683098938893104435 23330098024648408339656653)
    ·
      refine ⟨8748786759243153127371245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23330098024648408339656653 8748786759243153127371245)
      ·
        refine ⟨3280795034716182422764217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8748786759243153127371245 3280795034716182422764217)
        ·
          refine ⟨2460596276037136817073163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280795034716182422764217 2460596276037136817073163)
          ·
            refine ⟨3690894414055705225609745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460596276037136817073163 3690894414055705225609745)
            ·
              refine ⟨2768170810541778919207309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690894414055705225609745 2768170810541778919207309)
              ·
                refine ⟨1038064053953167094702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768170810541778919207309 1038064053953167094702741)
                ·
                  refine ⟨48659252529054707564191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1038064053953167094702741 48659252529054707564191)
                  ·
                    rfl

theorem cell23_852872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_852872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852872 prefixEnd_852872 := by exact prefixLift 852872
  have htrace : WordTrace (prefixWord ++ tailWord_852872) baseStart_852872 baseEnd_852872 := by
    simpa [prefixWord, tailWord_852872, baseEnd_852872] using wordTrace_append hprefix tailTrace_852872
  have hstable : (prefixWord ++ tailWord_852872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852872).length < 2 ^ (prefixWord ++ tailWord_852872).sum := by decide
  have hdescent : baseEnd_852872 < baseStart_852872 := by decide
  rcases family_descends (prefixWord ++ tailWord_852872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852939 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 4]
def baseStart_852939 : Nat := 118140960795 + 852939 * 2 ^ 59
def prefixEnd_852939 : Nat := 4983230072969 + 3 ^ 40 * 852939 * 2
def baseEnd_852939 : Nat := 437967675965343605939911

theorem tailTrace_852939 : CollatzResearch.WordTrace tailWord_852939 prefixEnd_852939 437967675965343605939911 := by
  unfold tailWord_852939
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109241056955148228897871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739494037970098819265247 31109241056955148228897871)
  ·
    refine ⟨46663861585432722343346807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31109241056955148228897871 46663861585432722343346807)
    ·
      refine ⟨69995792378149083515020211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46663861585432722343346807 69995792378149083515020211)
      ·
        refine ⟨104993688567223625272530317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69995792378149083515020211 104993688567223625272530317)
        ·
          refine ⟨39372633212708859477198869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104993688567223625272530317 39372633212708859477198869)
          ·
            refine ⟨1845592181845727787993697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39372633212708859477198869 1845592181845727787993697)
            ·
              refine ⟨1384194136384295840995273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845592181845727787993697 1384194136384295840995273)
              ·
                refine ⟨1038145602288221880746455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384194136384295840995273 1038145602288221880746455)
                ·
                  refine ⟨1557218403432332821119683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038145602288221880746455 1557218403432332821119683)
                  ·
                    refine ⟨2335827605148499231679525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1557218403432332821119683 2335827605148499231679525)
                    ·
                      refine ⟨437967675965343605939911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2335827605148499231679525 437967675965343605939911)
                      ·
                        rfl

theorem cell23_852939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 4].length) (baseStart_852939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852939 prefixEnd_852939 := by exact prefixLift 852939
  have htrace : WordTrace (prefixWord ++ tailWord_852939) baseStart_852939 baseEnd_852939 := by
    simpa [prefixWord, tailWord_852939, baseEnd_852939] using wordTrace_append hprefix tailTrace_852939
  have hstable : (prefixWord ++ tailWord_852939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852939).length < 2 ^ (prefixWord ++ tailWord_852939).sum := by decide
  have hdescent : baseEnd_852939 < baseStart_852939 := by decide
  rcases family_descends (prefixWord ++ tailWord_852939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852945 : List Nat := [1, 2, 2, 1, 2, 1, 5, 9]
def baseStart_852945 : Nat := 118140960795 + 852945 * 2 ^ 59
def prefixEnd_852945 : Nat := 4983230072969 + 3 ^ 40 * 852945 * 2
def baseEnd_852945 : Nat := 16221139142565577128329

theorem tailTrace_852945 : CollatzResearch.WordTrace tailWord_852945 prefixEnd_852945 16221139142565577128329 := by
  unfold tailWord_852945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109459894933411253616289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739639929955607502410859 31109459894933411253616289)
  ·
    refine ⟨23332094921200058440212217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31109459894933411253616289 23332094921200058440212217)
    ·
      refine ⟨17499071190900043830159163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23332094921200058440212217 17499071190900043830159163)
      ·
        refine ⟨26248606786350065745238745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17499071190900043830159163 26248606786350065745238745)
        ·
          refine ⟨19686455089762549308929059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26248606786350065745238745 19686455089762549308929059)
          ·
            refine ⟨29529682634643823963393589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19686455089762549308929059 29529682634643823963393589)
            ·
              refine ⟨2768407746997858496568149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29529682634643823963393589 2768407746997858496568149)
              ·
                refine ⟨16221139142565577128329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2768407746997858496568149 16221139142565577128329)
                ·
                  rfl

theorem cell23_852945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 9].length) (baseStart_852945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852945 prefixEnd_852945 := by exact prefixLift 852945
  have htrace : WordTrace (prefixWord ++ tailWord_852945) baseStart_852945 baseEnd_852945 := by
    simpa [prefixWord, tailWord_852945, baseEnd_852945] using wordTrace_append hprefix tailTrace_852945
  have hstable : (prefixWord ++ tailWord_852945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852945).length < 2 ^ (prefixWord ++ tailWord_852945).sum := by decide
  have hdescent : baseEnd_852945 < baseStart_852945 := by decide
  rcases family_descends (prefixWord ++ tailWord_852945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852950 : List Nat := [5, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_852950 : Nat := 118140960795 + 852950 * 2 ^ 59
def prefixEnd_852950 : Nat := 4983230072969 + 3 ^ 40 * 852950 * 2
def baseEnd_852950 : Nat := 437973324252543062902361

theorem tailTrace_852950 : CollatzResearch.WordTrace tailWord_852950 prefixEnd_852950 437973324252543062902361 := by
  unfold tailWord_852950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1944352641244706069221769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20739761506610198071698869 1944352641244706069221769)
  ·
    refine ⟨1458264480933529551916327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1944352641244706069221769 1458264480933529551916327)
    ·
      refine ⟨2187396721400294327874491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458264480933529551916327 2187396721400294327874491)
      ·
        refine ⟨3281095082100441491811737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187396721400294327874491 3281095082100441491811737)
        ·
          refine ⟨2460821311575331118858803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281095082100441491811737 2460821311575331118858803)
          ·
            refine ⟨3691231967362996678288205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460821311575331118858803 3691231967362996678288205)
            ·
              refine ⟨1384211987761123754358077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691231967362996678288205 1384211987761123754358077)
              ·
                refine ⟨519079495410421407884279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384211987761123754358077 519079495410421407884279)
                ·
                  refine ⟨778619243115632111826419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519079495410421407884279 778619243115632111826419)
                  ·
                    refine ⟨1167928864673448167739629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 778619243115632111826419 1167928864673448167739629)
                    ·
                      refine ⟨437973324252543062902361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1167928864673448167739629 437973324252543062902361)
                      ·
                        rfl

theorem cell23_852950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_852950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852950 prefixEnd_852950 := by exact prefixLift 852950
  have htrace : WordTrace (prefixWord ++ tailWord_852950) baseStart_852950 baseEnd_852950 := by
    simpa [prefixWord, tailWord_852950, baseEnd_852950] using wordTrace_append hprefix tailTrace_852950
  have hstable : (prefixWord ++ tailWord_852950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852950).length < 2 ^ (prefixWord ++ tailWord_852950).sum := by decide
  have hdescent : baseEnd_852950 < baseStart_852950 := by decide
  rcases family_descends (prefixWord ++ tailWord_852950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852959 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_852959 : Nat := 118140960795 + 852959 * 2 ^ 59
def prefixEnd_852959 : Nat := 4983230072969 + 3 ^ 40 * 852959 * 2
def baseEnd_852959 : Nat := 437977945578433527689819

theorem tailTrace_852959 : CollatzResearch.WordTrace tailWord_852959 prefixEnd_852959 437977945578433527689819 := by
  unfold tailWord_852959
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109970516882691644625931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739980344588461096417287 31109970516882691644625931)
  ·
    refine ⟨46664955775324037466938897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31109970516882691644625931 46664955775324037466938897)
    ·
      refine ⟨34998716831493028100204173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46664955775324037466938897 34998716831493028100204173)
      ·
        refine ⟨13124518811809885537576565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34998716831493028100204173 13124518811809885537576565)
        ·
          refine ⟨1230423638607176769147803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13124518811809885537576565 1230423638607176769147803)
          ·
            refine ⟨1845635457910765153721705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230423638607176769147803 1845635457910765153721705)
            ·
              refine ⟨1384226593433073865291279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845635457910765153721705 1384226593433073865291279)
              ·
                refine ⟨2076339890149610797936919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384226593433073865291279 2076339890149610797936919)
                ·
                  refine ⟨3114509835224416196905379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076339890149610797936919 3114509835224416196905379)
                  ·
                    refine ⟨4671764752836624295358069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3114509835224416196905379 4671764752836624295358069)
                    ·
                      refine ⟨437977945578433527689819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4671764752836624295358069 437977945578433527689819)
                      ·
                        rfl

theorem cell23_852959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_852959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852959 prefixEnd_852959 := by exact prefixLift 852959
  have htrace : WordTrace (prefixWord ++ tailWord_852959) baseStart_852959 baseEnd_852959 := by
    simpa [prefixWord, tailWord_852959, baseEnd_852959] using wordTrace_append hprefix tailTrace_852959
  have hstable : (prefixWord ++ tailWord_852959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852959).length < 2 ^ (prefixWord ++ tailWord_852959).sum := by decide
  have hdescent : baseEnd_852959 < baseStart_852959 := by decide
  rcases family_descends (prefixWord ++ tailWord_852959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852990 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_852990 : Nat := 118140960795 + 852990 * 2 ^ 59
def prefixEnd_852990 : Nat := 4983230072969 + 3 ^ 40 * 852990 * 2
def baseEnd_852990 : Nat := 437993863478722906402177

theorem tailTrace_852990 : CollatzResearch.WordTrace tailWord_852990 prefixEnd_852990 437993863478722906402177 := by
  unfold tailWord_852990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888887647471297992375553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20740734119846922626002949 3888887647471297992375553)
  ·
    refine ⟨2916665735603473494281665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3888887647471297992375553 2916665735603473494281665)
    ·
      refine ⟨2187499301702605120711249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2916665735603473494281665 2187499301702605120711249)
      ·
        refine ⟨1640624476276953840533437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187499301702605120711249 1640624476276953840533437)
        ·
          refine ⟨615234178603857690200039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1640624476276953840533437 615234178603857690200039)
          ·
            refine ⟨922851267905786535300059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615234178603857690200039 922851267905786535300059)
            ·
              refine ⟨1384276901858679802950089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922851267905786535300059 1384276901858679802950089)
              ·
                refine ⟨1038207676394009852212567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384276901858679802950089 1038207676394009852212567)
                ·
                  refine ⟨1557311514591014778318851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038207676394009852212567 1557311514591014778318851)
                  ·
                    refine ⟨2335967271886522167478277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1557311514591014778318851 2335967271886522167478277)
                    ·
                      refine ⟨437993863478722906402177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2335967271886522167478277 437993863478722906402177)
                      ·
                        rfl

theorem cell23_852990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_852990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852990 prefixEnd_852990 := by exact prefixLift 852990
  have htrace : WordTrace (prefixWord ++ tailWord_852990) baseStart_852990 baseEnd_852990 := by
    simpa [prefixWord, tailWord_852990, baseEnd_852990] using wordTrace_append hprefix tailTrace_852990
  have hstable : (prefixWord ++ tailWord_852990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852990).length < 2 ^ (prefixWord ++ tailWord_852990).sum := by decide
  have hdescent : baseEnd_852990 < baseStart_852990 := by decide
  rcases family_descends (prefixWord ++ tailWord_852990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852995 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_852995 : Nat := 118140960795 + 852995 * 2 ^ 59
def prefixEnd_852995 : Nat := 4983230072969 + 3 ^ 40 * 852995 * 2
def baseEnd_852995 : Nat := 437996430881995386839653

theorem tailTrace_852995 : CollatzResearch.WordTrace tailWord_852995 prefixEnd_852995 437996430881995386839653 := by
  unfold tailWord_852995
  simp only [CollatzResearch.WordTrace]
  refine ⟨31111283544752269792936439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20740855696501513195290959 31111283544752269792936439)
  ·
    refine ⟨46666925317128404689404659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31111283544752269792936439 46666925317128404689404659)
    ·
      refine ⟨70000387975692607034106989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46666925317128404689404659 70000387975692607034106989)
      ·
        refine ⟨26250145490884727637790121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70000387975692607034106989 26250145490884727637790121)
        ·
          refine ⟨19687609118163545728342591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26250145490884727637790121 19687609118163545728342591)
          ·
            refine ⟨29531413677245318592513887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687609118163545728342591 29531413677245318592513887)
            ·
              refine ⟨44297120515867977888770831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531413677245318592513887 44297120515867977888770831)
              ·
                refine ⟨66445680773801966833156247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44297120515867977888770831 66445680773801966833156247)
                ·
                  refine ⟨99668521160702950249734371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66445680773801966833156247 99668521160702950249734371)
                  ·
                    refine ⟨149502781741054425374601557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99668521160702950249734371 149502781741054425374601557)
                    ·
                      refine ⟨437996430881995386839653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 149502781741054425374601557 437996430881995386839653)
                      ·
                        rfl

theorem cell23_852995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_852995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_852995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_852995 prefixEnd_852995 := by exact prefixLift 852995
  have htrace : WordTrace (prefixWord ++ tailWord_852995) baseStart_852995 baseEnd_852995 := by
    simpa [prefixWord, tailWord_852995, baseEnd_852995] using wordTrace_append hprefix tailTrace_852995
  have hstable : (prefixWord ++ tailWord_852995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852995).length < 2 ^ (prefixWord ++ tailWord_852995).sum := by decide
  have hdescent : baseEnd_852995 < baseStart_852995 := by decide
  rcases family_descends (prefixWord ++ tailWord_852995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853010 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_853010 : Nat := 118140960795 + 853010 * 2 ^ 59
def prefixEnd_853010 : Nat := 4983230072969 + 3 ^ 40 * 853010 * 2
def baseEnd_853010 : Nat := 438004133091812828152085

theorem tailTrace_853010 : CollatzResearch.WordTrace tailWord_853010 prefixEnd_853010 438004133091812828152085 := by
  unfold tailWord_853010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777957659924481838683121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20741220426465284903154989 7777957659924481838683121)
  ·
    refine ⟨5833468244943361379012341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7777957659924481838683121 5833468244943361379012341)
    ·
      refine ⟨546887647963440129282407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5833468244943361379012341 546887647963440129282407)
      ·
        refine ⟨820331471945160193923611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546887647963440129282407 820331471945160193923611)
        ·
          refine ⟨1230497207917740290885417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820331471945160193923611 1230497207917740290885417)
          ·
            refine ⟨922872905938305218164063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230497207917740290885417 922872905938305218164063)
            ·
              refine ⟨1384309358907457827246095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922872905938305218164063 1384309358907457827246095)
              ·
                refine ⟨2076464038361186740869143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384309358907457827246095 2076464038361186740869143)
                ·
                  refine ⟨3114696057541780111303715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076464038361186740869143 3114696057541780111303715)
                  ·
                    refine ⟨4672044086312670166955573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3114696057541780111303715 4672044086312670166955573)
                    ·
                      refine ⟨438004133091812828152085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4672044086312670166955573 438004133091812828152085)
                      ·
                        rfl

theorem cell23_853010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_853010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853010 prefixEnd_853010 := by exact prefixLift 853010
  have htrace : WordTrace (prefixWord ++ tailWord_853010) baseStart_853010 baseEnd_853010 := by
    simpa [prefixWord, tailWord_853010, baseEnd_853010] using wordTrace_append hprefix tailTrace_853010
  have hstable : (prefixWord ++ tailWord_853010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853010).length < 2 ^ (prefixWord ++ tailWord_853010).sum := by decide
  have hdescent : baseEnd_853010 < baseStart_853010 := by decide
  rcases family_descends (prefixWord ++ tailWord_853010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853024 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 1, 2, 2]
def baseStart_853024 : Nat := 118140960795 + 853024 * 2 ^ 59
def prefixEnd_853024 : Nat := 4983230072969 + 3 ^ 40 * 853024 * 2
def baseEnd_853024 : Nat := 438011321820975773377021

theorem tailTrace_853024 : CollatzResearch.WordTrace tailWord_853024 prefixEnd_853024 438011321820975773377021 := by
  unfold tailWord_853024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556170630823603872871063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20741560841098138497161417 15556170630823603872871063)
  ·
    refine ⟨23334255946235405809306595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15556170630823603872871063 23334255946235405809306595)
    ·
      refine ⟨35001383919353108713959893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23334255946235405809306595 35001383919353108713959893)
      ·
        refine ⟨820344935609838485483435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35001383919353108713959893 820344935609838485483435)
        ·
          refine ⟨1230517403414757728225153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820344935609838485483435 1230517403414757728225153)
          ·
            refine ⟨922888052561068296168865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1230517403414757728225153 922888052561068296168865)
            ·
              refine ⟨692166039420801222126649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922888052561068296168865 692166039420801222126649)
              ·
                refine ⟨519124529565600916594987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692166039420801222126649 519124529565600916594987)
                ·
                  refine ⟨778686794348401374892481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519124529565600916594987 778686794348401374892481)
                  ·
                    refine ⟨584015095761301031169361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778686794348401374892481 584015095761301031169361)
                    ·
                      refine ⟨438011321820975773377021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584015095761301031169361 438011321820975773377021)
                      ·
                        rfl

theorem cell23_853024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_853024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853024 prefixEnd_853024 := by exact prefixLift 853024
  have htrace : WordTrace (prefixWord ++ tailWord_853024) baseStart_853024 baseEnd_853024 := by
    simpa [prefixWord, tailWord_853024, baseEnd_853024] using wordTrace_append hprefix tailTrace_853024
  have hstable : (prefixWord ++ tailWord_853024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853024).length < 2 ^ (prefixWord ++ tailWord_853024).sum := by decide
  have hdescent : baseEnd_853024 < baseStart_853024 := by decide
  rcases family_descends (prefixWord ++ tailWord_853024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853029 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_853029 : Nat := 118140960795 + 853029 * 2 ^ 59
def prefixEnd_853029 : Nat := 4983230072969 + 3 ^ 40 * 853029 * 2
def baseEnd_853029 : Nat := 438013889224248253814497

theorem tailTrace_853029 : CollatzResearch.WordTrace tailWord_853029 prefixEnd_853029 438013889224248253814497 := by
  unfold tailWord_853029
  simp only [CollatzResearch.WordTrace]
  refine ⟨31112523626629093599674141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741682417752729066449427 31112523626629093599674141)
  ·
    refine ⟨11667196359985910099877803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31112523626629093599674141 11667196359985910099877803)
    ·
      refine ⟨17500794539978865149816705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667196359985910099877803 17500794539978865149816705)
      ·
        refine ⟨13125595904984148862362529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17500794539978865149816705 13125595904984148862362529)
        ·
          refine ⟨9844196928738111646771897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13125595904984148862362529 9844196928738111646771897)
          ·
            refine ⟨7383147696553583735078923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9844196928738111646771897 7383147696553583735078923)
            ·
              refine ⟨11074721544830375602618385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383147696553583735078923 11074721544830375602618385)
              ·
                refine ⟨8306041158622781701963789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074721544830375602618385 8306041158622781701963789)
                ·
                  refine ⟨3114765434483543138236421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8306041158622781701963789 3114765434483543138236421)
                  ·
                    refine ⟨584018518965664338419329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114765434483543138236421 584018518965664338419329)
                    ·
                      refine ⟨438013889224248253814497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584018518965664338419329 438013889224248253814497)
                      ·
                        rfl

theorem cell23_853029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_853029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853029 prefixEnd_853029 := by exact prefixLift 853029
  have htrace : WordTrace (prefixWord ++ tailWord_853029) baseStart_853029 baseEnd_853029 := by
    simpa [prefixWord, tailWord_853029, baseEnd_853029] using wordTrace_append hprefix tailTrace_853029
  have hstable : (prefixWord ++ tailWord_853029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853029).length < 2 ^ (prefixWord ++ tailWord_853029).sum := by decide
  have hdescent : baseEnd_853029 < baseStart_853029 := by decide
  rcases family_descends (prefixWord ++ tailWord_853029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853052 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 9]
def baseStart_853052 : Nat := 118140960795 + 853052 * 2 ^ 59
def prefixEnd_853052 : Nat := 4983230072969 + 3 ^ 40 * 853052 * 2
def baseEnd_853052 : Nat := 48669522142144629314099

theorem tailTrace_853052 : CollatzResearch.WordTrace tailWord_853052 prefixEnd_853052 48669522142144629314099 := by
  unfold tailWord_853052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556681252772884263880705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20742241670363845685174273 15556681252772884263880705)
  ·
    refine ⟨11667510939579663197910529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15556681252772884263880705 11667510939579663197910529)
    ·
      refine ⟨8750633204684747398432897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11667510939579663197910529 8750633204684747398432897)
      ·
        refine ⟨6562974903513560548824673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8750633204684747398432897 6562974903513560548824673)
        ·
          refine ⟨4922231177635170411618505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6562974903513560548824673 4922231177635170411618505)
          ·
            refine ⟨3691673383226377808713879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922231177635170411618505 3691673383226377808713879)
            ·
              refine ⟨5537510074839566713070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691673383226377808713879 5537510074839566713070819)
              ·
                refine ⟨8306265112259350069606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537510074839566713070819 8306265112259350069606229)
                ·
                  refine ⟨48669522142144629314099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8306265112259350069606229 48669522142144629314099)
                  ·
                    rfl

theorem cell23_853052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_853052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853052 prefixEnd_853052 := by exact prefixLift 853052
  have htrace : WordTrace (prefixWord ++ tailWord_853052) baseStart_853052 baseEnd_853052 := by
    simpa [prefixWord, tailWord_853052, baseEnd_853052] using wordTrace_append hprefix tailTrace_853052
  have hstable : (prefixWord ++ tailWord_853052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853052).length < 2 ^ (prefixWord ++ tailWord_853052).sum := by decide
  have hdescent : baseEnd_853052 < baseStart_853052 := by decide
  rcases family_descends (prefixWord ++ tailWord_853052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853089 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_853089 : Nat := 118140960795 + 853089 * 2 ^ 59
def prefixEnd_853089 : Nat := 4983230072969 + 3 ^ 40 * 853089 * 2
def baseEnd_853089 : Nat := 438044698063518019064221

theorem tailTrace_853089 : CollatzResearch.WordTrace tailWord_853089 prefixEnd_853089 438044698063518019064221 := by
  unfold tailWord_853089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114712006411723846858321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20743141337607815897905547 31114712006411723846858321)
  ·
    refine ⟨23336034004808792885143741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31114712006411723846858321 23336034004808792885143741)
    ·
      refine ⟨8751012751803297331928903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23336034004808792885143741 8751012751803297331928903)
      ·
        refine ⟨13126519127704945997893355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751012751803297331928903 13126519127704945997893355)
        ·
          refine ⟨19689778691557418996840033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126519127704945997893355 19689778691557418996840033)
          ·
            refine ⟨14767334018668064247630025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19689778691557418996840033 14767334018668064247630025)
            ·
              refine ⟨11075500514001048185722519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14767334018668064247630025 11075500514001048185722519)
              ·
                refine ⟨16613250771001572278583779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075500514001048185722519 16613250771001572278583779)
                ·
                  refine ⟨24919876156502358417875669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16613250771001572278583779 24919876156502358417875669)
                  ·
                    refine ⟨584059597418024025418961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24919876156502358417875669 584059597418024025418961)
                    ·
                      refine ⟨438044698063518019064221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584059597418024025418961 438044698063518019064221)
                      ·
                        rfl

theorem cell23_853089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_853089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853089 prefixEnd_853089 := by exact prefixLift 853089
  have htrace : WordTrace (prefixWord ++ tailWord_853089) baseStart_853089 baseEnd_853089 := by
    simpa [prefixWord, tailWord_853089, baseEnd_853089] using wordTrace_append hprefix tailTrace_853089
  have hstable : (prefixWord ++ tailWord_853089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853089).length < 2 ^ (prefixWord ++ tailWord_853089).sum := by decide
  have hdescent : baseEnd_853089 < baseStart_853089 := by decide
  rcases family_descends (prefixWord ++ tailWord_853089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853092 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_853092 : Nat := 118140960795 + 853092 * 2 ^ 59
def prefixEnd_853092 : Nat := 4983230072969 + 3 ^ 40 * 853092 * 2
def baseEnd_853092 : Nat := 438046238505481507326707

theorem tailTrace_853092 : CollatzResearch.WordTrace tailWord_853092 prefixEnd_853092 438046238505481507326707 := by
  unfold tailWord_853092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557410712700427679608765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743214283600570239478353 15557410712700427679608765)
  ·
    refine ⟨5834029017262660379853287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15557410712700427679608765 5834029017262660379853287)
    ·
      refine ⟨8751043525893990569779931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834029017262660379853287 8751043525893990569779931)
      ·
        refine ⟨13126565288840985854669897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751043525893990569779931 13126565288840985854669897)
        ·
          refine ⟨9844923966630739391002423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13126565288840985854669897 9844923966630739391002423)
          ·
            refine ⟨14767385949946109086503635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844923966630739391002423 14767385949946109086503635)
            ·
              refine ⟨22151078924919163629755453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767385949946109086503635 22151078924919163629755453)
              ·
                refine ⟨8306654596844686361158295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22151078924919163629755453 8306654596844686361158295)
                ·
                  refine ⟨12459981895267029541737443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306654596844686361158295 12459981895267029541737443)
                  ·
                    refine ⟨18689972842900544312606165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12459981895267029541737443 18689972842900544312606165)
                    ·
                      refine ⟨438046238505481507326707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18689972842900544312606165 438046238505481507326707)
                      ·
                        rfl

theorem cell23_853092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_853092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853092 prefixEnd_853092 := by exact prefixLift 853092
  have htrace : WordTrace (prefixWord ++ tailWord_853092) baseStart_853092 baseEnd_853092 := by
    simpa [prefixWord, tailWord_853092, baseEnd_853092] using wordTrace_append hprefix tailTrace_853092
  have hstable : (prefixWord ++ tailWord_853092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853092).length < 2 ^ (prefixWord ++ tailWord_853092).sum := by decide
  have hdescent : baseEnd_853092 < baseStart_853092 := by decide
  rcases family_descends (prefixWord ++ tailWord_853092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853132 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_853132 : Nat := 118140960795 + 853132 * 2 ^ 59
def prefixEnd_853132 : Nat := 4983230072969 + 3 ^ 40 * 853132 * 2
def baseEnd_853132 : Nat := 438066777731661350826523

theorem tailTrace_853132 : CollatzResearch.WordTrace tailWord_853132 prefixEnd_853132 438066777731661350826523 := by
  unfold tailWord_853132
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558140172627971095336825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20744186896837294793782433 15558140172627971095336825)
  ·
    refine ⟨11668605129470978321502619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15558140172627971095336825 11668605129470978321502619)
    ·
      refine ⟨17502907694206467482253929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668605129470978321502619 17502907694206467482253929)
      ·
        refine ⟨13127180770654850611690447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17502907694206467482253929 13127180770654850611690447)
        ·
          refine ⟨19690771155982275917535671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13127180770654850611690447 19690771155982275917535671)
          ·
            refine ⟨29536156733973413876303507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19690771155982275917535671 29536156733973413876303507)
            ·
              refine ⟨44304235100960120814455261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29536156733973413876303507 44304235100960120814455261)
              ·
                refine ⟨16614088162860045305420723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44304235100960120814455261 16614088162860045305420723)
                ·
                  refine ⟨24921132244290067958131085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16614088162860045305420723 24921132244290067958131085)
                  ·
                    refine ⟨9345424591608775484299157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24921132244290067958131085 9345424591608775484299157)
                    ·
                      refine ⟨438066777731661350826523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9345424591608775484299157 438066777731661350826523)
                      ·
                        rfl

theorem cell23_853132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_853132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853132 prefixEnd_853132 := by exact prefixLift 853132
  have htrace : WordTrace (prefixWord ++ tailWord_853132) baseStart_853132 baseEnd_853132 := by
    simpa [prefixWord, tailWord_853132, baseEnd_853132] using wordTrace_append hprefix tailTrace_853132
  have hstable : (prefixWord ++ tailWord_853132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853132).length < 2 ^ (prefixWord ++ tailWord_853132).sum := by decide
  have hdescent : baseEnd_853132 < baseStart_853132 := by decide
  rcases family_descends (prefixWord ++ tailWord_853132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853139 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3]
def baseStart_853139 : Nat := 118140960795 + 853139 * 2 ^ 59
def prefixEnd_853139 : Nat := 4983230072969 + 3 ^ 40 * 853139 * 2
def baseEnd_853139 : Nat := 438070372096242823438991

theorem tailTrace_853139 : CollatzResearch.WordTrace tailWord_853139 prefixEnd_853139 438070372096242823438991 := by
  unfold tailWord_853139
  simp only [CollatzResearch.WordTrace]
  refine ⟨31116535656230582386178471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20744357104153721590785647 31116535656230582386178471)
  ·
    refine ⟨46674803484345873579267707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31116535656230582386178471 46674803484345873579267707)
    ·
      refine ⟨70012205226518810368901561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46674803484345873579267707 70012205226518810368901561)
      ·
        refine ⟨52509153919889107776676171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70012205226518810368901561 52509153919889107776676171)
        ·
          refine ⟨78763730879833661665014257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52509153919889107776676171 78763730879833661665014257)
          ·
            refine ⟨59072798159875246248760693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78763730879833661665014257 59072798159875246248760693)
            ·
              refine ⟨5538074827488304335821315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59072798159875246248760693 5538074827488304335821315)
              ·
                refine ⟨8307112241232456503731973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538074827488304335821315 8307112241232456503731973)
                ·
                  refine ⟨1557583545231085594449745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8307112241232456503731973 1557583545231085594449745)
                  ·
                    refine ⟨1168187658923314195837309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557583545231085594449745 1168187658923314195837309)
                    ·
                      refine ⟨438070372096242823438991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168187658923314195837309 438070372096242823438991)
                      ·
                        rfl

theorem cell23_853139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_853139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853139 prefixEnd_853139 := by exact prefixLift 853139
  have htrace : WordTrace (prefixWord ++ tailWord_853139) baseStart_853139 baseEnd_853139 := by
    simpa [prefixWord, tailWord_853139, baseEnd_853139] using wordTrace_append hprefix tailTrace_853139
  have hstable : (prefixWord ++ tailWord_853139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853139).length < 2 ^ (prefixWord ++ tailWord_853139).sum := by decide
  have hdescent : baseEnd_853139 < baseStart_853139 := by decide
  rcases family_descends (prefixWord ++ tailWord_853139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853203 : List Nat := [1, 1, 1, 2, 1, 1, 1, 10, 1, 1, 3]
def baseStart_853203 : Nat := 118140960795 + 853203 * 2 ^ 59
def prefixEnd_853203 : Nat := 4983230072969 + 3 ^ 40 * 853203 * 2
def baseEnd_853203 : Nat := 438103234858130573038697

theorem tailTrace_853203 : CollatzResearch.WordTrace tailWord_853203 prefixEnd_853203 438103234858130573038697 := by
  unfold tailWord_853203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31118869927998721316508263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20745913285332480877672175 31118869927998721316508263)
  ·
    refine ⟨46678304891998081974762395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31118869927998721316508263 46678304891998081974762395)
    ·
      refine ⟨70017457337997122962143593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46678304891998081974762395 70017457337997122962143593)
      ·
        refine ⟨52513093003497842221607695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70017457337997122962143593 52513093003497842221607695)
        ·
          refine ⟨78769639505246763332411543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52513093003497842221607695 78769639505246763332411543)
          ·
            refine ⟨118154459257870144998617315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78769639505246763332411543 118154459257870144998617315)
            ·
              refine ⟨177231688886805217497925973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118154459257870144998617315 177231688886805217497925973)
              ·
                refine ⟨519233463535562160638455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 177231688886805217497925973 519233463535562160638455)
                ·
                  refine ⟨778850195303343240957683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519233463535562160638455 778850195303343240957683)
                  ·
                    refine ⟨1168275292955014861436525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 778850195303343240957683 1168275292955014861436525)
                    ·
                      refine ⟨438103234858130573038697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168275292955014861436525 438103234858130573038697)
                      ·
                        rfl

theorem cell23_853203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 10, 1, 1, 3].length) (baseStart_853203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853203 prefixEnd_853203 := by exact prefixLift 853203
  have htrace : WordTrace (prefixWord ++ tailWord_853203) baseStart_853203 baseEnd_853203 := by
    simpa [prefixWord, tailWord_853203, baseEnd_853203] using wordTrace_append hprefix tailTrace_853203
  have hstable : (prefixWord ++ tailWord_853203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853203).length < 2 ^ (prefixWord ++ tailWord_853203).sum := by decide
  have hdescent : baseEnd_853203 < baseStart_853203 := by decide
  rcases family_descends (prefixWord ++ tailWord_853203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853226 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_853226 : Nat := 118140960795 + 853226 * 2 ^ 59
def prefixEnd_853226 : Nat := 4983230072969 + 3 ^ 40 * 853226 * 2
def baseEnd_853226 : Nat := 438115044913183983051091

theorem tailTrace_853226 : CollatzResearch.WordTrace tailWord_853226 prefixEnd_853226 438115044913183983051091 := by
  unfold tailWord_853226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779927201728849061148883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20746472537943597496397021 7779927201728849061148883)
  ·
    refine ⟨11669890802593273591723325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779927201728849061148883 11669890802593273591723325)
    ·
      refine ⟨4376209050972477596896247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11669890802593273591723325 4376209050972477596896247)
      ·
        refine ⟨6564313576458716395344371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376209050972477596896247 6564313576458716395344371)
        ·
          refine ⟨9846470364688074593016557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564313576458716395344371 9846470364688074593016557)
          ·
            refine ⟨3692426386758027972381209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9846470364688074593016557 3692426386758027972381209)
            ·
              refine ⟨2769319790068520979285907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692426386758027972381209 2769319790068520979285907)
              ·
                refine ⟨4153979685102781468928861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769319790068520979285907 4153979685102781468928861)
                ·
                  refine ⟨1557742381913543050848323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4153979685102781468928861 1557742381913543050848323)
                  ·
                    refine ⟨2336613572870314576272485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1557742381913543050848323 2336613572870314576272485)
                    ·
                      refine ⟨438115044913183983051091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2336613572870314576272485 438115044913183983051091)
                      ·
                        rfl

theorem cell23_853226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_853226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853226 prefixEnd_853226 := by exact prefixLift 853226
  have htrace : WordTrace (prefixWord ++ tailWord_853226) baseStart_853226 baseEnd_853226 := by
    simpa [prefixWord, tailWord_853226, baseEnd_853226] using wordTrace_append hprefix tailTrace_853226
  have hstable : (prefixWord ++ tailWord_853226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853226).length < 2 ^ (prefixWord ++ tailWord_853226).sum := by decide
  have hdescent : baseEnd_853226 < baseStart_853226 := by decide
  rcases family_descends (prefixWord ++ tailWord_853226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853249 : List Nat := [1, 2, 4, 1, 1, 4, 10]
def baseStart_853249 : Nat := 118140960795 + 853249 * 2 ^ 59
def prefixEnd_853249 : Nat := 4983230072969 + 3 ^ 40 * 853249 * 2
def baseEnd_853249 : Nat := 5408973518126387568685

theorem tailTrace_853249 : CollatzResearch.WordTrace tailWord_853249 prefixEnd_853249 5408973518126387568685 := by
  unfold tailWord_853249
  simp only [CollatzResearch.WordTrace]
  refine ⟨31120547685832071172682801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20747031790554714115121867 31120547685832071172682801)
  ·
    refine ⟨23340410764374053379512101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31120547685832071172682801 23340410764374053379512101)
    ·
      refine ⟨4376327018320135008658519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23340410764374053379512101 4376327018320135008658519)
      ·
        refine ⟨6564490527480202512987779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376327018320135008658519 6564490527480202512987779)
        ·
          refine ⟨9846735791220303769481669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564490527480202512987779 9846735791220303769481669)
          ·
            refine ⟨1846262960853806956777813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9846735791220303769481669 1846262960853806956777813)
            ·
              refine ⟨5408973518126387568685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1846262960853806956777813 5408973518126387568685)
              ·
                rfl

theorem cell23_853249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 10].length) (baseStart_853249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853249 prefixEnd_853249 := by exact prefixLift 853249
  have htrace : WordTrace (prefixWord ++ tailWord_853249) baseStart_853249 baseEnd_853249 := by
    simpa [prefixWord, tailWord_853249, baseEnd_853249] using wordTrace_append hprefix tailTrace_853249
  have hstable : (prefixWord ++ tailWord_853249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853249).length < 2 ^ (prefixWord ++ tailWord_853249).sum := by decide
  have hdescent : baseEnd_853249 < baseStart_853249 := by decide
  rcases family_descends (prefixWord ++ tailWord_853249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853260 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_853260 : Nat := 118140960795 + 853260 * 2 ^ 59
def prefixEnd_853260 : Nat := 4983230072969 + 3 ^ 40 * 853260 * 2
def baseEnd_853260 : Nat := 438132503255436850025935

theorem tailTrace_853260 : CollatzResearch.WordTrace tailWord_853260 prefixEnd_853260 438132503255436850025935 := by
  unfold tailWord_853260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15560474444396110025666617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20747299259194813367555489 15560474444396110025666617)
  ·
    refine ⟨11670355833297082519249963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15560474444396110025666617 11670355833297082519249963)
    ·
      refine ⟨17505533749945623778874945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11670355833297082519249963 17505533749945623778874945)
      ·
        refine ⟨13129150312459217834156209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17505533749945623778874945 13129150312459217834156209)
        ·
          refine ⟨9846862734344413375617157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13129150312459217834156209 9846862734344413375617157)
          ·
            refine ⟨1846286762689577507928217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9846862734344413375617157 1846286762689577507928217)
            ·
              refine ⟨1384715072017183130946163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846286762689577507928217 1384715072017183130946163)
              ·
                refine ⟨2077072608025774696419245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384715072017183130946163 2077072608025774696419245)
                ·
                  refine ⟨778902228009665511157217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2077072608025774696419245 778902228009665511157217)
                  ·
                    refine ⟨584176671007249133367913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 778902228009665511157217 584176671007249133367913)
                    ·
                      refine ⟨438132503255436850025935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584176671007249133367913 438132503255436850025935)
                      ·
                        rfl

theorem cell23_853260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_853260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853260 prefixEnd_853260 := by exact prefixLift 853260
  have htrace : WordTrace (prefixWord ++ tailWord_853260) baseStart_853260 baseEnd_853260 := by
    simpa [prefixWord, tailWord_853260, baseEnd_853260] using wordTrace_append hprefix tailTrace_853260
  have hstable : (prefixWord ++ tailWord_853260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853260).length < 2 ^ (prefixWord ++ tailWord_853260).sum := by decide
  have hdescent : baseEnd_853260 < baseStart_853260 := by decide
  rcases family_descends (prefixWord ++ tailWord_853260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853280 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_853280 : Nat := 118140960795 + 853280 * 2 ^ 59
def prefixEnd_853280 : Nat := 4983230072969 + 3 ^ 40 * 853280 * 2
def baseEnd_853280 : Nat := 438142772868526771775843

theorem tailTrace_853280 : CollatzResearch.WordTrace tailWord_853280 prefixEnd_853280 438142772868526771775843 := by
  unfold tailWord_853280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15560839174359881733530647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20747785565813175644707529 15560839174359881733530647)
  ·
    refine ⟨23341258761539822600295971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15560839174359881733530647 23341258761539822600295971)
    ·
      refine ⟨35011888142309733900443957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23341258761539822600295971 35011888142309733900443957)
      ·
        refine ⟨3282364513341537553166621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35011888142309733900443957 3282364513341537553166621)
        ·
          refine ⟨1230886692503076582437483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3282364513341537553166621 1230886692503076582437483)
          ·
            refine ⟨1846330038754614873656225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230886692503076582437483 1846330038754614873656225)
            ·
              refine ⟨1384747529065961155242169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846330038754614873656225 1384747529065961155242169)
              ·
                refine ⟨1038560646799470866431627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384747529065961155242169 1038560646799470866431627)
                ·
                  refine ⟨1557840970199206299647441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038560646799470866431627 1557840970199206299647441)
                  ·
                    refine ⟨1168380727649404724735581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557840970199206299647441 1168380727649404724735581)
                    ·
                      refine ⟨438142772868526771775843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168380727649404724735581 438142772868526771775843)
                      ·
                        rfl

theorem cell23_853280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_853280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853280 prefixEnd_853280 := by exact prefixLift 853280
  have htrace : WordTrace (prefixWord ++ tailWord_853280) baseStart_853280 baseEnd_853280 := by
    simpa [prefixWord, tailWord_853280, baseEnd_853280] using wordTrace_append hprefix tailTrace_853280
  have hstable : (prefixWord ++ tailWord_853280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853280).length < 2 ^ (prefixWord ++ tailWord_853280).sum := by decide
  have hdescent : baseEnd_853280 < baseStart_853280 := by decide
  rcases family_descends (prefixWord ++ tailWord_853280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853310 : List Nat := [4, 2, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_853310 : Nat := 118140960795 + 853310 * 2 ^ 59
def prefixEnd_853310 : Nat := 4983230072969 + 3 ^ 40 * 853310 * 2
def baseEnd_853310 : Nat := 438158177288161654400705

theorem tailTrace_853310 : CollatzResearch.WordTrace tailWord_853310 prefixEnd_853310 438158177288161654400705 := by
  unfold tailWord_853310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890346567326384823831673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20748515025740719060435589 3890346567326384823831673)
  ·
    refine ⟨2917759925494788617873755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3890346567326384823831673 2917759925494788617873755)
    ·
      refine ⟨4376639888242182926810633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917759925494788617873755 4376639888242182926810633)
      ·
        refine ⟨3282479916181637195107975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4376639888242182926810633 3282479916181637195107975)
        ·
          refine ⟨4923719874272455792661963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282479916181637195107975 4923719874272455792661963)
          ·
            refine ⟨7385579811408683688992945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923719874272455792661963 7385579811408683688992945)
            ·
              refine ⟨5539184858556512766744709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385579811408683688992945 5539184858556512766744709)
              ·
                refine ⟨1038597160979346143764633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5539184858556512766744709 1038597160979346143764633)
                ·
                  refine ⟨778947870734509607823475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1038597160979346143764633 778947870734509607823475)
                  ·
                    refine ⟨1168421806101764411735213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 778947870734509607823475 1168421806101764411735213)
                    ·
                      refine ⟨438158177288161654400705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168421806101764411735213 438158177288161654400705)
                      ·
                        rfl

theorem cell23_853310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_853310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853310 prefixEnd_853310 := by exact prefixLift 853310
  have htrace : WordTrace (prefixWord ++ tailWord_853310) baseStart_853310 baseEnd_853310 := by
    simpa [prefixWord, tailWord_853310, baseEnd_853310] using wordTrace_append hprefix tailTrace_853310
  have hstable : (prefixWord ++ tailWord_853310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853310).length < 2 ^ (prefixWord ++ tailWord_853310).sum := by decide
  have hdescent : baseEnd_853310 < baseStart_853310 := by decide
  rcases family_descends (prefixWord ++ tailWord_853310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853354 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_853354 : Nat := 118140960795 + 853354 * 2 ^ 59
def prefixEnd_853354 : Nat := 4983230072969 + 3 ^ 40 * 853354 * 2
def baseEnd_853354 : Nat := 438180770436959482250503

theorem tailTrace_853354 : CollatzResearch.WordTrace tailWord_853354 prefixEnd_853354 438180770436959482250503 := by
  unfold tailWord_853354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781094337612918526313779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20749584900301116070170077 7781094337612918526313779)
  ·
    refine ⟨11671641506419377789470669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7781094337612918526313779 11671641506419377789470669)
    ·
      refine ⟨4376865564907266671051501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11671641506419377789470669 4376865564907266671051501)
      ·
        refine ⟨1641324586840225001644313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4376865564907266671051501 1641324586840225001644313)
        ·
          refine ⟨1230993440130168751233235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641324586840225001644313 1230993440130168751233235)
          ·
            refine ⟨1846490160195253126849853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230993440130168751233235 1846490160195253126849853)
            ·
              refine ⟨692433810073219922568695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1846490160195253126849853 692433810073219922568695)
              ·
                refine ⟨1038650715109829883853043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692433810073219922568695 1038650715109829883853043)
                ·
                  refine ⟨1557976072664744825779565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038650715109829883853043 1557976072664744825779565)
                  ·
                    refine ⟨584241027249279309667337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1557976072664744825779565 584241027249279309667337)
                    ·
                      refine ⟨438180770436959482250503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584241027249279309667337 438180770436959482250503)
                      ·
                        rfl

theorem cell23_853354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_853354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853354 prefixEnd_853354 := by exact prefixLift 853354
  have htrace : WordTrace (prefixWord ++ tailWord_853354) baseStart_853354 baseEnd_853354 := by
    simpa [prefixWord, tailWord_853354, baseEnd_853354] using wordTrace_append hprefix tailTrace_853354
  have hstable : (prefixWord ++ tailWord_853354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853354).length < 2 ^ (prefixWord ++ tailWord_853354).sum := by decide
  have hdescent : baseEnd_853354 < baseStart_853354 := by decide
  rcases family_descends (prefixWord ++ tailWord_853354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853373 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 5]
def baseStart_853373 : Nat := 118140960795 + 853373 * 2 ^ 59
def prefixEnd_853373 : Nat := 4983230072969 + 3 ^ 40 * 853373 * 2
def baseEnd_853373 : Nat := 48687836285488323101435

theorem tailTrace_853373 : CollatzResearch.WordTrace tailWord_853373 prefixEnd_853373 48687836285488323101435 := by
  unfold tailWord_853373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31125070337382840350196773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20750046891588560233464515 31125070337382840350196773)
  ·
    refine ⟨5835950688259282565661895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31125070337382840350196773 5835950688259282565661895)
    ·
      refine ⟨8753926032388923848492843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5835950688259282565661895 8753926032388923848492843)
      ·
        refine ⟨13130889048583385772739265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753926032388923848492843 13130889048583385772739265)
        ·
          refine ⟨9848166786437539329554449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13130889048583385772739265 9848166786437539329554449)
          ·
            refine ⟨7386125089828154497165837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9848166786437539329554449 7386125089828154497165837)
            ·
              refine ⟨2769796908685557936437189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7386125089828154497165837 2769796908685557936437189)
              ·
                refine ⟨519336920378542113081973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2769796908685557936437189 519336920378542113081973)
                ·
                  refine ⟨48687836285488323101435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519336920378542113081973 48687836285488323101435)
                  ·
                    rfl

theorem cell23_853373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_853373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853373 prefixEnd_853373 := by exact prefixLift 853373
  have htrace : WordTrace (prefixWord ++ tailWord_853373) baseStart_853373 baseEnd_853373 := by
    simpa [prefixWord, tailWord_853373, baseEnd_853373] using wordTrace_append hprefix tailTrace_853373
  have hstable : (prefixWord ++ tailWord_853373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853373).length < 2 ^ (prefixWord ++ tailWord_853373).sum := by decide
  have hdescent : baseEnd_853373 < baseStart_853373 := by decide
  rcases family_descends (prefixWord ++ tailWord_853373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853383 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_853383 : Nat := 118140960795 + 853383 * 2 ^ 59
def prefixEnd_853383 : Nat := 4983230072969 + 3 ^ 40 * 853383 * 2
def baseEnd_853383 : Nat := 438195661375939868787869

theorem tailTrace_853383 : CollatzResearch.WordTrace tailWord_853383 prefixEnd_853383 438195661375939868787869 := by
  unfold tailWord_853383
  simp only [CollatzResearch.WordTrace]
  refine ⟨31125435067346612058060803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20750290044897741372040535 31125435067346612058060803)
  ·
    refine ⟨46688152601019918087091205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31125435067346612058060803 46688152601019918087091205)
    ·
      refine ⟨8754028612691234641329601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46688152601019918087091205 8754028612691234641329601)
      ·
        refine ⟨6565521459518425980997201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8754028612691234641329601 6565521459518425980997201)
        ·
          refine ⟨4924141094638819485747901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565521459518425980997201 4924141094638819485747901)
          ·
            refine ⟨1846552910489557307155463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924141094638819485747901 1846552910489557307155463)
            ·
              refine ⟨2769829365734335960733195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846552910489557307155463 2769829365734335960733195)
              ·
                refine ⟨4154744048601503941099793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769829365734335960733195 4154744048601503941099793)
                ·
                  refine ⟨3116058036451127955824845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4154744048601503941099793 3116058036451127955824845)
                  ·
                    refine ⟨1168521763669172983434317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116058036451127955824845 1168521763669172983434317)
                    ·
                      refine ⟨438195661375939868787869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168521763669172983434317 438195661375939868787869)
                      ·
                        rfl

theorem cell23_853383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_853383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853383 prefixEnd_853383 := by exact prefixLift 853383
  have htrace : WordTrace (prefixWord ++ tailWord_853383) baseStart_853383 baseEnd_853383 := by
    simpa [prefixWord, tailWord_853383, baseEnd_853383] using wordTrace_append hprefix tailTrace_853383
  have hstable : (prefixWord ++ tailWord_853383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853383).length < 2 ^ (prefixWord ++ tailWord_853383).sum := by decide
  have hdescent : baseEnd_853383 < baseStart_853383 := by decide
  rcases family_descends (prefixWord ++ tailWord_853383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853483 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 5, 2]
def baseStart_853483 : Nat := 118140960795 + 853483 * 2 ^ 59
def prefixEnd_853483 : Nat := 4983230072969 + 3 ^ 40 * 853483 * 2
def baseEnd_853483 : Nat := 438247009441389477537409

theorem tailTrace_853483 : CollatzResearch.WordTrace tailWord_853483 prefixEnd_853483 438247009441389477537409 := by
  unfold tailWord_853483
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129082366984329136701103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752721577989552757800735 31129082366984329136701103)
  ·
    refine ⟨46693623550476493705051655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31129082366984329136701103 46693623550476493705051655)
    ·
      refine ⟨70040435325714740557577483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46693623550476493705051655 70040435325714740557577483)
      ·
        refine ⟨105060652988572110836366225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70040435325714740557577483 105060652988572110836366225)
        ·
          refine ⟨78795489741429083127274669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105060652988572110836366225 78795489741429083127274669)
          ·
            refine ⟨29548308653035906172728001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78795489741429083127274669 29548308653035906172728001)
            ·
              refine ⟨22161231489776929629546001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29548308653035906172728001 22161231489776929629546001)
              ·
                refine ⟨16620923617332697222159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22161231489776929629546001 16620923617332697222159501)
                ·
                  refine ⟨6232846356499761458309813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16620923617332697222159501 6232846356499761458309813)
                  ·
                    refine ⟨584329345921852636716545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6232846356499761458309813 584329345921852636716545)
                    ·
                      refine ⟨438247009441389477537409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584329345921852636716545 438247009441389477537409)
                      ·
                        rfl

theorem cell23_853483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5, 2].length) (baseStart_853483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853483 prefixEnd_853483 := by exact prefixLift 853483
  have htrace : WordTrace (prefixWord ++ tailWord_853483) baseStart_853483 baseEnd_853483 := by
    simpa [prefixWord, tailWord_853483, baseEnd_853483] using wordTrace_append hprefix tailTrace_853483
  have hstable : (prefixWord ++ tailWord_853483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853483).length < 2 ^ (prefixWord ++ tailWord_853483).sum := by decide
  have hdescent : baseEnd_853483 < baseStart_853483 := by decide
  rcases family_descends (prefixWord ++ tailWord_853483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853513 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_853513 : Nat := 118140960795 + 853513 * 2 ^ 59
def prefixEnd_853513 : Nat := 4983230072969 + 3 ^ 40 * 853513 * 2
def baseEnd_853513 : Nat := 438262413861024360162271

theorem tailTrace_853513 : CollatzResearch.WordTrace tailWord_853513 prefixEnd_853513 438262413861024360162271 := by
  unfold tailWord_853513
  simp only [CollatzResearch.WordTrace]
  refine ⟨31130176556875644260293193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20753451037917096173528795 31130176556875644260293193)
  ·
    refine ⟨23347632417656733195219895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31130176556875644260293193 23347632417656733195219895)
    ·
      refine ⟨35021448626485099792829843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23347632417656733195219895 35021448626485099792829843)
      ·
        refine ⟨52532172939727649689244765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35021448626485099792829843 52532172939727649689244765)
        ·
          refine ⟨19699564852397868633466787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52532172939727649689244765 19699564852397868633466787)
          ·
            refine ⟨29549347278596802950200181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19699564852397868633466787 29549347278596802950200181)
            ·
              refine ⟨2770251307368450276581267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29549347278596802950200181 2770251307368450276581267)
              ·
                refine ⟨4155376961052675414871901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770251307368450276581267 4155376961052675414871901)
                ·
                  refine ⟨1558266360394753280576963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4155376961052675414871901 1558266360394753280576963)
                  ·
                    refine ⟨2337399540592129920865445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558266360394753280576963 2337399540592129920865445)
                    ·
                      refine ⟨438262413861024360162271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2337399540592129920865445 438262413861024360162271)
                      ·
                        rfl

theorem cell23_853513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_853513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853513 prefixEnd_853513 := by exact prefixLift 853513
  have htrace : WordTrace (prefixWord ++ tailWord_853513) baseStart_853513 baseEnd_853513 := by
    simpa [prefixWord, tailWord_853513, baseEnd_853513] using wordTrace_append hprefix tailTrace_853513
  have hstable : (prefixWord ++ tailWord_853513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853513).length < 2 ^ (prefixWord ++ tailWord_853513).sum := by decide
  have hdescent : baseEnd_853513 < baseStart_853513 := by decide
  rcases family_descends (prefixWord ++ tailWord_853513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853523 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 1, 6]
def baseStart_853523 : Nat := 118140960795 + 853523 * 2 ^ 59
def prefixEnd_853523 : Nat := 4983230072969 + 3 ^ 40 * 853523 * 2
def baseEnd_853523 : Nat := 146089182889189773679075

theorem tailTrace_853523 : CollatzResearch.WordTrace tailWord_853523 prefixEnd_853523 146089182889189773679075 := by
  unfold tailWord_853523
  simp only [CollatzResearch.WordTrace]
  refine ⟨31130541286839415968157223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20753694191226277312104815 31130541286839415968157223)
  ·
    refine ⟨46695811930259123952235835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31130541286839415968157223 46695811930259123952235835)
    ·
      refine ⟨70043717895388685928353753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46695811930259123952235835 70043717895388685928353753)
      ·
        refine ⟨52532788421541514446265315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70043717895388685928353753 52532788421541514446265315)
        ·
          refine ⟨78799182632312271669397973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52532788421541514446265315 78799182632312271669397973)
          ·
            refine ⟨1846855842944818867251515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78799182632312271669397973 1846855842944818867251515)
            ·
              refine ⟨2770283764417228300877273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846855842944818867251515 2770283764417228300877273)
              ·
                refine ⟨2077712823312921225657955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770283764417228300877273 2077712823312921225657955)
                ·
                  refine ⟨3116569234969381838486933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077712823312921225657955 3116569234969381838486933)
                  ·
                    refine ⟨146089182889189773679075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3116569234969381838486933 146089182889189773679075)
                    ·
                      rfl

theorem cell23_853523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_853523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853523 prefixEnd_853523 := by exact prefixLift 853523
  have htrace : WordTrace (prefixWord ++ tailWord_853523) baseStart_853523 baseEnd_853523 := by
    simpa [prefixWord, tailWord_853523, baseEnd_853523] using wordTrace_append hprefix tailTrace_853523
  have hstable : (prefixWord ++ tailWord_853523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853523).length < 2 ^ (prefixWord ++ tailWord_853523).sum := by decide
  have hdescent : baseEnd_853523 < baseStart_853523 := by decide
  rcases family_descends (prefixWord ++ tailWord_853523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853560 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_853560 : Nat := 118140960795 + 853560 * 2 ^ 59
def prefixEnd_853560 : Nat := 4983230072969 + 3 ^ 40 * 853560 * 2
def baseEnd_853560 : Nat := 438286547451785676274555

theorem tailTrace_853560 : CollatzResearch.WordTrace tailWord_853560 prefixEnd_853560 438286547451785676274555 := by
  unfold tailWord_853560
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565945393852685643627067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20754593858470247524836089 15565945393852685643627067)
  ·
    refine ⟨23348918090779028465440601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15565945393852685643627067 23348918090779028465440601)
    ·
      refine ⟨17511688568084271349080451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23348918090779028465440601 17511688568084271349080451)
      ·
        refine ⟨26267532852126407023620677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511688568084271349080451 26267532852126407023620677)
        ·
          refine ⟨4925162409773701316928877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26267532852126407023620677 4925162409773701316928877)
          ·
            refine ⟨1846935903665137993848329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4925162409773701316928877 1846935903665137993848329)
            ·
              refine ⟨1385201927748853495386247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846935903665137993848329 1385201927748853495386247)
              ·
                refine ⟨2077802891623280243079371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385201927748853495386247 2077802891623280243079371)
                ·
                  refine ⟨3116704337434920364619057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077802891623280243079371 3116704337434920364619057)
                  ·
                    refine ⟨2337528253076190273464293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116704337434920364619057 2337528253076190273464293)
                    ·
                      refine ⟨438286547451785676274555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2337528253076190273464293 438286547451785676274555)
                      ·
                        rfl

theorem cell23_853560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_853560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853560 prefixEnd_853560 := by exact prefixLift 853560
  have htrace : WordTrace (prefixWord ++ tailWord_853560) baseStart_853560 baseEnd_853560 := by
    simpa [prefixWord, tailWord_853560, baseEnd_853560] using wordTrace_append hprefix tailTrace_853560
  have hstable : (prefixWord ++ tailWord_853560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853560).length < 2 ^ (prefixWord ++ tailWord_853560).sum := by decide
  have hdescent : baseEnd_853560 < baseStart_853560 := by decide
  rcases family_descends (prefixWord ++ tailWord_853560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853564 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_853564 : Nat := 118140960795 + 853564 * 2 ^ 59
def prefixEnd_853564 : Nat := 4983230072969 + 3 ^ 40 * 853564 * 2
def baseEnd_853564 : Nat := 438288601374403660624537

theorem tailTrace_853564 : CollatzResearch.WordTrace tailWord_853564 prefixEnd_853564 438288601374403660624537 := by
  unfold tailWord_853564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566018339845439985199873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20754691119793919980266497 15566018339845439985199873)
  ·
    refine ⟨11674513754884079988899905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15566018339845439985199873 11674513754884079988899905)
    ·
      refine ⟨8755885316163059991674929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11674513754884079988899905 8755885316163059991674929)
      ·
        refine ⟨6566913987122294993756197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8755885316163059991674929 6566913987122294993756197)
        ·
          refine ⟨1231296372585430311329287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6566913987122294993756197 1231296372585430311329287)
          ·
            refine ⟨1846944558878145466993931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231296372585430311329287 1846944558878145466993931)
            ·
              refine ⟨2770416838317218200490897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846944558878145466993931 2770416838317218200490897)
              ·
                refine ⟨2077812628737913650368173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770416838317218200490897 2077812628737913650368173)
                ·
                  refine ⟨779179735776717618888065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2077812628737913650368173 779179735776717618888065)
                  ·
                    refine ⟨584384801832538214166049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 779179735776717618888065 584384801832538214166049)
                    ·
                      refine ⟨438288601374403660624537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584384801832538214166049 438288601374403660624537)
                      ·
                        rfl

theorem cell23_853564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_853564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853564 prefixEnd_853564 := by exact prefixLift 853564
  have htrace : WordTrace (prefixWord ++ tailWord_853564) baseStart_853564 baseEnd_853564 := by
    simpa [prefixWord, tailWord_853564, baseEnd_853564] using wordTrace_append hprefix tailTrace_853564
  have hstable : (prefixWord ++ tailWord_853564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853564).length < 2 ^ (prefixWord ++ tailWord_853564).sum := by decide
  have hdescent : baseEnd_853564 < baseStart_853564 := by decide
  rcases family_descends (prefixWord ++ tailWord_853564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853580 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_853580 : Nat := 118140960795 + 853580 * 2 ^ 59
def prefixEnd_853580 : Nat := 4983230072969 + 3 ^ 40 * 853580 * 2
def baseEnd_853580 : Nat := 438296817064875598024463

theorem tailTrace_853580 : CollatzResearch.WordTrace tailWord_853580 prefixEnd_853580 438296817064875598024463 := by
  unfold tailWord_853580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566310123816457351491097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20755080165088609801988129 15566310123816457351491097)
  ·
    refine ⟨11674732592862343013618323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15566310123816457351491097 11674732592862343013618323)
    ·
      refine ⟨17512098889293514520427485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11674732592862343013618323 17512098889293514520427485)
      ·
        refine ⟨6567037083485067945160307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17512098889293514520427485 6567037083485067945160307)
        ·
          refine ⟨9850555625227601917740461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567037083485067945160307 9850555625227601917740461)
          ·
            refine ⟨3693958359460350719152673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9850555625227601917740461 3693958359460350719152673)
            ·
              refine ⟨2770468769595263039364505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693958359460350719152673 2770468769595263039364505)
              ·
                refine ⟨2077851577196447279523379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770468769595263039364505 2077851577196447279523379)
                ·
                  refine ⟨3116777365794670919285069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077851577196447279523379 3116777365794670919285069)
                  ·
                    refine ⟨1168791512173001594731901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116777365794670919285069 1168791512173001594731901)
                    ·
                      refine ⟨438296817064875598024463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168791512173001594731901 438296817064875598024463)
                      ·
                        rfl

theorem cell23_853580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_853580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853580 prefixEnd_853580 := by exact prefixLift 853580
  have htrace : WordTrace (prefixWord ++ tailWord_853580) baseStart_853580 baseEnd_853580 := by
    simpa [prefixWord, tailWord_853580, baseEnd_853580] using wordTrace_append hprefix tailTrace_853580
  have hstable : (prefixWord ++ tailWord_853580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853580).length < 2 ^ (prefixWord ++ tailWord_853580).sum := by decide
  have hdescent : baseEnd_853580 < baseStart_853580 := by decide
  rcases family_descends (prefixWord ++ tailWord_853580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853581 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_853581 : Nat := 118140960795 + 853581 * 2 ^ 59
def prefixEnd_853581 : Nat := 4983230072969 + 3 ^ 40 * 853581 * 2
def baseEnd_853581 : Nat := 438297330545530094111959

theorem tailTrace_853581 : CollatzResearch.WordTrace tailWord_853581 prefixEnd_853581 438297330545530094111959 := by
  unfold tailWord_853581
  simp only [CollatzResearch.WordTrace]
  refine ⟨31132656720629291873768597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20755104480419527915845731 31132656720629291873768597)
  ·
    refine ⟨1459343283779498056582903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31132656720629291873768597 1459343283779498056582903)
    ·
      refine ⟨2189014925669247084874355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459343283779498056582903 2189014925669247084874355)
      ·
        refine ⟨3283522388503870627311533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189014925669247084874355 3283522388503870627311533)
        ·
          refine ⟨1231320895688951485241825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3283522388503870627311533 1231320895688951485241825)
          ·
            refine ⟨923490671766713613931369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231320895688951485241825 923490671766713613931369)
            ·
              refine ⟨692618003825035210448527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923490671766713613931369 692618003825035210448527)
              ·
                refine ⟨1038927005737552815672791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692618003825035210448527 1038927005737552815672791)
                ·
                  refine ⟨1558390508606329223509187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038927005737552815672791 1558390508606329223509187)
                  ·
                    refine ⟨2337585762909493835263781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558390508606329223509187 2337585762909493835263781)
                    ·
                      refine ⟨438297330545530094111959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2337585762909493835263781 438297330545530094111959)
                      ·
                        rfl

theorem cell23_853581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_853581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853581 prefixEnd_853581 := by exact prefixLift 853581
  have htrace : WordTrace (prefixWord ++ tailWord_853581) baseStart_853581 baseEnd_853581 := by
    simpa [prefixWord, tailWord_853581, baseEnd_853581] using wordTrace_append hprefix tailTrace_853581
  have hstable : (prefixWord ++ tailWord_853581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853581).length < 2 ^ (prefixWord ++ tailWord_853581).sum := by decide
  have hdescent : baseEnd_853581 < baseStart_853581 := by decide
  rcases family_descends (prefixWord ++ tailWord_853581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853614 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_853614 : Nat := 118140960795 + 853614 * 2 ^ 59
def prefixEnd_853614 : Nat := 4983230072969 + 3 ^ 40 * 853614 * 2
def baseEnd_853614 : Nat := 438314275407128464999307

theorem tailTrace_853614 : CollatzResearch.WordTrace tailWord_853614 prefixEnd_853614 438314275407128464999307 := by
  unfold tailWord_853614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891732541188717313714987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20755906886339825673146597 3891732541188717313714987)
  ·
    refine ⟨5837598811783075970572481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3891732541188717313714987 5837598811783075970572481)
    ·
      refine ⟨4378199108837306977929361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5837598811783075970572481 4378199108837306977929361)
      ·
        refine ⟨3283649331627980233447021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378199108837306977929361 3283649331627980233447021)
        ·
          refine ⟨1231368499360492587542633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3283649331627980233447021 1231368499360492587542633)
          ·
            refine ⟨923526374520369440656975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231368499360492587542633 923526374520369440656975)
            ·
              refine ⟨1385289561780554160985463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923526374520369440656975 1385289561780554160985463)
              ·
                refine ⟨2077934342670831241478195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385289561780554160985463 2077934342670831241478195)
                ·
                  refine ⟨3116901514006246862217293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077934342670831241478195 3116901514006246862217293)
                  ·
                    refine ⟨1168838067752342573331485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116901514006246862217293 1168838067752342573331485)
                    ·
                      refine ⟨438314275407128464999307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1168838067752342573331485 438314275407128464999307)
                      ·
                        rfl

theorem cell23_853614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_853614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853614 prefixEnd_853614 := by exact prefixLift 853614
  have htrace : WordTrace (prefixWord ++ tailWord_853614) baseStart_853614 baseEnd_853614 := by
    simpa [prefixWord, tailWord_853614, baseEnd_853614] using wordTrace_append hprefix tailTrace_853614
  have hstable : (prefixWord ++ tailWord_853614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853614).length < 2 ^ (prefixWord ++ tailWord_853614).sum := by decide
  have hdescent : baseEnd_853614 < baseStart_853614 := by decide
  rcases family_descends (prefixWord ++ tailWord_853614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853623 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_853623 : Nat := 118140960795 + 853623 * 2 ^ 59
def prefixEnd_853623 : Nat := 4983230072969 + 3 ^ 40 * 853623 * 2
def baseEnd_853623 : Nat := 438318896733018929786765

theorem tailTrace_853623 : CollatzResearch.WordTrace tailWord_853623 prefixEnd_853623 438318896733018929786765 := by
  unfold tailWord_853623
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134188586477133046797523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756125724318088697865015 31134188586477133046797523)
  ·
    refine ⟨46701282879715699570196285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31134188586477133046797523 46701282879715699570196285)
    ·
      refine ⟨17512981079893387338823607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46701282879715699570196285 17512981079893387338823607)
      ·
        refine ⟨26269471619840081008235411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17512981079893387338823607 26269471619840081008235411)
        ·
          refine ⟨39404207429760121512353117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26269471619840081008235411 39404207429760121512353117)
          ·
            refine ⟨14776577786160045567132419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39404207429760121512353117 14776577786160045567132419)
            ·
              refine ⟨22164866679240068350698629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14776577786160045567132419 22164866679240068350698629)
              ·
                refine ⟨4155912502357512815755993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22164866679240068350698629 4155912502357512815755993)
                ·
                  refine ⟨3116934376768134611816995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4155912502357512815755993 3116934376768134611816995)
                  ·
                    refine ⟨4675401565152201917725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116934376768134611816995 4675401565152201917725493)
                    ·
                      refine ⟨438318896733018929786765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4675401565152201917725493 438318896733018929786765)
                      ·
                        rfl

theorem cell23_853623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_853623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853623 prefixEnd_853623 := by exact prefixLift 853623
  have htrace : WordTrace (prefixWord ++ tailWord_853623) baseStart_853623 baseEnd_853623 := by
    simpa [prefixWord, tailWord_853623, baseEnd_853623] using wordTrace_append hprefix tailTrace_853623
  have hstable : (prefixWord ++ tailWord_853623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853623).length < 2 ^ (prefixWord ++ tailWord_853623).sum := by decide
  have hdescent : baseEnd_853623 < baseStart_853623 := by decide
  rcases family_descends (prefixWord ++ tailWord_853623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853637 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_853637 : Nat := 118140960795 + 853637 * 2 ^ 59
def prefixEnd_853637 : Nat := 4983230072969 + 3 ^ 40 * 853637 * 2
def baseEnd_853637 : Nat := 438326085462181875011701

theorem tailTrace_853637 : CollatzResearch.WordTrace tailWord_853637 prefixEnd_853637 438326085462181875011701 := by
  unfold tailWord_853637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134699208426413437807165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756466138950942291871443 31134699208426413437807165)
  ·
    refine ⟨11675512203159905039177687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31134699208426413437807165 11675512203159905039177687)
    ·
      refine ⟨17513268304739857558766531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675512203159905039177687 17513268304739857558766531)
      ·
        refine ⟨26269902457109786338149797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513268304739857558766531 26269902457109786338149797)
        ·
          refine ⟨4925606710708084938403087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26269902457109786338149797 4925606710708084938403087)
          ·
            refine ⟨7388410066062127407604631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925606710708084938403087 7388410066062127407604631)
            ·
              refine ⟨11082615099093191111406947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388410066062127407604631 11082615099093191111406947)
              ·
                refine ⟨16623922648639786667110421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082615099093191111406947 16623922648639786667110421)
                ·
                  refine ⟨779246374154990000020801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16623922648639786667110421 779246374154990000020801)
                  ·
                    refine ⟨584434780616242500015601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 779246374154990000020801 584434780616242500015601)
                    ·
                      refine ⟨438326085462181875011701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584434780616242500015601 438326085462181875011701)
                      ·
                        rfl

theorem cell23_853637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_853637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853637 prefixEnd_853637 := by exact prefixLift 853637
  have htrace : WordTrace (prefixWord ++ tailWord_853637) baseStart_853637 baseEnd_853637 := by
    simpa [prefixWord, tailWord_853637, baseEnd_853637] using wordTrace_append hprefix tailTrace_853637
  have hstable : (prefixWord ++ tailWord_853637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853637).length < 2 ^ (prefixWord ++ tailWord_853637).sum := by decide
  have hdescent : baseEnd_853637 < baseStart_853637 := by decide
  rcases family_descends (prefixWord ++ tailWord_853637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853683 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_853683 : Nat := 118140960795 + 853683 * 2 ^ 59
def prefixEnd_853683 : Nat := 4983230072969 + 3 ^ 40 * 853683 * 2
def baseEnd_853683 : Nat := 438349705572288695036489

theorem tailTrace_853683 : CollatzResearch.WordTrace tailWord_853683 prefixEnd_853683 438349705572288695036489 := by
  unfold tailWord_853683
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136376966259763293981703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20757584644173175529321135 31136376966259763293981703)
  ·
    refine ⟨46704565449389644940972555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31136376966259763293981703 46704565449389644940972555)
    ·
      refine ⟨70056848174084467411458833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46704565449389644940972555 70056848174084467411458833)
      ·
        refine ⟨52542636130563350558594125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70056848174084467411458833 52542636130563350558594125)
        ·
          refine ⟨19703488548961256459472797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52542636130563350558594125 19703488548961256459472797)
          ·
            refine ⟨7388808205860471172302299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19703488548961256459472797 7388808205860471172302299)
            ·
              refine ⟨11083212308790706758453449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388808205860471172302299 11083212308790706758453449)
              ·
                refine ⟨8312409231593030068840087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11083212308790706758453449 8312409231593030068840087)
                ·
                  refine ⟨12468613847389545103260131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312409231593030068840087 12468613847389545103260131)
                  ·
                    refine ⟨18702920771084317654890197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12468613847389545103260131 18702920771084317654890197)
                    ·
                      refine ⟨438349705572288695036489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18702920771084317654890197 438349705572288695036489)
                      ·
                        rfl

theorem cell23_853683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_853683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853683 prefixEnd_853683 := by exact prefixLift 853683
  have htrace : WordTrace (prefixWord ++ tailWord_853683) baseStart_853683 baseEnd_853683 := by
    simpa [prefixWord, tailWord_853683, baseEnd_853683] using wordTrace_append hprefix tailTrace_853683
  have hstable : (prefixWord ++ tailWord_853683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853683).length < 2 ^ (prefixWord ++ tailWord_853683).sum := by decide
  have hdescent : baseEnd_853683 < baseStart_853683 := by decide
  rcases family_descends (prefixWord ++ tailWord_853683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853690 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_853690 : Nat := 118140960795 + 853690 * 2 ^ 59
def prefixEnd_853690 : Nat := 4983230072969 + 3 ^ 40 * 853690 * 2
def baseEnd_853690 : Nat := 146117766645623389216319

theorem tailTrace_853690 : CollatzResearch.WordTrace tailWord_853690 prefixEnd_853690 146117766645623389216319 := by
  unfold tailWord_853690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784158069308600872371631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20757754851489602326324349 7784158069308600872371631)
  ·
    refine ⟨11676237103962901308557447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784158069308600872371631 11676237103962901308557447)
    ·
      refine ⟨17514355655944351962836171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676237103962901308557447 17514355655944351962836171)
      ·
        refine ⟨26271533483916527944254257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514355655944351962836171 26271533483916527944254257)
        ·
          refine ⟨19703650112937395958190693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26271533483916527944254257 19703650112937395958190693)
          ·
            refine ⟨3694434396175761742160755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19703650112937395958190693 3694434396175761742160755)
            ·
              refine ⟨5541651594263642613241133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694434396175761742160755 5541651594263642613241133)
              ·
                refine ⟨2078119347848865979965425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541651594263642613241133 2078119347848865979965425)
                ·
                  refine ⟨1558589510886649484974069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078119347848865979965425 1558589510886649484974069)
                  ·
                    refine ⟨146117766645623389216319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1558589510886649484974069 146117766645623389216319)
                    ·
                      rfl

theorem cell23_853690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_853690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853690 prefixEnd_853690 := by exact prefixLift 853690
  have htrace : WordTrace (prefixWord ++ tailWord_853690) baseStart_853690 baseEnd_853690 := by
    simpa [prefixWord, tailWord_853690, baseEnd_853690] using wordTrace_append hprefix tailTrace_853690
  have hstable : (prefixWord ++ tailWord_853690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853690).length < 2 ^ (prefixWord ++ tailWord_853690).sum := by decide
  have hdescent : baseEnd_853690 < baseStart_853690 := by decide
  rcases family_descends (prefixWord ++ tailWord_853690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853700 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_853700 : Nat := 118140960795 + 853700 * 2 ^ 59
def prefixEnd_853700 : Nat := 4983230072969 + 3 ^ 40 * 853700 * 2
def baseEnd_853700 : Nat := 438358434743415128523911

theorem tailTrace_853700 : CollatzResearch.WordTrace tailWord_853700 prefixEnd_853700 438358434743415128523911 := by
  unfold tailWord_853700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568498503599087598675277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20757998004798783464900369 15568498503599087598675277)
  ·
    refine ⟨5838186938849657849503229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15568498503599087598675277 5838186938849657849503229)
    ·
      refine ⟨2189320102068621693563711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5838186938849657849503229 2189320102068621693563711)
      ·
        refine ⟨3283980153102932540345567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189320102068621693563711 3283980153102932540345567)
        ·
          refine ⟨4925970229654398810518351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283980153102932540345567 4925970229654398810518351)
          ·
            refine ⟨7388955344481598215777527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925970229654398810518351 7388955344481598215777527)
            ·
              refine ⟨11083433016722397323666291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388955344481598215777527 11083433016722397323666291)
              ·
                refine ⟨16625149525083595985499437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083433016722397323666291 16625149525083595985499437)
                ·
                  refine ⟨6234431071906348494562289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16625149525083595985499437 6234431071906348494562289)
                  ·
                    refine ⟨4675823303929761370921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234431071906348494562289 4675823303929761370921717)
                    ·
                      refine ⟨438358434743415128523911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4675823303929761370921717 438358434743415128523911)
                      ·
                        rfl

theorem cell23_853700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_853700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853700 prefixEnd_853700 := by exact prefixLift 853700
  have htrace : WordTrace (prefixWord ++ tailWord_853700) baseStart_853700 baseEnd_853700 := by
    simpa [prefixWord, tailWord_853700, baseEnd_853700] using wordTrace_append hprefix tailTrace_853700
  have hstable : (prefixWord ++ tailWord_853700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853700).length < 2 ^ (prefixWord ++ tailWord_853700).sum := by decide
  have hdescent : baseEnd_853700 < baseStart_853700 := by decide
  rcases family_descends (prefixWord ++ tailWord_853700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853727 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 2, 4, 2]
def baseStart_853727 : Nat := 118140960795 + 853727 * 2 ^ 59
def prefixEnd_853727 : Nat := 4983230072969 + 3 ^ 40 * 853727 * 2
def baseEnd_853727 : Nat := 438372298721086522886287

theorem tailTrace_853727 : CollatzResearch.WordTrace tailWord_853727 prefixEnd_853727 438372298721086522886287 := by
  unfold tailWord_853727
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137981778100358808583435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20758654518733572539055623 31137981778100358808583435)
  ·
    refine ⟨46706972667150538212875153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137981778100358808583435 46706972667150538212875153)
    ·
      refine ⟨35030229500362903659656365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46706972667150538212875153 35030229500362903659656365)
      ·
        refine ⟨13136336062636088872371137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35030229500362903659656365 13136336062636088872371137)
        ·
          refine ⟨9852252046977066654278353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13136336062636088872371137 9852252046977066654278353)
          ·
            refine ⟨7389189035232799990708765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9852252046977066654278353 7389189035232799990708765)
            ·
              refine ⟨2770945888212299996515787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7389189035232799990708765 2770945888212299996515787)
              ·
                refine ⟨4156418832318449994773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770945888212299996515787 4156418832318449994773681)
                ·
                  refine ⟨3117314124238837496080261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156418832318449994773681 3117314124238837496080261)
                  ·
                    refine ⟨584496398294782030515049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117314124238837496080261 584496398294782030515049)
                    ·
                      refine ⟨438372298721086522886287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584496398294782030515049 438372298721086522886287)
                      ·
                        rfl

theorem cell23_853727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_853727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853727 prefixEnd_853727 := by exact prefixLift 853727
  have htrace : WordTrace (prefixWord ++ tailWord_853727) baseStart_853727 baseEnd_853727 := by
    simpa [prefixWord, tailWord_853727, baseEnd_853727] using wordTrace_append hprefix tailTrace_853727
  have hstable : (prefixWord ++ tailWord_853727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853727).length < 2 ^ (prefixWord ++ tailWord_853727).sum := by decide
  have hdescent : baseEnd_853727 < baseStart_853727 := by decide
  rcases family_descends (prefixWord ++ tailWord_853727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853747 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3]
def baseStart_853747 : Nat := 118140960795 + 853747 * 2 ^ 59
def prefixEnd_853747 : Nat := 4983230072969 + 3 ^ 40 * 853747 * 2
def baseEnd_853747 : Nat := 438382568334176444636195

theorem tailTrace_853747 : CollatzResearch.WordTrace tailWord_853747 prefixEnd_853747 438382568334176444636195 := by
  unfold tailWord_853747
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138711238027902224311495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20759140825351934816207663 31138711238027902224311495)
  ·
    refine ⟨46708066857041853336467243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31138711238027902224311495 46708066857041853336467243)
    ·
      refine ⟨70062100285562780004700865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46708066857041853336467243 70062100285562780004700865)
      ·
        refine ⟨52546575214172085003525649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70062100285562780004700865 52546575214172085003525649)
        ·
          refine ⟨39409931410629063752644237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52546575214172085003525649 39409931410629063752644237)
          ·
            refine ⟨14778724278985898907241589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39409931410629063752644237 14778724278985898907241589)
            ·
              refine ⟨1385505401154928022553899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14778724278985898907241589 1385505401154928022553899)
              ·
                refine ⟨2078258101732392033830849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385505401154928022553899 2078258101732392033830849)
                ·
                  refine ⟨1558693576299294025373137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078258101732392033830849 1558693576299294025373137)
                  ·
                    refine ⟨1169020182224470519029853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558693576299294025373137 1169020182224470519029853)
                    ·
                      refine ⟨438382568334176444636195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169020182224470519029853 438382568334176444636195)
                      ·
                        rfl

theorem cell23_853747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_853747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853747 prefixEnd_853747 := by exact prefixLift 853747
  have htrace : WordTrace (prefixWord ++ tailWord_853747) baseStart_853747 baseEnd_853747 := by
    simpa [prefixWord, tailWord_853747, baseEnd_853747] using wordTrace_append hprefix tailTrace_853747
  have hstable : (prefixWord ++ tailWord_853747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853747).length < 2 ^ (prefixWord ++ tailWord_853747).sum := by decide
  have hdescent : baseEnd_853747 < baseStart_853747 := by decide
  rcases family_descends (prefixWord ++ tailWord_853747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853767 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 8]
def baseStart_853767 : Nat := 118140960795 + 853767 * 2 ^ 59
def prefixEnd_853767 : Nat := 4983230072969 + 3 ^ 40 * 853767 * 2
def baseEnd_853767 : Nat := 48710315327474040709567

theorem tailTrace_853767 : CollatzResearch.WordTrace tailWord_853767 prefixEnd_853767 48710315327474040709567 := by
  unfold tailWord_853767
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139440697955445640039555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20759627131970297093359703 31139440697955445640039555)
  ·
    refine ⟨46709161046933168460059333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31139440697955445640039555 46709161046933168460059333)
    ·
      refine ⟨8757967696299969086261125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46709161046933168460059333 8757967696299969086261125)
      ·
        refine ⟨1642118943056244203673961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8757967696299969086261125 1642118943056244203673961)
        ·
          refine ⟨1231589207292183152755471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642118943056244203673961 1231589207292183152755471)
          ·
            refine ⟨1847383810938274729133207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231589207292183152755471 1847383810938274729133207)
            ·
              refine ⟨2771075716407412093699811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847383810938274729133207 2771075716407412093699811)
              ·
                refine ⟨4156613574611118140549717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771075716407412093699811 4156613574611118140549717)
                ·
                  refine ⟨48710315327474040709567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4156613574611118140549717 48710315327474040709567)
                  ·
                    rfl

theorem cell23_853767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 8].length) (baseStart_853767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853767 prefixEnd_853767 := by exact prefixLift 853767
  have htrace : WordTrace (prefixWord ++ tailWord_853767) baseStart_853767 baseEnd_853767 := by
    simpa [prefixWord, tailWord_853767, baseEnd_853767] using wordTrace_append hprefix tailTrace_853767
  have hstable : (prefixWord ++ tailWord_853767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853767).length < 2 ^ (prefixWord ++ tailWord_853767).sum := by decide
  have hdescent : baseEnd_853767 < baseStart_853767 := by decide
  rcases family_descends (prefixWord ++ tailWord_853767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853770 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_853770 : Nat := 118140960795 + 853770 * 2 ^ 59
def prefixEnd_853770 : Nat := 4983230072969 + 3 ^ 40 * 853770 * 2
def baseEnd_853770 : Nat := 438394378389229854648589

theorem tailTrace_853770 : CollatzResearch.WordTrace tailWord_853770 prefixEnd_853770 438394378389229854648589 := by
  unfold tailWord_853770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784887529236144288099691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20759700077963051434932509 7784887529236144288099691)
  ·
    refine ⟨11677331293854216432149537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784887529236144288099691 11677331293854216432149537)
    ·
      refine ⟨8757998470390662324112153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11677331293854216432149537 8757998470390662324112153)
      ·
        refine ⟨6568498852792996743084115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757998470390662324112153 6568498852792996743084115)
        ·
          refine ⟨9852748279189495114626173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568498852792996743084115 9852748279189495114626173)
          ·
            refine ⟨3694780604696060667984815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9852748279189495114626173 3694780604696060667984815)
            ·
              refine ⟨5542170907044091001977223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694780604696060667984815 5542170907044091001977223)
              ·
                refine ⟨8313256360566136502965835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542170907044091001977223 8313256360566136502965835)
                ·
                  refine ⟨12469884540849204754448753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313256360566136502965835 12469884540849204754448753)
                  ·
                    refine ⟨9352413405636903565836565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12469884540849204754448753 9352413405636903565836565)
                    ·
                      refine ⟨438394378389229854648589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9352413405636903565836565 438394378389229854648589)
                      ·
                        rfl

theorem cell23_853770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_853770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853770 prefixEnd_853770 := by exact prefixLift 853770
  have htrace : WordTrace (prefixWord ++ tailWord_853770) baseStart_853770 baseEnd_853770 := by
    simpa [prefixWord, tailWord_853770, baseEnd_853770] using wordTrace_append hprefix tailTrace_853770
  have hstable : (prefixWord ++ tailWord_853770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853770).length < 2 ^ (prefixWord ++ tailWord_853770).sum := by decide
  have hdescent : baseEnd_853770 < baseStart_853770 := by decide
  rcases family_descends (prefixWord ++ tailWord_853770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853787 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 4, 3, 2]
def baseStart_853787 : Nat := 118140960795 + 853787 * 2 ^ 59
def prefixEnd_853787 : Nat := 4983230072969 + 3 ^ 40 * 853787 * 2
def baseEnd_853787 : Nat := 438403107560356288136011

theorem tailTrace_853787 : CollatzResearch.WordTrace tailWord_853787 prefixEnd_853787 438403107560356288136011 := by
  unfold tailWord_853787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31140170157882989055767615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20760113438588659370511743 31140170157882989055767615)
  ·
    refine ⟨46710255236824483583651423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31140170157882989055767615 46710255236824483583651423)
    ·
      refine ⟨70065382855236725375477135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46710255236824483583651423 70065382855236725375477135)
      ·
        refine ⟨105098074282855088063215703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70065382855236725375477135 105098074282855088063215703)
        ·
          refine ⟨157647111424282632094823555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105098074282855088063215703 157647111424282632094823555)
          ·
            refine ⟨236470667136423948142235333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157647111424282632094823555 236470667136423948142235333)
            ·
              refine ⟨44338250088079490276669125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236470667136423948142235333 44338250088079490276669125)
              ·
                refine ⟨8313421891514904426875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44338250088079490276669125 8313421891514904426875461)
                ·
                  refine ⟨1558766604659044580039149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8313421891514904426875461 1558766604659044580039149)
                  ·
                    refine ⟨584537476747141717514681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558766604659044580039149 584537476747141717514681)
                    ·
                      refine ⟨438403107560356288136011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584537476747141717514681 438403107560356288136011)
                      ·
                        rfl

theorem cell23_853787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3, 2].length) (baseStart_853787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853787 prefixEnd_853787 := by exact prefixLift 853787
  have htrace : WordTrace (prefixWord ++ tailWord_853787) baseStart_853787 baseEnd_853787 := by
    simpa [prefixWord, tailWord_853787, baseEnd_853787] using wordTrace_append hprefix tailTrace_853787
  have hstable : (prefixWord ++ tailWord_853787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853787).length < 2 ^ (prefixWord ++ tailWord_853787).sum := by decide
  have hdescent : baseEnd_853787 < baseStart_853787 := by decide
  rcases family_descends (prefixWord ++ tailWord_853787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853794 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_853794 : Nat := 118140960795 + 853794 * 2 ^ 59
def prefixEnd_853794 : Nat := 4983230072969 + 3 ^ 40 * 853794 * 2
def baseEnd_853794 : Nat := 438406701924937760748479

theorem tailTrace_853794 : CollatzResearch.WordTrace tailWord_853794 prefixEnd_853794 438406701924937760748479 := by
  unfold tailWord_853794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785106367214407312818109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20760283645905086167514957 7785106367214407312818109)
  ·
    refine ⟨2919414887705402742306791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7785106367214407312818109 2919414887705402742306791)
    ·
      refine ⟨4379122331558104113460187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919414887705402742306791 4379122331558104113460187)
      ·
        refine ⟨6568683497337156170190281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379122331558104113460187 6568683497337156170190281)
        ·
          refine ⟨4926512623002867127642711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6568683497337156170190281 4926512623002867127642711)
          ·
            refine ⟨7389768934504300691464067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926512623002867127642711 7389768934504300691464067)
            ·
              refine ⟨11084653401756451037196101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389768934504300691464067 11084653401756451037196101)
              ·
                refine ⟨2078372512829334569474269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11084653401756451037196101 2078372512829334569474269)
                ·
                  refine ⟨779389692311000463552851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2078372512829334569474269 779389692311000463552851)
                  ·
                    refine ⟨1169084538466500695329277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 779389692311000463552851 1169084538466500695329277)
                    ·
                      refine ⟨438406701924937760748479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169084538466500695329277 438406701924937760748479)
                      ·
                        rfl

theorem cell23_853794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_853794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853794 prefixEnd_853794 := by exact prefixLift 853794
  have htrace : WordTrace (prefixWord ++ tailWord_853794) baseStart_853794 baseEnd_853794 := by
    simpa [prefixWord, tailWord_853794, baseEnd_853794] using wordTrace_append hprefix tailTrace_853794
  have hstable : (prefixWord ++ tailWord_853794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853794).length < 2 ^ (prefixWord ++ tailWord_853794).sum := by decide
  have hdescent : baseEnd_853794 < baseStart_853794 := by decide
  rcases family_descends (prefixWord ++ tailWord_853794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853797 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_853797 : Nat := 118140960795 + 853797 * 2 ^ 59
def prefixEnd_853797 : Nat := 4983230072969 + 3 ^ 40 * 853797 * 2
def baseEnd_853797 : Nat := 146136080788967083003655

theorem tailTrace_853797 : CollatzResearch.WordTrace tailWord_853797 prefixEnd_853797 146136080788967083003655 := by
  unfold tailWord_853797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31140534887846760763631645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20760356591897840509087763 31140534887846760763631645)
  ·
    refine ⟨11677700582942535286361867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31140534887846760763631645 11677700582942535286361867)
    ·
      refine ⟨17516550874413802929542801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11677700582942535286361867 17516550874413802929542801)
      ·
        refine ⟨13137413155810352197157101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17516550874413802929542801 13137413155810352197157101)
        ·
          refine ⟨4926529933428882073933913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13137413155810352197157101 4926529933428882073933913)
          ·
            refine ⟨3694897450071661555450435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926529933428882073933913 3694897450071661555450435)
            ·
              refine ⟨5542346175107492333175653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694897450071661555450435 5542346175107492333175653)
              ·
                refine ⟨1039189907832654812470435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5542346175107492333175653 1039189907832654812470435)
                ·
                  refine ⟨1558784861748982218705653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039189907832654812470435 1558784861748982218705653)
                  ·
                    refine ⟨146136080788967083003655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1558784861748982218705653 146136080788967083003655)
                    ·
                      rfl

theorem cell23_853797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_853797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853797 prefixEnd_853797 := by exact prefixLift 853797
  have htrace : WordTrace (prefixWord ++ tailWord_853797) baseStart_853797 baseEnd_853797 := by
    simpa [prefixWord, tailWord_853797, baseEnd_853797] using wordTrace_append hprefix tailTrace_853797
  have hstable : (prefixWord ++ tailWord_853797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853797).length < 2 ^ (prefixWord ++ tailWord_853797).sum := by decide
  have hdescent : baseEnd_853797 < baseStart_853797 := by decide
  rcases family_descends (prefixWord ++ tailWord_853797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853821 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_853821 : Nat := 118140960795 + 853821 * 2 ^ 59
def prefixEnd_853821 : Nat := 4983230072969 + 3 ^ 40 * 853821 * 2
def baseEnd_853821 : Nat := 438420565902609155110855

theorem tailTrace_853821 : CollatzResearch.WordTrace tailWord_853821 prefixEnd_853821 438420565902609155110855 := by
  unfold tailWord_853821
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141410239759812862505317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20760940159839875241670211 31141410239759812862505317)
  ·
    refine ⟨5839014419954964911719747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31141410239759812862505317 5839014419954964911719747)
    ·
      refine ⟨8758521629932447367579621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839014419954964911719747 8758521629932447367579621)
      ·
        refine ⟨1642222805612333881421179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8758521629932447367579621 1642222805612333881421179)
        ·
          refine ⟨2463334208418500822131769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642222805612333881421179 2463334208418500822131769)
          ·
            refine ⟨1847500656313875616598827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463334208418500822131769 1847500656313875616598827)
            ·
              refine ⟨2771250984470813424898241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847500656313875616598827 2771250984470813424898241)
              ·
                refine ⟨2078438238353110068673681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771250984470813424898241 2078438238353110068673681)
                ·
                  refine ⟨1558828678764832551505261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078438238353110068673681 1558828678764832551505261)
                  ·
                    refine ⟨584560754536812206814473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1558828678764832551505261 584560754536812206814473)
                    ·
                      refine ⟨438420565902609155110855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584560754536812206814473 438420565902609155110855)
                      ·
                        rfl

theorem cell23_853821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_853821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853821 prefixEnd_853821 := by exact prefixLift 853821
  have htrace : WordTrace (prefixWord ++ tailWord_853821) baseStart_853821 baseEnd_853821 := by
    simpa [prefixWord, tailWord_853821, baseEnd_853821] using wordTrace_append hprefix tailTrace_853821
  have hstable : (prefixWord ++ tailWord_853821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853821).length < 2 ^ (prefixWord ++ tailWord_853821).sum := by decide
  have hdescent : baseEnd_853821 < baseStart_853821 := by decide
  rcases family_descends (prefixWord ++ tailWord_853821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853827 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 4, 4]
def baseStart_853827 : Nat := 118140960795 + 853827 * 2 ^ 59
def prefixEnd_853827 : Nat := 4983230072969 + 3 ^ 40 * 853827 * 2
def baseEnd_853827 : Nat := 146141215595512043878609

theorem tailTrace_853827 : CollatzResearch.WordTrace tailWord_853827 prefixEnd_853827 146141215595512043878609 := by
  unfold tailWord_853827
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141629077738075887223735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20761086051825383924815823 31141629077738075887223735)
  ·
    refine ⟨46712443616607113830835603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31141629077738075887223735 46712443616607113830835603)
    ·
      refine ⟨70068665424910670746253405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46712443616607113830835603 70068665424910670746253405)
      ·
        refine ⟨26275749534341501529845027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70068665424910670746253405 26275749534341501529845027)
        ·
          refine ⟨39413624301512252294767541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26275749534341501529845027 39413624301512252294767541)
          ·
            refine ⟨3695027278266773652634457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39413624301512252294767541 3695027278266773652634457)
            ·
              refine ⟨2771270458700080239475843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3695027278266773652634457 2771270458700080239475843)
              ·
                refine ⟨4156905688050120359213765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771270458700080239475843 4156905688050120359213765)
                ·
                  refine ⟨779419816509397567352581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4156905688050120359213765 779419816509397567352581)
                  ·
                    refine ⟨146141215595512043878609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779419816509397567352581 146141215595512043878609)
                    ·
                      rfl

theorem cell23_853827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 4].length) (baseStart_853827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853827 prefixEnd_853827 := by exact prefixLift 853827
  have htrace : WordTrace (prefixWord ++ tailWord_853827) baseStart_853827 baseEnd_853827 := by
    simpa [prefixWord, tailWord_853827, baseEnd_853827] using wordTrace_append hprefix tailTrace_853827
  have hstable : (prefixWord ++ tailWord_853827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853827).length < 2 ^ (prefixWord ++ tailWord_853827).sum := by decide
  have hdescent : baseEnd_853827 < baseStart_853827 := by decide
  rcases family_descends (prefixWord ++ tailWord_853827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853878 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_853878 : Nat := 118140960795 + 853878 * 2 ^ 59
def prefixEnd_853878 : Nat := 4983230072969 + 3 ^ 40 * 853878 * 2
def baseEnd_853878 : Nat := 146149944766638477366031

theorem tailTrace_853878 : CollatzResearch.WordTrace tailWord_853878 prefixEnd_853878 146149944766638477366031 := by
  unfold tailWord_853878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946468075034581974833143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20762326133702207731553525 1946468075034581974833143)
  ·
    refine ⟨2919702112551872962249715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946468075034581974833143 2919702112551872962249715)
    ·
      refine ⟨4379553168827809443374573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919702112551872962249715 4379553168827809443374573)
      ·
        refine ⟨1642332438310428541265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4379553168827809443374573 1642332438310428541265465)
        ·
          refine ⟨1231749328732821405949099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642332438310428541265465 1231749328732821405949099)
          ·
            refine ⟨1847623993099232108923649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231749328732821405949099 1847623993099232108923649)
            ·
              refine ⟨1385717994824424081692737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847623993099232108923649 1385717994824424081692737)
              ·
                refine ⟨1039288496118318061269553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385717994824424081692737 1039288496118318061269553)
                ·
                  refine ⟨779466372088738545952165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039288496118318061269553 779466372088738545952165)
                  ·
                    refine ⟨146149944766638477366031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779466372088738545952165 146149944766638477366031)
                    ·
                      rfl

theorem cell23_853878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_853878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853878 prefixEnd_853878 := by exact prefixLift 853878
  have htrace : WordTrace (prefixWord ++ tailWord_853878) baseStart_853878 baseEnd_853878 := by
    simpa [prefixWord, tailWord_853878, baseEnd_853878] using wordTrace_append hprefix tailTrace_853878
  have hstable : (prefixWord ++ tailWord_853878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853878).length < 2 ^ (prefixWord ++ tailWord_853878).sum := by decide
  have hdescent : baseEnd_853878 < baseStart_853878 := by decide
  rcases family_descends (prefixWord ++ tailWord_853878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853880 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_853880 : Nat := 118140960795 + 853880 * 2 ^ 59
def prefixEnd_853880 : Nat := 4983230072969 + 3 ^ 40 * 853880 * 2
def baseEnd_853880 : Nat := 438450861261224424273083

theorem tailTrace_853880 : CollatzResearch.WordTrace tailWord_853880 prefixEnd_853880 438450861261224424273083 := by
  unfold tailWord_853880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571781073273032969451547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20762374764364043959268729 15571781073273032969451547)
  ·
    refine ⟨23357671609909549454177321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15571781073273032969451547 23357671609909549454177321)
    ·
      refine ⟨17518253707432162090632991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23357671609909549454177321 17518253707432162090632991)
      ·
        refine ⟨26277380561148243135949487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17518253707432162090632991 26277380561148243135949487)
        ·
          refine ⟨39416070841722364703924231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26277380561148243135949487 39416070841722364703924231)
          ·
            refine ⟨59124106262583547055886347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39416070841722364703924231 59124106262583547055886347)
            ·
              refine ⟨88686159393875320583829521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59124106262583547055886347 88686159393875320583829521)
              ·
                refine ⟨66514619545406490437872141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88686159393875320583829521 66514619545406490437872141)
                ·
                  refine ⟨24942982329527433914202053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66514619545406490437872141 24942982329527433914202053)
                  ·
                    refine ⟨4676809186786393858912885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24942982329527433914202053 4676809186786393858912885)
                    ·
                      refine ⟨438450861261224424273083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4676809186786393858912885 438450861261224424273083)
                      ·
                        rfl

theorem cell23_853880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_853880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853880 prefixEnd_853880 := by exact prefixLift 853880
  have htrace : WordTrace (prefixWord ++ tailWord_853880) baseStart_853880 baseEnd_853880 := by
    simpa [prefixWord, tailWord_853880, baseEnd_853880] using wordTrace_append hprefix tailTrace_853880
  have hstable : (prefixWord ++ tailWord_853880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853880).length < 2 ^ (prefixWord ++ tailWord_853880).sum := by decide
  have hdescent : baseEnd_853880 < baseStart_853880 := by decide
  rcases family_descends (prefixWord ++ tailWord_853880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853957 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_853957 : Nat := 118140960795 + 853957 * 2 ^ 59
def prefixEnd_853957 : Nat := 4983230072969 + 3 ^ 40 * 853957 * 2
def baseEnd_853957 : Nat := 438490399271620623010229

theorem tailTrace_853957 : CollatzResearch.WordTrace tailWord_853957 prefixEnd_853957 438490399271620623010229 := by
  unfold tailWord_853957
  simp only [CollatzResearch.WordTrace]
  refine ⟨31146370567267108089456125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20764247044844738726304083 31146370567267108089456125)
  ·
    refine ⟨11679888962725165533546047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31146370567267108089456125 11679888962725165533546047)
    ·
      refine ⟨17519833444087748300319071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11679888962725165533546047 17519833444087748300319071)
      ·
        refine ⟨26279750166131622450478607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519833444087748300319071 26279750166131622450478607)
        ·
          refine ⟨39419625249197433675717911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279750166131622450478607 39419625249197433675717911)
          ·
            refine ⟨59129437873796150513576867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39419625249197433675717911 59129437873796150513576867)
            ·
              refine ⟨88694156810694225770365301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59129437873796150513576867 88694156810694225770365301)
              ·
                refine ⟨8315077201002583665971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88694156810694225770365301 8315077201002583665971747)
                ·
                  refine ⟨12472615801503875498957621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315077201002583665971747 12472615801503875498957621)
                  ·
                    refine ⟨1169307731390988328027277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12472615801503875498957621 1169307731390988328027277)
                    ·
                      refine ⟨438490399271620623010229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169307731390988328027277 438490399271620623010229)
                      ·
                        rfl

theorem cell23_853957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_853957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853957 prefixEnd_853957 := by exact prefixLift 853957
  have htrace : WordTrace (prefixWord ++ tailWord_853957) baseStart_853957 baseEnd_853957 := by
    simpa [prefixWord, tailWord_853957, baseEnd_853957] using wordTrace_append hprefix tailTrace_853957
  have hstable : (prefixWord ++ tailWord_853957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853957).length < 2 ^ (prefixWord ++ tailWord_853957).sum := by decide
  have hdescent : baseEnd_853957 < baseStart_853957 := by decide
  rcases family_descends (prefixWord ++ tailWord_853957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853994 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_853994 : Nat := 118140960795 + 853994 * 2 ^ 59
def prefixEnd_853994 : Nat := 4983230072969 + 3 ^ 40 * 853994 * 2
def baseEnd_853994 : Nat := 146169799351945659415853

theorem tailTrace_853994 : CollatzResearch.WordTrace tailWord_853994 prefixEnd_853994 146169799351945659415853 := by
  unfold tailWord_853994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786930017033265852138259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20765146712088708939035357 7786930017033265852138259)
  ·
    refine ⟨11680395025549898778207389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7786930017033265852138259 11680395025549898778207389)
    ·
      refine ⟨4380148134581212041827771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11680395025549898778207389 4380148134581212041827771)
      ·
        refine ⟨6570222201871818062741657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380148134581212041827771 6570222201871818062741657)
        ·
          refine ⟨4927666651403863547056243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6570222201871818062741657 4927666651403863547056243)
          ·
            refine ⟨7391499977105795320584365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927666651403863547056243 7391499977105795320584365)
            ·
              refine ⟨2771812491414673245219137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7391499977105795320584365 2771812491414673245219137)
              ·
                refine ⟨2078859368561004933914353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771812491414673245219137 2078859368561004933914353)
                ·
                  refine ⟨1559144526420753700435765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078859368561004933914353 1559144526420753700435765)
                  ·
                    refine ⟨146169799351945659415853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559144526420753700435765 146169799351945659415853)
                    ·
                      rfl

theorem cell23_853994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_853994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853994 prefixEnd_853994 := by exact prefixLift 853994
  have htrace : WordTrace (prefixWord ++ tailWord_853994) baseStart_853994 baseEnd_853994 := by
    simpa [prefixWord, tailWord_853994, baseEnd_853994] using wordTrace_append hprefix tailTrace_853994
  have hstable : (prefixWord ++ tailWord_853994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853994).length < 2 ^ (prefixWord ++ tailWord_853994).sum := by decide
  have hdescent : baseEnd_853994 < baseStart_853994 := by decide
  rcases family_descends (prefixWord ++ tailWord_853994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853998 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_853998 : Nat := 118140960795 + 853998 * 2 ^ 59
def prefixEnd_853998 : Nat := 4983230072969 + 3 ^ 40 * 853998 * 2
def baseEnd_853998 : Nat := 48723494664272773621949

theorem tailTrace_853998 : CollatzResearch.WordTrace tailWord_853998 prefixEnd_853998 48723494664272773621949 := by
  unfold tailWord_853998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893483245014821511462331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20765243973412381394465765 3893483245014821511462331)
  ·
    refine ⟨5840224867522232267193497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893483245014821511462331 5840224867522232267193497)
    ·
      refine ⟨4380168650641674200395123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5840224867522232267193497 4380168650641674200395123)
      ·
        refine ⟨6570252975962511300592685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380168650641674200395123 6570252975962511300592685)
        ·
          refine ⟨2463844865985941737722257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6570252975962511300592685 2463844865985941737722257)
          ·
            refine ⟨1847883649489456303291693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463844865985941737722257 1847883649489456303291693)
            ·
              refine ⟨692956368558546113734385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847883649489456303291693 692956368558546113734385)
              ·
                refine ⟨519717276418909585300789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692956368558546113734385 519717276418909585300789)
                ·
                  refine ⟨48723494664272773621949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519717276418909585300789 48723494664272773621949)
                  ·
                    rfl

theorem cell23_853998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_853998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_853998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_853998 prefixEnd_853998 := by exact prefixLift 853998
  have htrace : WordTrace (prefixWord ++ tailWord_853998) baseStart_853998 baseEnd_853998 := by
    simpa [prefixWord, tailWord_853998, baseEnd_853998] using wordTrace_append hprefix tailTrace_853998
  have hstable : (prefixWord ++ tailWord_853998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853998).length < 2 ^ (prefixWord ++ tailWord_853998).sum := by decide
  have hdescent : baseEnd_853998 < baseStart_853998 := by decide
  rcases family_descends (prefixWord ++ tailWord_853998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854024 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_854024 : Nat := 118140960795 + 854024 * 2 ^ 59
def prefixEnd_854024 : Nat := 4983230072969 + 3 ^ 40 * 854024 * 2
def baseEnd_854024 : Nat := 146174934158490620290807

theorem tailTrace_854024 : CollatzResearch.WordTrace tailWord_854024 prefixEnd_854024 146174934158490620290807 := by
  unfold tailWord_854024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15574407129012189266072563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20765876172016252354763417 15574407129012189266072563)
  ·
    refine ⟨23361610693518283899108845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15574407129012189266072563 23361610693518283899108845)
    ·
      refine ⟨8760604010069356462165817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23361610693518283899108845 8760604010069356462165817)
      ·
        refine ⟨6570453007552017346624363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8760604010069356462165817 6570453007552017346624363)
        ·
          refine ⟨9855679511328026019936545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570453007552017346624363 9855679511328026019936545)
          ·
            refine ⟨7391759633496019514952409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855679511328026019936545 7391759633496019514952409)
            ·
              refine ⟨5543819725122014636214307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391759633496019514952409 5543819725122014636214307)
              ·
                refine ⟨8315729587683021954321461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543819725122014636214307 8315729587683021954321461)
                ·
                  refine ⟨779599648845283308217637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8315729587683021954321461 779599648845283308217637)
                  ·
                    refine ⟨146174934158490620290807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779599648845283308217637 146174934158490620290807)
                    ·
                      rfl

theorem cell23_854024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_854024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854024 prefixEnd_854024 := by exact prefixLift 854024
  have htrace : WordTrace (prefixWord ++ tailWord_854024) baseStart_854024 baseEnd_854024 := by
    simpa [prefixWord, tailWord_854024, baseEnd_854024] using wordTrace_append hprefix tailTrace_854024
  have hstable : (prefixWord ++ tailWord_854024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854024).length < 2 ^ (prefixWord ++ tailWord_854024).sum := by decide
  have hdescent : baseEnd_854024 < baseStart_854024 := by decide
  rcases family_descends (prefixWord ++ tailWord_854024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854041 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 1, 4]
def baseStart_854041 : Nat := 118140960795 + 854041 * 2 ^ 59
def prefixEnd_854041 : Nat := 4983230072969 + 3 ^ 40 * 854041 * 2
def baseEnd_854041 : Nat := 146177843882199431453281

theorem tailTrace_854041 : CollatzResearch.WordTrace tailWord_854041 prefixEnd_854041 146177843882199431453281 := by
  unfold tailWord_854041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149434298962790435513977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20766289532641860290342651 31149434298962790435513977)
  ·
    refine ⟨23362075724222092826635483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31149434298962790435513977 23362075724222092826635483)
    ·
      refine ⟨35043113586333139239953225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23362075724222092826635483 35043113586333139239953225)
      ·
        refine ⟨26282335189749854429964919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35043113586333139239953225 26282335189749854429964919)
        ·
          refine ⟨39423502784624781644947379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26282335189749854429964919 39423502784624781644947379)
          ·
            refine ⟨59135254176937172467421069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39423502784624781644947379 59135254176937172467421069)
            ·
              refine ⟨22175720316351439675282901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59135254176937172467421069 22175720316351439675282901)
              ·
                refine ⟨519743444914486867389443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22175720316351439675282901 519743444914486867389443)
                ·
                  refine ⟨779615167371730301084165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519743444914486867389443 779615167371730301084165)
                  ·
                    refine ⟨146177843882199431453281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779615167371730301084165 146177843882199431453281)
                    ·
                      rfl

theorem cell23_854041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_854041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854041 prefixEnd_854041 := by exact prefixLift 854041
  have htrace : WordTrace (prefixWord ++ tailWord_854041) baseStart_854041 baseEnd_854041 := by
    simpa [prefixWord, tailWord_854041, baseEnd_854041] using wordTrace_append hprefix tailTrace_854041
  have hstable : (prefixWord ++ tailWord_854041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854041).length < 2 ^ (prefixWord ++ tailWord_854041).sum := by decide
  have hdescent : baseEnd_854041 < baseStart_854041 := by decide
  rcases family_descends (prefixWord ++ tailWord_854041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854101 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_854101 : Nat := 118140960795 + 854101 * 2 ^ 59
def prefixEnd_854101 : Nat := 4983230072969 + 3 ^ 40 * 854101 * 2
def baseEnd_854101 : Nat := 146188113495289353203189

theorem tailTrace_854101 : CollatzResearch.WordTrace tailWord_854101 prefixEnd_854101 146188113495289353203189 := by
  unfold tailWord_854101
  simp only [CollatzResearch.WordTrace]
  refine ⟨31151622678745420682698157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20767748452496947121798771 31151622678745420682698157)
  ·
    refine ⟨11681858504529532756011809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31151622678745420682698157 11681858504529532756011809)
    ·
      refine ⟨8761393878397149567008857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11681858504529532756011809 8761393878397149567008857)
      ·
        refine ⟨6571045408797862175256643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8761393878397149567008857 6571045408797862175256643)
        ·
          refine ⟨9856568113196793262884965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571045408797862175256643 9856568113196793262884965)
          ·
            refine ⟨1848106521224398736790931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9856568113196793262884965 1848106521224398736790931)
            ·
              refine ⟨2772159781836598105186397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848106521224398736790931 2772159781836598105186397)
              ·
                refine ⟨1039559918188724289444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2772159781836598105186397 1039559918188724289444899)
                ·
                  refine ⟨1559339877283086434167349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039559918188724289444899 1559339877283086434167349)
                  ·
                    refine ⟨146188113495289353203189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559339877283086434167349 146188113495289353203189)
                    ·
                      rfl

theorem cell23_854101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_854101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854101 prefixEnd_854101 := by exact prefixLift 854101
  have htrace : WordTrace (prefixWord ++ tailWord_854101) baseStart_854101 baseEnd_854101 := by
    simpa [prefixWord, tailWord_854101, baseEnd_854101] using wordTrace_append hprefix tailTrace_854101
  have hstable : (prefixWord ++ tailWord_854101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854101).length < 2 ^ (prefixWord ++ tailWord_854101).sum := by decide
  have hdescent : baseEnd_854101 < baseStart_854101 := by decide
  rcases family_descends (prefixWord ++ tailWord_854101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854124 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_854124 : Nat := 118140960795 + 854124 * 2 ^ 59
def prefixEnd_854124 : Nat := 4983230072969 + 3 ^ 40 * 854124 * 2
def baseEnd_854124 : Nat := 438576150540921469621961

theorem tailTrace_854124 : CollatzResearch.WordTrace tailWord_854124 prefixEnd_854124 438576150540921469621961 := by
  unfold tailWord_854124
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576230778831047805392713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20768307705108063740523617 15576230778831047805392713)
  ·
    refine ⟨11682173084123285854044535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15576230778831047805392713 11682173084123285854044535)
    ·
      refine ⟨17523259626184928781066803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11682173084123285854044535 17523259626184928781066803)
      ·
        refine ⟨26284889439277393171600205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17523259626184928781066803 26284889439277393171600205)
        ·
          refine ⟨9856833539729022439350077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26284889439277393171600205 9856833539729022439350077)
          ·
            refine ⟨3696312577398383414756279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9856833539729022439350077 3696312577398383414756279)
            ·
              refine ⟨5544468866097575122134419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696312577398383414756279 5544468866097575122134419)
              ·
                refine ⟨8316703299146362683201629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544468866097575122134419 8316703299146362683201629)
                ·
                  refine ⟨3118763737179886006200611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8316703299146362683201629 3118763737179886006200611)
                  ·
                    refine ⟨4678145605769829009300917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118763737179886006200611 4678145605769829009300917)
                    ·
                      refine ⟨438576150540921469621961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4678145605769829009300917 438576150540921469621961)
                      ·
                        rfl

theorem cell23_854124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_854124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854124 prefixEnd_854124 := by exact prefixLift 854124
  have htrace : WordTrace (prefixWord ++ tailWord_854124) baseStart_854124 baseEnd_854124 := by
    simpa [prefixWord, tailWord_854124, baseEnd_854124] using wordTrace_append hprefix tailTrace_854124
  have hstable : (prefixWord ++ tailWord_854124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854124).length < 2 ^ (prefixWord ++ tailWord_854124).sum := by decide
  have hdescent : baseEnd_854124 < baseStart_854124 := by decide
  rcases family_descends (prefixWord ++ tailWord_854124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854158 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_854158 : Nat := 118140960795 + 854158 * 2 ^ 59
def prefixEnd_854158 : Nat := 4983230072969 + 3 ^ 40 * 854158 * 2
def baseEnd_854158 : Nat := 438593608883174336596805

theorem tailTrace_854158 : CollatzResearch.WordTrace tailWord_854158 prefixEnd_854158 438593608883174336596805 := by
  unfold tailWord_854158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894212704942364927190391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20769134426359279611682085 3894212704942364927190391)
  ·
    refine ⟨5841319057413547390785587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894212704942364927190391 5841319057413547390785587)
    ·
      refine ⟨8761978586120321086178381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841319057413547390785587 8761978586120321086178381)
      ·
        refine ⟨3285741969795120407316893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8761978586120321086178381 3285741969795120407316893)
        ·
          refine ⟨1232153238673170152743835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3285741969795120407316893 1232153238673170152743835)
          ·
            refine ⟨1848229858009755229115753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232153238673170152743835 1848229858009755229115753)
            ·
              refine ⟨1386172393507316421836815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848229858009755229115753 1386172393507316421836815)
              ·
                refine ⟨2079258590260974632755223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386172393507316421836815 2079258590260974632755223)
                ·
                  refine ⟨3118887885391461949132835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079258590260974632755223 3118887885391461949132835)
                  ·
                    refine ⟨4678331828087192923699253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118887885391461949132835 4678331828087192923699253)
                    ·
                      refine ⟨438593608883174336596805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4678331828087192923699253 438593608883174336596805)
                      ·
                        rfl

theorem cell23_854158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_854158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854158 prefixEnd_854158 := by exact prefixLift 854158
  have htrace : WordTrace (prefixWord ++ tailWord_854158) baseStart_854158 baseEnd_854158 := by
    simpa [prefixWord, tailWord_854158, baseEnd_854158] using wordTrace_append hprefix tailTrace_854158
  have hstable : (prefixWord ++ tailWord_854158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854158).length < 2 ^ (prefixWord ++ tailWord_854158).sum := by decide
  have hdescent : baseEnd_854158 < baseStart_854158 := by decide
  rcases family_descends (prefixWord ++ tailWord_854158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 3]
def baseStart_854171 : Nat := 118140960795 + 854171 * 2 ^ 59
def prefixEnd_854171 : Nat := 4983230072969 + 3 ^ 40 * 854171 * 2
def baseEnd_854171 : Nat := 438600284131682785734245

theorem tailTrace_854171 : CollatzResearch.WordTrace tailWord_854171 prefixEnd_854171 438600284131682785734245 := by
  unfold tailWord_854171
  simp only [CollatzResearch.WordTrace]
  refine ⟨31154175788491822637746367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20769450525661215091830911 31154175788491822637746367)
  ·
    refine ⟨46731263682737733956619551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31154175788491822637746367 46731263682737733956619551)
    ·
      refine ⟨70096895524106600934929327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46731263682737733956619551 70096895524106600934929327)
      ·
        refine ⟨105145343286159901402393991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70096895524106600934929327 105145343286159901402393991)
        ·
          refine ⟨157718014929239852103590987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105145343286159901402393991 157718014929239852103590987)
          ·
            refine ⟨236577022393859778155386481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157718014929239852103590987 236577022393859778155386481)
            ·
              refine ⟨177432766795394833616539861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236577022393859778155386481 177432766795394833616539861)
              ·
                refine ⟨4158580471767066412887653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177432766795394833616539861 4158580471767066412887653)
                ·
                  refine ⟨779733838456324952416435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4158580471767066412887653 779733838456324952416435)
                  ·
                    refine ⟨1169600757684487428624653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 779733838456324952416435 1169600757684487428624653)
                    ·
                      refine ⟨438600284131682785734245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169600757684487428624653 438600284131682785734245)
                      ·
                        rfl

theorem cell23_854171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 3].length) (baseStart_854171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854171 prefixEnd_854171 := by exact prefixLift 854171
  have htrace : WordTrace (prefixWord ++ tailWord_854171) baseStart_854171 baseEnd_854171 := by
    simpa [prefixWord, tailWord_854171, baseEnd_854171] using wordTrace_append hprefix tailTrace_854171
  have hstable : (prefixWord ++ tailWord_854171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854171).length < 2 ^ (prefixWord ++ tailWord_854171).sum := by decide
  have hdescent : baseEnd_854171 < baseStart_854171 := by decide
  rcases family_descends (prefixWord ++ tailWord_854171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854224 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_854224 : Nat := 118140960795 + 854224 * 2 ^ 59
def prefixEnd_854224 : Nat := 4983230072969 + 3 ^ 40 * 854224 * 2
def baseEnd_854224 : Nat := 438627498606371078371501

theorem tailTrace_854224 : CollatzResearch.WordTrace tailWord_854224 prefixEnd_854224 438627498606371078371501 := by
  unfold tailWord_854224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578054428649906344712863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20770739238199875126283817 15578054428649906344712863)
  ·
    refine ⟨23367081642974859517069295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15578054428649906344712863 23367081642974859517069295)
    ·
      refine ⟨35050622464462289275603943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23367081642974859517069295 35050622464462289275603943)
      ·
        refine ⟨52575933696693433913405915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35050622464462289275603943 52575933696693433913405915)
        ·
          refine ⟨78863900545040150870108873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52575933696693433913405915 78863900545040150870108873)
          ·
            refine ⟨59147925408780113152581655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78863900545040150870108873 59147925408780113152581655)
            ·
              refine ⟨88721888113170169728872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59147925408780113152581655 88721888113170169728872483)
              ·
                refine ⟨133082832169755254593308725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88721888113170169728872483 133082832169755254593308725)
                ·
                  refine ⟨12476515515914555118122693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133082832169755254593308725 12476515515914555118122693)
                  ·
                    refine ⟨2339346659233979084648005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12476515515914555118122693 2339346659233979084648005)
                    ·
                      refine ⟨438627498606371078371501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2339346659233979084648005 438627498606371078371501)
                      ·
                        rfl

theorem cell23_854224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_854224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854224 prefixEnd_854224 := by exact prefixLift 854224
  have htrace : WordTrace (prefixWord ++ tailWord_854224) baseStart_854224 baseEnd_854224 := by
    simpa [prefixWord, tailWord_854224, baseEnd_854224] using wordTrace_append hprefix tailTrace_854224
  have hstable : (prefixWord ++ tailWord_854224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854224).length < 2 ^ (prefixWord ++ tailWord_854224).sum := by decide
  have hdescent : baseEnd_854224 < baseStart_854224 := by decide
  rcases family_descends (prefixWord ++ tailWord_854224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854241 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_854241 : Nat := 118140960795 + 854241 * 2 ^ 59
def prefixEnd_854241 : Nat := 4983230072969 + 3 ^ 40 * 854241 * 2
def baseEnd_854241 : Nat := 438636227777497511858923

theorem tailTrace_854241 : CollatzResearch.WordTrace tailWord_854241 prefixEnd_854241 438636227777497511858923 := by
  unfold tailWord_854241
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156728898238224592794577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20771152598825483061863051 31156728898238224592794577)
  ·
    refine ⟨23367546673678668444595933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31156728898238224592794577 23367546673678668444595933)
    ·
      refine ⟨8762830002629500666723475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23367546673678668444595933 8762830002629500666723475)
      ·
        refine ⟨13144245003944251000085213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762830002629500666723475 13144245003944251000085213)
        ·
          refine ⟨4929091876479094125031955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13144245003944251000085213 4929091876479094125031955)
          ·
            refine ⟨7393637814718641187547933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929091876479094125031955 7393637814718641187547933)
            ·
              refine ⟨2772614180519490445330475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7393637814718641187547933 2772614180519490445330475)
              ·
                refine ⟨4158921270779235667995713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772614180519490445330475 4158921270779235667995713)
                ·
                  refine ⟨3119190953084426750996785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4158921270779235667995713 3119190953084426750996785)
                  ·
                    refine ⟨2339393214813320063247589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3119190953084426750996785 2339393214813320063247589)
                    ·
                      refine ⟨438636227777497511858923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2339393214813320063247589 438636227777497511858923)
                      ·
                        rfl

theorem cell23_854241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_854241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854241 prefixEnd_854241 := by exact prefixLift 854241
  have htrace : WordTrace (prefixWord ++ tailWord_854241) baseStart_854241 baseEnd_854241 := by
    simpa [prefixWord, tailWord_854241, baseEnd_854241] using wordTrace_append hprefix tailTrace_854241
  have hstable : (prefixWord ++ tailWord_854241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854241).length < 2 ^ (prefixWord ++ tailWord_854241).sum := by decide
  have hdescent : baseEnd_854241 < baseStart_854241 := by decide
  rcases family_descends (prefixWord ++ tailWord_854241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854245 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_854245 : Nat := 118140960795 + 854245 * 2 ^ 59
def prefixEnd_854245 : Nat := 4983230072969 + 3 ^ 40 * 854245 * 2
def baseEnd_854245 : Nat := 438638281700115496208905

theorem tailTrace_854245 : CollatzResearch.WordTrace tailWord_854245 prefixEnd_854245 438638281700115496208905 := by
  unfold tailWord_854245
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156874790223733275940189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20771249860149155517293459 31156874790223733275940189)
  ·
    refine ⟨11683828046333899978477571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31156874790223733275940189 11683828046333899978477571)
    ·
      refine ⟨17525742069500849967716357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683828046333899978477571 17525742069500849967716357)
      ·
        refine ⟨3286076638031409368946817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17525742069500849967716357 3286076638031409368946817)
        ·
          refine ⟨2464557478523557026710113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286076638031409368946817 2464557478523557026710113)
          ·
            refine ⟨1848418108892667770032585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464557478523557026710113 1848418108892667770032585)
            ·
              refine ⟨1386313581669500827524439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848418108892667770032585 1386313581669500827524439)
              ·
                refine ⟨2079470372504251241286659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386313581669500827524439 2079470372504251241286659)
                ·
                  refine ⟨3119205558756376861929989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079470372504251241286659 3119205558756376861929989)
                  ·
                    refine ⟨584851042266820661611873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119205558756376861929989 584851042266820661611873)
                    ·
                      refine ⟨438638281700115496208905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584851042266820661611873 438638281700115496208905)
                      ·
                        rfl

theorem cell23_854245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_854245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854245 prefixEnd_854245 := by exact prefixLift 854245
  have htrace : WordTrace (prefixWord ++ tailWord_854245) baseStart_854245 baseEnd_854245 := by
    simpa [prefixWord, tailWord_854245, baseEnd_854245] using wordTrace_append hprefix tailTrace_854245
  have hstable : (prefixWord ++ tailWord_854245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854245).length < 2 ^ (prefixWord ++ tailWord_854245).sum := by decide
  have hdescent : baseEnd_854245 < baseStart_854245 := by decide
  rcases family_descends (prefixWord ++ tailWord_854245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854268 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 5]
def baseStart_854268 : Nat := 118140960795 + 854268 * 2 ^ 59
def prefixEnd_854268 : Nat := 4983230072969 + 3 ^ 40 * 854268 * 2
def baseEnd_854268 : Nat := 48738899083907656246811

theorem tailTrace_854268 : CollatzResearch.WordTrace tailWord_854268 prefixEnd_854268 48738899083907656246811 := by
  unfold tailWord_854268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578856834570204102013729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20771809112760272136018305 15578856834570204102013729)
  ·
    refine ⟨11684142625927653076510297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15578856834570204102013729 11684142625927653076510297)
    ·
      refine ⟨8763106969445739807382723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11684142625927653076510297 8763106969445739807382723)
      ·
        refine ⟨13144660454168609711074085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8763106969445739807382723 13144660454168609711074085)
        ·
          refine ⟨2464623835156614320826391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13144660454168609711074085 2464623835156614320826391)
          ·
            refine ⟨3696935752734921481239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464623835156614320826391 3696935752734921481239587)
            ·
              refine ⟨5545403629102382221859381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696935752734921481239587 5545403629102382221859381)
              ·
                refine ⟨519881590228348333299317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5545403629102382221859381 519881590228348333299317)
                ·
                  refine ⟨48738899083907656246811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519881590228348333299317 48738899083907656246811)
                  ·
                    rfl

theorem cell23_854268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_854268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854268 prefixEnd_854268 := by exact prefixLift 854268
  have htrace : WordTrace (prefixWord ++ tailWord_854268) baseStart_854268 baseEnd_854268 := by
    simpa [prefixWord, tailWord_854268, baseEnd_854268] using wordTrace_append hprefix tailTrace_854268
  have hstable : (prefixWord ++ tailWord_854268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854268).length < 2 ^ (prefixWord ++ tailWord_854268).sum := by decide
  have hdescent : baseEnd_854268 < baseStart_854268 := by decide
  rcases family_descends (prefixWord ++ tailWord_854268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854351 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_854351 : Nat := 118140960795 + 854351 * 2 ^ 59
def prefixEnd_854351 : Nat := 4983230072969 + 3 ^ 40 * 854351 * 2
def baseEnd_854351 : Nat := 438692710649492081483417

theorem tailTrace_854351 : CollatzResearch.WordTrace tailWord_854351 prefixEnd_854351 438692710649492081483417 := by
  unfold tailWord_854351
  simp only [CollatzResearch.WordTrace]
  refine ⟨31160740927839713379298907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20773827285226475586199271 31160740927839713379298907)
  ·
    refine ⟨46741111391759570068948361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31160740927839713379298907 46741111391759570068948361)
    ·
      refine ⟨35055833543819677551711271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46741111391759570068948361 35055833543819677551711271)
      ·
        refine ⟨52583750315729516327566907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35055833543819677551711271 52583750315729516327566907)
        ·
          refine ⟨78875625473594274491350361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52583750315729516327566907 78875625473594274491350361)
          ·
            refine ⟨59156719105195705868512771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78875625473594274491350361 59156719105195705868512771)
            ·
              refine ⟨88735078657793558802769157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59156719105195705868512771 88735078657793558802769157)
              ·
                refine ⟨16637827248336292275519217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88735078657793558802769157 16637827248336292275519217)
                ·
                  refine ⟨12478370436252219206639413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16637827248336292275519217 12478370436252219206639413)
                  ·
                    refine ⟨1169847228398645550622445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12478370436252219206639413 1169847228398645550622445)
                    ·
                      refine ⟨438692710649492081483417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169847228398645550622445 438692710649492081483417)
                      ·
                        rfl

theorem cell23_854351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_854351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854351 prefixEnd_854351 := by exact prefixLift 854351
  have htrace : WordTrace (prefixWord ++ tailWord_854351) baseStart_854351 baseEnd_854351 := by
    simpa [prefixWord, tailWord_854351, baseEnd_854351] using wordTrace_append hprefix tailTrace_854351
  have hstable : (prefixWord ++ tailWord_854351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854351).length < 2 ^ (prefixWord ++ tailWord_854351).sum := by decide
  have hdescent : baseEnd_854351 < baseStart_854351 := by decide
  rcases family_descends (prefixWord ++ tailWord_854351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854366 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_854366 : Nat := 118140960795 + 854366 * 2 ^ 59
def prefixEnd_854366 : Nat := 4983230072969 + 3 ^ 40 * 854366 * 2
def baseEnd_854366 : Nat := 146233470953103174265283

theorem tailTrace_854366 : CollatzResearch.WordTrace tailWord_854366 prefixEnd_854366 146233470953103174265283 := by
  unfold tailWord_854366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895161002848171367636869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20774192015190247294063301 3895161002848171367636869)
  ·
    refine ⟨730342688034032131431913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3895161002848171367636869 730342688034032131431913)
    ·
      refine ⟨547757016025524098573935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 730342688034032131431913 547757016025524098573935)
      ·
        refine ⟨821635524038286147860903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547757016025524098573935 821635524038286147860903)
        ·
          refine ⟨1232453286057429221791355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821635524038286147860903 1232453286057429221791355)
          ·
            refine ⟨1848679929086143832687033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232453286057429221791355 1848679929086143832687033)
            ·
              refine ⟨1386509946814607874515275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848679929086143832687033 1386509946814607874515275)
              ·
                refine ⟨2079764920221911811772913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386509946814607874515275 2079764920221911811772913)
                ·
                  refine ⟨1559823690166433858829685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079764920221911811772913 1559823690166433858829685)
                  ·
                    refine ⟨146233470953103174265283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559823690166433858829685 146233470953103174265283)
                    ·
                      rfl

theorem cell23_854366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_854366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854366 prefixEnd_854366 := by exact prefixLift 854366
  have htrace : WordTrace (prefixWord ++ tailWord_854366) baseStart_854366 baseEnd_854366 := by
    simpa [prefixWord, tailWord_854366, baseEnd_854366] using wordTrace_append hprefix tailTrace_854366
  have hstable : (prefixWord ++ tailWord_854366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854366).length < 2 ^ (prefixWord ++ tailWord_854366).sum := by decide
  have hdescent : baseEnd_854366 < baseStart_854366 := by decide
  rcases family_descends (prefixWord ++ tailWord_854366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854395 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 2, 3, 2]
def baseStart_854395 : Nat := 118140960795 + 854395 * 2 ^ 59
def prefixEnd_854395 : Nat := 4983230072969 + 3 ^ 40 * 854395 * 2
def baseEnd_854395 : Nat := 438715303798289909333215

theorem tailTrace_854395 : CollatzResearch.WordTrace tailWord_854395 prefixEnd_854395 438715303798289909333215 := by
  unfold tailWord_854395
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162345739680308893900639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20774897159786872595933759 31162345739680308893900639)
  ·
    refine ⟨46743518609520463340850959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31162345739680308893900639 46743518609520463340850959)
    ·
      refine ⟨70115277914280695011276439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46743518609520463340850959 70115277914280695011276439)
      ·
        refine ⟨105172916871421042516914659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70115277914280695011276439 105172916871421042516914659)
        ·
          refine ⟨157759375307131563775371989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105172916871421042516914659 157759375307131563775371989)
          ·
            refine ⟨3697485358760896025985281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 157759375307131563775371989 3697485358760896025985281)
            ·
              refine ⟨2773114019070672019488961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697485358760896025985281 2773114019070672019488961)
              ·
                refine ⟨2079835514303004014616721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773114019070672019488961 2079835514303004014616721)
                ·
                  refine ⟨1559876635727253010962541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079835514303004014616721 1559876635727253010962541)
                  ·
                    refine ⟨584953738397719879110953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559876635727253010962541 584953738397719879110953)
                    ·
                      refine ⟨438715303798289909333215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584953738397719879110953 438715303798289909333215)
                      ·
                        rfl

theorem cell23_854395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3, 2].length) (baseStart_854395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854395 prefixEnd_854395 := by exact prefixLift 854395
  have htrace : WordTrace (prefixWord ++ tailWord_854395) baseStart_854395 baseEnd_854395 := by
    simpa [prefixWord, tailWord_854395, baseEnd_854395] using wordTrace_append hprefix tailTrace_854395
  have hstable : (prefixWord ++ tailWord_854395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854395).length < 2 ^ (prefixWord ++ tailWord_854395).sum := by decide
  have hdescent : baseEnd_854395 < baseStart_854395 := by decide
  rcases family_descends (prefixWord ++ tailWord_854395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854408 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_854408 : Nat := 118140960795 + 854408 * 2 ^ 59
def prefixEnd_854408 : Nat := 4983230072969 + 3 ^ 40 * 854408 * 2
def baseEnd_854408 : Nat := 438721979046798358470655

theorem tailTrace_854408 : CollatzResearch.WordTrace tailWord_854408 prefixEnd_854408 438721979046798358470655 := by
  unfold tailWord_854408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15581409944316606057061939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20775213259088808076082585 15581409944316606057061939)
  ·
    refine ⟨23372114916474909085592909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15581409944316606057061939 23372114916474909085592909)
    ·
      refine ⟨8764543093678090907097341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23372114916474909085592909 8764543093678090907097341)
      ·
        refine ⟨3286703660129284090161503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8764543093678090907097341 3286703660129284090161503)
        ·
          refine ⟨4930055490193926135242255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286703660129284090161503 4930055490193926135242255)
          ·
            refine ⟨7395083235290889202863383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930055490193926135242255 7395083235290889202863383)
            ·
              refine ⟨11092624852936333804295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395083235290889202863383 11092624852936333804295075)
              ·
                refine ⟨16638937279404500706442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092624852936333804295075 16638937279404500706442613)
                ·
                  refine ⟨1559900369944171941228995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16638937279404500706442613 1559900369944171941228995)
                  ·
                    refine ⟨2339850554916257911843493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1559900369944171941228995 2339850554916257911843493)
                    ·
                      refine ⟨438721979046798358470655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2339850554916257911843493 438721979046798358470655)
                      ·
                        rfl

theorem cell23_854408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_854408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854408 prefixEnd_854408 := by exact prefixLift 854408
  have htrace : WordTrace (prefixWord ++ tailWord_854408) baseStart_854408 baseEnd_854408 := by
    simpa [prefixWord, tailWord_854408, baseEnd_854408] using wordTrace_append hprefix tailTrace_854408
  have hstable : (prefixWord ++ tailWord_854408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854408).length < 2 ^ (prefixWord ++ tailWord_854408).sum := by decide
  have hdescent : baseEnd_854408 < baseStart_854408 := by decide
  rcases family_descends (prefixWord ++ tailWord_854408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854429 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_854429 : Nat := 118140960795 + 854429 * 2 ^ 59
def prefixEnd_854429 : Nat := 4983230072969 + 3 ^ 40 * 854429 * 2
def baseEnd_854429 : Nat := 438732762140542776308059

theorem tailTrace_854429 : CollatzResearch.WordTrace tailWord_854429 prefixEnd_854429 438732762140542776308059 := by
  unfold tailWord_854429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31163585821557132700638341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20775723881038088467092227 31163585821557132700638341)
  ·
    refine ⟨5843172341541962381369689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31163585821557132700638341 5843172341541962381369689)
    ·
      refine ⟨4382379256156471786027267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5843172341541962381369689 4382379256156471786027267)
      ·
        refine ⟨6573568884234707679040901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382379256156471786027267 6573568884234707679040901)
        ·
          refine ⟨1232544165794007689820169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6573568884234707679040901 1232544165794007689820169)
          ·
            refine ⟨924408124345505767365127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232544165794007689820169 924408124345505767365127)
            ·
              refine ⟨1386612186518258651047691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924408124345505767365127 1386612186518258651047691)
              ·
                refine ⟨2079918279777387976571537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386612186518258651047691 2079918279777387976571537)
                ·
                  refine ⟨1559938709833040982428653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079918279777387976571537 1559938709833040982428653)
                  ·
                    refine ⟨584977016187390368410745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1559938709833040982428653 584977016187390368410745)
                    ·
                      refine ⟨438732762140542776308059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 584977016187390368410745 438732762140542776308059)
                      ·
                        rfl

theorem cell23_854429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_854429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854429 prefixEnd_854429 := by exact prefixLift 854429
  have htrace : WordTrace (prefixWord ++ tailWord_854429) baseStart_854429 baseEnd_854429 := by
    simpa [prefixWord, tailWord_854429, baseEnd_854429] using wordTrace_append hprefix tailTrace_854429
  have hstable : (prefixWord ++ tailWord_854429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854429).length < 2 ^ (prefixWord ++ tailWord_854429).sum := by decide
  have hdescent : baseEnd_854429 < baseStart_854429 := by decide
  rcases family_descends (prefixWord ++ tailWord_854429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854451 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_854451 : Nat := 118140960795 + 854451 * 2 ^ 59
def prefixEnd_854451 : Nat := 4983230072969 + 3 ^ 40 * 854451 * 2
def baseEnd_854451 : Nat := 438744058714941690232957

theorem tailTrace_854451 : CollatzResearch.WordTrace tailWord_854451 prefixEnd_854451 438744058714941690232957 := by
  unfold tailWord_854451
  simp only [CollatzResearch.WordTrace]
  refine ⟨31164388227477430457939207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20776258818318286971959471 31164388227477430457939207)
  ·
    refine ⟨46746582341216145686908811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31164388227477430457939207 46746582341216145686908811)
    ·
      refine ⟨70119873511824218530363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46746582341216145686908811 70119873511824218530363217)
      ·
        refine ⟨52589905133868163897772413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70119873511824218530363217 52589905133868163897772413)
        ·
          refine ⟨19721214425200561461664655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52589905133868163897772413 19721214425200561461664655)
          ·
            refine ⟨29581821637800842192496983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19721214425200561461664655 29581821637800842192496983)
            ·
              refine ⟨44372732456701263288745475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29581821637800842192496983 44372732456701263288745475)
              ·
                refine ⟨66559098685051894933118213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44372732456701263288745475 66559098685051894933118213)
                ·
                  refine ⟨12479831003447230299959665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66559098685051894933118213 12479831003447230299959665)
                  ·
                    refine ⟨9359873252585422724969749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12479831003447230299959665 9359873252585422724969749)
                    ·
                      refine ⟨438744058714941690232957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9359873252585422724969749 438744058714941690232957)
                      ·
                        rfl

theorem cell23_854451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_854451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854451 prefixEnd_854451 := by exact prefixLift 854451
  have htrace : WordTrace (prefixWord ++ tailWord_854451) baseStart_854451 baseEnd_854451 := by
    simpa [prefixWord, tailWord_854451, baseEnd_854451] using wordTrace_append hprefix tailTrace_854451
  have hstable : (prefixWord ++ tailWord_854451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854451).length < 2 ^ (prefixWord ++ tailWord_854451).sum := by decide
  have hdescent : baseEnd_854451 < baseStart_854451 := by decide
  rcases family_descends (prefixWord ++ tailWord_854451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854458 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_854458 : Nat := 118140960795 + 854458 * 2 ^ 59
def prefixEnd_854458 : Nat := 4983230072969 + 3 ^ 40 * 854458 * 2
def baseEnd_854458 : Nat := 438747653079523162845425

theorem tailTrace_854458 : CollatzResearch.WordTrace tailWord_854458 prefixEnd_854458 438747653079523162845425 := by
  unfold tailWord_854458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791160884613017663361007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20776429025634713768962685 7791160884613017663361007)
  ·
    refine ⟨11686741326919526495041511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791160884613017663361007 11686741326919526495041511)
    ·
      refine ⟨17530111990379289742562267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686741326919526495041511 17530111990379289742562267)
      ·
        refine ⟨26295167985568934613843401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530111990379289742562267 26295167985568934613843401)
        ·
          refine ⟨19721375989176700960382551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26295167985568934613843401 19721375989176700960382551)
          ·
            refine ⟨29582063983765051440573827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19721375989176700960382551 29582063983765051440573827)
            ·
              refine ⟨44373095975647577160860741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29582063983765051440573827 44373095975647577160860741)
              ·
                refine ⟨8319955495433920717661389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44373095975647577160860741 8319955495433920717661389)
                ·
                  refine ⟨3119983310787720269123021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8319955495433920717661389 3119983310787720269123021)
                  ·
                    refine ⟨1169993741545395100921133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3119983310787720269123021 1169993741545395100921133)
                    ·
                      refine ⟨438747653079523162845425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1169993741545395100921133 438747653079523162845425)
                      ·
                        rfl

theorem cell23_854458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_854458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854458 prefixEnd_854458 := by exact prefixLift 854458
  have htrace : WordTrace (prefixWord ++ tailWord_854458) baseStart_854458 baseEnd_854458 := by
    simpa [prefixWord, tailWord_854458, baseEnd_854458] using wordTrace_append hprefix tailTrace_854458
  have hstable : (prefixWord ++ tailWord_854458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854458).length < 2 ^ (prefixWord ++ tailWord_854458).sum := by decide
  have hdescent : baseEnd_854458 < baseStart_854458 := by decide
  rcases family_descends (prefixWord ++ tailWord_854458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854491 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 12]
def baseStart_854491 : Nat := 118140960795 + 854491 * 2 ^ 59
def prefixEnd_854491 : Nat := 4983230072969 + 3 ^ 40 * 854491 * 2
def baseEnd_854491 : Nat := 146254865980373844577591

theorem tailTrace_854491 : CollatzResearch.WordTrace tailWord_854491 prefixEnd_854491 146254865980373844577591 := by
  unfold tailWord_854491
  simp only [CollatzResearch.WordTrace]
  refine ⟨31165847147332517289395327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20777231431555011526263551 31165847147332517289395327)
  ·
    refine ⟨46748770720998775934092991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31165847147332517289395327 46748770720998775934092991)
    ·
      refine ⟨70123156081498163901139487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46748770720998775934092991 70123156081498163901139487)
      ·
        refine ⟨105184734122247245851709231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70123156081498163901139487 105184734122247245851709231)
        ·
          refine ⟨157777101183370868777563847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105184734122247245851709231 157777101183370868777563847)
          ·
            refine ⟨236665651775056303166345771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157777101183370868777563847 236665651775056303166345771)
            ·
              refine ⟨354998477662584454749518657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236665651775056303166345771 354998477662584454749518657)
              ·
                refine ⟨266248858246938341062138993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354998477662584454749518657 266248858246938341062138993)
                ·
                  refine ⟨199686643685203755796604245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266248858246938341062138993 199686643685203755796604245)
                  ·
                    refine ⟨146254865980373844577591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 199686643685203755796604245 146254865980373844577591)
                    ·
                      rfl

theorem cell23_854491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_854491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854491 prefixEnd_854491 := by exact prefixLift 854491
  have htrace : WordTrace (prefixWord ++ tailWord_854491) baseStart_854491 baseEnd_854491 := by
    simpa [prefixWord, tailWord_854491, baseEnd_854491] using wordTrace_append hprefix tailTrace_854491
  have hstable : (prefixWord ++ tailWord_854491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854491).length < 2 ^ (prefixWord ++ tailWord_854491).sum := by decide
  have hdescent : baseEnd_854491 < baseStart_854491 := by decide
  rcases family_descends (prefixWord ++ tailWord_854491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854538 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_854538 : Nat := 118140960795 + 854538 * 2 ^ 59
def prefixEnd_854538 : Nat := 4983230072969 + 3 ^ 40 * 854538 * 2
def baseEnd_854538 : Nat := 48754303503542538871673

theorem tailTrace_854538 : CollatzResearch.WordTrace tailWord_854538 prefixEnd_854538 48754303503542538871673 := by
  unfold tailWord_854538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791890344540561079089067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20778374252108162877570845 7791890344540561079089067)
  ·
    refine ⟨11687835516810841618633601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7791890344540561079089067 11687835516810841618633601)
    ·
      refine ⟨8765876637608131213975201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11687835516810841618633601 8765876637608131213975201)
      ·
        refine ⟨6574407478206098410481401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8765876637608131213975201 6574407478206098410481401)
        ·
          refine ⟨4930805608654573807861051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574407478206098410481401 4930805608654573807861051)
          ·
            refine ⟨7396208412981860711791577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930805608654573807861051 7396208412981860711791577)
            ·
              refine ⟨5547156309736395533843683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396208412981860711791577 5547156309736395533843683)
              ·
                refine ⟨8320734464604593300765525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547156309736395533843683 8320734464604593300765525)
                ·
                  refine ⟨48754303503542538871673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8320734464604593300765525 48754303503542538871673)
                  ·
                    rfl

theorem cell23_854538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_854538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854538 prefixEnd_854538 := by exact prefixLift 854538
  have htrace : WordTrace (prefixWord ++ tailWord_854538) baseStart_854538 baseEnd_854538 := by
    simpa [prefixWord, tailWord_854538, baseEnd_854538] using wordTrace_append hprefix tailTrace_854538
  have hstable : (prefixWord ++ tailWord_854538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854538).length < 2 ^ (prefixWord ++ tailWord_854538).sum := by decide
  have hdescent : baseEnd_854538 < baseStart_854538 := by decide
  rcases family_descends (prefixWord ++ tailWord_854538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854582 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_854582 : Nat := 118140960795 + 854582 * 2 ^ 59
def prefixEnd_854582 : Nat := 4983230072969 + 3 ^ 40 * 854582 * 2
def baseEnd_854582 : Nat := 438811324680680677694855

theorem tailTrace_854582 : CollatzResearch.WordTrace tailWord_854582 prefixEnd_854582 438811324680680677694855 := by
  unfold tailWord_854582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948072886875177489434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20779444126668559887305333 1948072886875177489434875)
  ·
    refine ⟨2922109330312766234152313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948072886875177489434875 2922109330312766234152313)
    ·
      refine ⟨2191581997734574675614235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2922109330312766234152313 2191581997734574675614235)
      ·
        refine ⟨3287372996601862013421353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191581997734574675614235 3287372996601862013421353)
        ·
          refine ⟨2465529747451396510066015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3287372996601862013421353 2465529747451396510066015)
          ·
            refine ⟨3698294621177094765099023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465529747451396510066015 3698294621177094765099023)
            ·
              refine ⟨5547441931765642147648535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698294621177094765099023 5547441931765642147648535)
              ·
                refine ⟨8321162897648463221472803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547441931765642147648535 8321162897648463221472803)
                ·
                  refine ⟨12481744346472694832209205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321162897648463221472803 12481744346472694832209205)
                  ·
                    refine ⟨1170163532481815140519613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12481744346472694832209205 1170163532481815140519613)
                    ·
                      refine ⟨438811324680680677694855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170163532481815140519613 438811324680680677694855)
                      ·
                        rfl

theorem cell23_854582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_854582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854582 prefixEnd_854582 := by exact prefixLift 854582
  have htrace : WordTrace (prefixWord ++ tailWord_854582) baseStart_854582 baseEnd_854582 := by
    simpa [prefixWord, tailWord_854582, baseEnd_854582] using wordTrace_append hprefix tailTrace_854582
  have hstable : (prefixWord ++ tailWord_854582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854582).length < 2 ^ (prefixWord ++ tailWord_854582).sum := by decide
  have hdescent : baseEnd_854582 < baseStart_854582 := by decide
  rcases family_descends (prefixWord ++ tailWord_854582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854602 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_854602 : Nat := 118140960795 + 854602 * 2 ^ 59
def prefixEnd_854602 : Nat := 4983230072969 + 3 ^ 40 * 854602 * 2
def baseEnd_854602 : Nat := 146273864764590199814921

theorem tailTrace_854602 : CollatzResearch.WordTrace tailWord_854602 prefixEnd_854602 146273864764590199814921 := by
  unfold tailWord_854602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792473912482595811671515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20779930433286922164457373 7792473912482595811671515)
  ·
    refine ⟨11688710868723893717507273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792473912482595811671515 11688710868723893717507273)
    ·
      refine ⟨8766533151542920288130455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11688710868723893717507273 8766533151542920288130455)
      ·
        refine ⟨13149799727314380432195683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766533151542920288130455 13149799727314380432195683)
        ·
          refine ⟨19724699590971570648293525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13149799727314380432195683 19724699590971570648293525)
          ·
            refine ⟨924595293326792374138759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19724699590971570648293525 924595293326792374138759)
            ·
              refine ⟨1386892939990188561208139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924595293326792374138759 1386892939990188561208139)
              ·
                refine ⟨2080339409985282841812209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386892939990188561208139 2080339409985282841812209)
                ·
                  refine ⟨1560254557488962131359157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080339409985282841812209 1560254557488962131359157)
                  ·
                    refine ⟨146273864764590199814921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1560254557488962131359157 146273864764590199814921)
                    ·
                      rfl

theorem cell23_854602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_854602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854602 prefixEnd_854602 := by exact prefixLift 854602
  have htrace : WordTrace (prefixWord ++ tailWord_854602) baseStart_854602 baseEnd_854602 := by
    simpa [prefixWord, tailWord_854602, baseEnd_854602] using wordTrace_append hprefix tailTrace_854602
  have hstable : (prefixWord ++ tailWord_854602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854602).length < 2 ^ (prefixWord ++ tailWord_854602).sum := by decide
  have hdescent : baseEnd_854602 < baseStart_854602 := by decide
  rcases family_descends (prefixWord ++ tailWord_854602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854608 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_854608 : Nat := 118140960795 + 854608 * 2 ^ 59
def prefixEnd_854608 : Nat := 4983230072969 + 3 ^ 40 * 854608 * 2
def baseEnd_854608 : Nat := 438824675177697575969735

theorem tailTrace_854608 : CollatzResearch.WordTrace tailWord_854608 prefixEnd_854608 438824675177697575969735 := by
  unfold tailWord_854608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15585057243954323135702239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20780076325272430847602985 15585057243954323135702239)
  ·
    refine ⟨23377585865931484703553359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15585057243954323135702239 23377585865931484703553359)
    ·
      refine ⟨35066378798897227055330039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23377585865931484703553359 35066378798897227055330039)
      ·
        refine ⟨52599568198345840582995059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35066378798897227055330039 52599568198345840582995059)
        ·
          refine ⟨78899352297518760874492589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52599568198345840582995059 78899352297518760874492589)
          ·
            refine ⟨29587257111569535327934721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78899352297518760874492589 29587257111569535327934721)
            ·
              refine ⟨22190442833677151495951041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29587257111569535327934721 22190442833677151495951041)
              ·
                refine ⟨16642832125257863621963281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22190442833677151495951041 16642832125257863621963281)
                ·
                  refine ⟨12482124093943397716472461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16642832125257863621963281 12482124093943397716472461)
                  ·
                    refine ⟨4680796535228774143677173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12482124093943397716472461 4680796535228774143677173)
                    ·
                      refine ⟨438824675177697575969735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4680796535228774143677173 438824675177697575969735)
                      ·
                        rfl

theorem cell23_854608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_854608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854608 prefixEnd_854608 := by exact prefixLift 854608
  have htrace : WordTrace (prefixWord ++ tailWord_854608) baseStart_854608 baseEnd_854608 := by
    simpa [prefixWord, tailWord_854608, baseEnd_854608] using wordTrace_append hprefix tailTrace_854608
  have hstable : (prefixWord ++ tailWord_854608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854608).length < 2 ^ (prefixWord ++ tailWord_854608).sum := by decide
  have hdescent : baseEnd_854608 < baseStart_854608 := by decide
  rcases family_descends (prefixWord ++ tailWord_854608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854615 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 5, 4]
def baseStart_854615 : Nat := 118140960795 + 854615 * 2 ^ 59
def prefixEnd_854615 : Nat := 4983230072969 + 3 ^ 40 * 854615 * 2
def baseEnd_854615 : Nat := 146276089847426349527401

theorem tailTrace_854615 : CollatzResearch.WordTrace tailWord_854615 prefixEnd_854615 146276089847426349527401 := by
  unfold tailWord_854615
  simp only [CollatzResearch.WordTrace]
  refine ⟨31170369798883286466909299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20780246532588857644606199 31170369798883286466909299)
  ·
    refine ⟨46755554698324929700363949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31170369798883286466909299 46755554698324929700363949)
    ·
      refine ⟨17533333011871848637636481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46755554698324929700363949 17533333011871848637636481)
      ·
        refine ⟨13149999758903886478227361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17533333011871848637636481 13149999758903886478227361)
        ·
          refine ⟨9862499819177914858670521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13149999758903886478227361 9862499819177914858670521)
          ·
            refine ⟨7396874864383436144002891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9862499819177914858670521 7396874864383436144002891)
            ·
              refine ⟨11095312296575154216004337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396874864383436144002891 11095312296575154216004337)
              ·
                refine ⟨8321484222431365662003253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095312296575154216004337 8321484222431365662003253)
                ·
                  refine ⟨780139145852940530812805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8321484222431365662003253 780139145852940530812805)
                  ·
                    refine ⟨146276089847426349527401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780139145852940530812805 146276089847426349527401)
                    ·
                      rfl

theorem cell23_854615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_854615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854615 prefixEnd_854615 := by exact prefixLift 854615
  have htrace : WordTrace (prefixWord ++ tailWord_854615) baseStart_854615 baseEnd_854615 := by
    simpa [prefixWord, tailWord_854615, baseEnd_854615] using wordTrace_append hprefix tailTrace_854615
  have hstable : (prefixWord ++ tailWord_854615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854615).length < 2 ^ (prefixWord ++ tailWord_854615).sum := by decide
  have hdescent : baseEnd_854615 < baseStart_854615 := by decide
  rcases family_descends (prefixWord ++ tailWord_854615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854709 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_854709 : Nat := 118140960795 + 854709 * 2 ^ 59
def prefixEnd_854709 : Nat := 4983230072969 + 3 ^ 40 * 854709 * 2
def baseEnd_854709 : Nat := 146292178907933893602257

theorem tailTrace_854709 : CollatzResearch.WordTrace tailWord_854709 prefixEnd_854709 146292178907933893602257 := by
  unfold tailWord_854709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173798260542740520831181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20782532173695160347220787 31173798260542740520831181)
  ·
    refine ⟨11690174347703527695311693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31173798260542740520831181 11690174347703527695311693)
    ·
      refine ⟨4383815380388822885741885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11690174347703527695311693 4383815380388822885741885)
      ·
        refine ⟨1643930767645808582153207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4383815380388822885741885 1643930767645808582153207)
        ·
          refine ⟨2465896151468712873229811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643930767645808582153207 2465896151468712873229811)
          ·
            refine ⟨3698844227203069309844717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465896151468712873229811 3698844227203069309844717)
            ·
              refine ⟨1387066585201150991191769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3698844227203069309844717 1387066585201150991191769)
              ·
                refine ⟨1040299938900863243393827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387066585201150991191769 1040299938900863243393827)
                ·
                  refine ⟨1560449908351294865090741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040299938900863243393827 1560449908351294865090741)
                  ·
                    refine ⟨146292178907933893602257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1560449908351294865090741 146292178907933893602257)
                    ·
                      rfl

theorem cell23_854709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_854709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854709 prefixEnd_854709 := by exact prefixLift 854709
  have htrace : WordTrace (prefixWord ++ tailWord_854709) baseStart_854709 baseEnd_854709 := by
    simpa [prefixWord, tailWord_854709, baseEnd_854709] using wordTrace_append hprefix tailTrace_854709
  have hstable : (prefixWord ++ tailWord_854709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854709).length < 2 ^ (prefixWord ++ tailWord_854709).sum := by decide
  have hdescent : baseEnd_854709 < baseStart_854709 := by decide
  rcases family_descends (prefixWord ++ tailWord_854709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854775 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_854775 : Nat := 118140960795 + 854775 * 2 ^ 59
def prefixEnd_854775 : Nat := 4983230072969 + 3 ^ 40 * 854775 * 2
def baseEnd_854775 : Nat := 438910426446998422581467

theorem tailTrace_854775 : CollatzResearch.WordTrace tailWord_854775 prefixEnd_854775 438910426446998422581467 := by
  unfold tailWord_854775
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176205478303633792733779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20784136985535755861822519 31176205478303633792733779)
  ·
    refine ⟨46764308217455450689100669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31176205478303633792733779 46764308217455450689100669)
    ·
      refine ⟨17536615581545794008412751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46764308217455450689100669 17536615581545794008412751)
      ·
        refine ⟨26304923372318691012619127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536615581545794008412751 26304923372318691012619127)
        ·
          refine ⟨39457385058478036518928691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26304923372318691012619127 39457385058478036518928691)
          ·
            refine ⟨59186077587717054778393037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39457385058478036518928691 59186077587717054778393037)
            ·
              refine ⟨22194779095393895541897389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59186077587717054778393037 22194779095393895541897389)
              ·
                refine ⟨8323042160772710828211521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22194779095393895541897389 8323042160772710828211521)
                ·
                  refine ⟨6242281620579533121158641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8323042160772710828211521 6242281620579533121158641)
                  ·
                    refine ⟨4681711215434649840868981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6242281620579533121158641 4681711215434649840868981)
                    ·
                      refine ⟨438910426446998422581467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4681711215434649840868981 438910426446998422581467)
                      ·
                        rfl

theorem cell23_854775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_854775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854775 prefixEnd_854775 := by exact prefixLift 854775
  have htrace : WordTrace (prefixWord ++ tailWord_854775) baseStart_854775 baseEnd_854775 := by
    simpa [prefixWord, tailWord_854775, baseEnd_854775] using wordTrace_append hprefix tailTrace_854775
  have hstable : (prefixWord ++ tailWord_854775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854775).length < 2 ^ (prefixWord ++ tailWord_854775).sum := by decide
  have hdescent : baseEnd_854775 < baseStart_854775 := by decide
  rcases family_descends (prefixWord ++ tailWord_854775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854812 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_854812 : Nat := 118140960795 + 854812 * 2 ^ 59
def prefixEnd_854812 : Nat := 4983230072969 + 3 ^ 40 * 854812 * 2
def baseEnd_854812 : Nat := 146309808410404925939599

theorem tailTrace_854812 : CollatzResearch.WordTrace tailWord_854812 prefixEnd_854812 146309808410404925939599 := by
  unfold tailWord_854812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588777489584794555915345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20785036652779726074553793 15588777489584794555915345)
  ·
    refine ⟨11691583117188595916936509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15588777489584794555915345 11691583117188595916936509)
    ·
      refine ⟨4384343668945723468851191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11691583117188595916936509 4384343668945723468851191)
      ·
        refine ⟨6576515503418585203276787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384343668945723468851191 6576515503418585203276787)
        ·
          refine ⟨9864773255127877804915181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576515503418585203276787 9864773255127877804915181)
          ·
            refine ⟨3699289970672954176843193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9864773255127877804915181 3699289970672954176843193)
            ·
              refine ⟨2774467478004715632632395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699289970672954176843193 2774467478004715632632395)
              ·
                refine ⟨4161701217007073448948593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774467478004715632632395 4161701217007073448948593)
                ·
                  refine ⟨3121275912755305086711445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161701217007073448948593 3121275912755305086711445)
                  ·
                    refine ⟨146309808410404925939599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3121275912755305086711445 146309808410404925939599)
                    ·
                      rfl

theorem cell23_854812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_854812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854812 prefixEnd_854812 := by exact prefixLift 854812
  have htrace : WordTrace (prefixWord ++ tailWord_854812) baseStart_854812 baseEnd_854812 := by
    simpa [prefixWord, tailWord_854812, baseEnd_854812] using wordTrace_append hprefix tailTrace_854812
  have hstable : (prefixWord ++ tailWord_854812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854812).length < 2 ^ (prefixWord ++ tailWord_854812).sum := by decide
  have hdescent : baseEnd_854812 < baseStart_854812 := by decide
  rcases family_descends (prefixWord ++ tailWord_854812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854813 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_854813 : Nat := 118140960795 + 854813 * 2 ^ 59
def prefixEnd_854813 : Nat := 4983230072969 + 3 ^ 40 * 854813 * 2
def baseEnd_854813 : Nat := 438929938711869273906293

theorem tailTrace_854813 : CollatzResearch.WordTrace tailWord_854813 prefixEnd_854813 438929938711869273906293 := by
  unfold tailWord_854813
  simp only [CollatzResearch.WordTrace]
  refine ⟨31177591452165966282617093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20785060968110644188411395 31177591452165966282617093)
  ·
    refine ⟨5845798397281118677990705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31177591452165966282617093 5845798397281118677990705)
    ·
      refine ⟨4384348797960839008493029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5845798397281118677990705 4384348797960839008493029)
      ·
        refine ⟨822065399617657314092443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4384348797960839008493029 822065399617657314092443)
        ·
          refine ⟨1233098099426485971138665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822065399617657314092443 1233098099426485971138665)
          ·
            refine ⟨924823574569864478353999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233098099426485971138665 924823574569864478353999)
            ·
              refine ⟨1387235361854796717530999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924823574569864478353999 1387235361854796717530999)
              ·
                refine ⟨2080853042782195076296499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387235361854796717530999 2080853042782195076296499)
                ·
                  refine ⟨3121279564173292614444749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080853042782195076296499 3121279564173292614444749)
                  ·
                    refine ⟨1170479836564984730416781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121279564173292614444749 1170479836564984730416781)
                    ·
                      refine ⟨438929938711869273906293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170479836564984730416781 438929938711869273906293)
                      ·
                        rfl

theorem cell23_854813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_854813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854813 prefixEnd_854813 := by exact prefixLift 854813
  have htrace : WordTrace (prefixWord ++ tailWord_854813) baseStart_854813 baseEnd_854813 := by
    simpa [prefixWord, tailWord_854813, baseEnd_854813] using wordTrace_append hprefix tailTrace_854813
  have hstable : (prefixWord ++ tailWord_854813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854813).length < 2 ^ (prefixWord ++ tailWord_854813).sum := by decide
  have hdescent : baseEnd_854813 < baseStart_854813 := by decide
  rcases family_descends (prefixWord ++ tailWord_854813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854909 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_854909 : Nat := 118140960795 + 854909 * 2 ^ 59
def prefixEnd_854909 : Nat := 4983230072969 + 3 ^ 40 * 854909 * 2
def baseEnd_854909 : Nat := 438979232854700898305851

theorem tailTrace_854909 : CollatzResearch.WordTrace tailWord_854909 prefixEnd_854909 438979232854700898305851 := by
  unfold tailWord_854909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31181092859818174678111781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20787395239878783118741187 31181092859818174678111781)
  ·
    refine ⟨5846454911215907752145959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31181092859818174678111781 5846454911215907752145959)
    ·
      refine ⟨8769682366823861628218939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846454911215907752145959 8769682366823861628218939)
      ·
        refine ⟨13154523550235792442328409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769682366823861628218939 13154523550235792442328409)
        ·
          refine ⟨9865892662676844331746307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13154523550235792442328409 9865892662676844331746307)
          ·
            refine ⟨14798838994015266497619461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865892662676844331746307 14798838994015266497619461)
            ·
              refine ⟨2774782311377862468303649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14798838994015266497619461 2774782311377862468303649)
              ·
                refine ⟨2081086733533396851227737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774782311377862468303649 2081086733533396851227737)
                ·
                  refine ⟨1560815050150047638420803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081086733533396851227737 1560815050150047638420803)
                  ·
                    refine ⟨2341222575225071457631205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560815050150047638420803 2341222575225071457631205)
                    ·
                      refine ⟨438979232854700898305851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2341222575225071457631205 438979232854700898305851)
                      ·
                        rfl

theorem cell23_854909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_854909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854909 prefixEnd_854909 := by exact prefixLift 854909
  have htrace : WordTrace (prefixWord ++ tailWord_854909) baseStart_854909 baseEnd_854909 := by
    simpa [prefixWord, tailWord_854909, baseEnd_854909] using wordTrace_append hprefix tailTrace_854909
  have hstable : (prefixWord ++ tailWord_854909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854909).length < 2 ^ (prefixWord ++ tailWord_854909).sum := by decide
  have hdescent : baseEnd_854909 < baseStart_854909 := by decide
  rcases family_descends (prefixWord ++ tailWord_854909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854946 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_854946 : Nat := 118140960795 + 854946 * 2 ^ 59
def prefixEnd_854946 : Nat := 4983230072969 + 3 ^ 40 * 854946 * 2
def baseEnd_854946 : Nat := 438998231638917253543181

theorem tailTrace_854946 : CollatzResearch.WordTrace tailWord_854946 prefixEnd_854946 438998231638917253543181 := by
  unfold tailWord_854946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795610590171032499302173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20788294907122753331472461 7795610590171032499302173)
  ·
    refine ⟨2923353971314137187238315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7795610590171032499302173 2923353971314137187238315)
    ·
      refine ⟨4385030956971205780857473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923353971314137187238315 4385030956971205780857473)
      ·
        refine ⟨3288773217728404335643105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4385030956971205780857473 3288773217728404335643105)
        ·
          refine ⟨2466579913296303251732329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3288773217728404335643105 2466579913296303251732329)
          ·
            refine ⟨1849934934972227438799247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2466579913296303251732329 1849934934972227438799247)
            ·
              refine ⟨2774902402458341158198871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849934934972227438799247 2774902402458341158198871)
              ·
                refine ⟨4162353603687511737298307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774902402458341158198871 4162353603687511737298307)
                ·
                  refine ⟨6243530405531267605947461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162353603687511737298307 6243530405531267605947461)
                  ·
                    refine ⟨1170661951037112676115149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6243530405531267605947461 1170661951037112676115149)
                    ·
                      refine ⟨438998231638917253543181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170661951037112676115149 438998231638917253543181)
                      ·
                        rfl

theorem cell23_854946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_854946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854946 prefixEnd_854946 := by exact prefixLift 854946
  have htrace : WordTrace (prefixWord ++ tailWord_854946) baseStart_854946 baseEnd_854946 := by
    simpa [prefixWord, tailWord_854946, baseEnd_854946] using wordTrace_append hprefix tailTrace_854946
  have hstable : (prefixWord ++ tailWord_854946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854946).length < 2 ^ (prefixWord ++ tailWord_854946).sum := by decide
  have hdescent : baseEnd_854946 < baseStart_854946 := by decide
  rcases family_descends (prefixWord ++ tailWord_854946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854976 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_854976 : Nat := 118140960795 + 854976 * 2 ^ 59
def prefixEnd_854976 : Nat := 4983230072969 + 3 ^ 40 * 854976 * 2
def baseEnd_854976 : Nat := 439013636058552136168043

theorem tailTrace_854976 : CollatzResearch.WordTrace tailWord_854976 prefixEnd_854976 439013636058552136168043 := by
  unfold tailWord_854976
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591768275287722560400391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20789024367050296747200521 15591768275287722560400391)
  ·
    refine ⟨23387652412931583840600587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15591768275287722560400391 23387652412931583840600587)
    ·
      refine ⟨35081478619397375760900881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23387652412931583840600587 35081478619397375760900881)
      ·
        refine ⟨26311108964548031820675661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35081478619397375760900881 26311108964548031820675661)
        ·
          refine ⟨9866665861705511932753373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26311108964548031820675661 9866665861705511932753373)
          ·
            refine ⟨3699999698139566974782515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9866665861705511932753373 3699999698139566974782515)
            ·
              refine ⟨5549999547209350462173773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699999698139566974782515 5549999547209350462173773)
              ·
                refine ⟨2081249830203506423315165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5549999547209350462173773 2081249830203506423315165)
                ·
                  refine ⟨780468686326314908743187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2081249830203506423315165 780468686326314908743187)
                  ·
                    refine ⟨1170703029489472363114781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 780468686326314908743187 1170703029489472363114781)
                    ·
                      refine ⟨439013636058552136168043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170703029489472363114781 439013636058552136168043)
                      ·
                        rfl

theorem cell23_854976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_854976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854976 prefixEnd_854976 := by exact prefixLift 854976
  have htrace : WordTrace (prefixWord ++ tailWord_854976) baseStart_854976 baseEnd_854976 := by
    simpa [prefixWord, tailWord_854976, baseEnd_854976] using wordTrace_append hprefix tailTrace_854976
  have hstable : (prefixWord ++ tailWord_854976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854976).length < 2 ^ (prefixWord ++ tailWord_854976).sum := by decide
  have hdescent : baseEnd_854976 < baseStart_854976 := by decide
  rcases family_descends (prefixWord ++ tailWord_854976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854996 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_854996 : Nat := 118140960795 + 854996 * 2 ^ 59
def prefixEnd_854996 : Nat := 4983230072969 + 3 ^ 40 * 854996 * 2
def baseEnd_854996 : Nat := 146341301890547352639317

theorem tailTrace_854996 : CollatzResearch.WordTrace tailWord_854996 prefixEnd_854996 146341301890547352639317 := by
  unfold tailWord_854996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592133005251494268264421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20789510673668659024352561 15592133005251494268264421)
  ·
    refine ⟨2923524938484655175299579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15592133005251494268264421 2923524938484655175299579)
    ·
      refine ⟨4385287407726982762949369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923524938484655175299579 4385287407726982762949369)
      ·
        refine ⟨3288965555795237072212027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4385287407726982762949369 3288965555795237072212027)
        ·
          refine ⟨4933448333692855608318041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288965555795237072212027 4933448333692855608318041)
          ·
            refine ⟨3700086250269641706238531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4933448333692855608318041 3700086250269641706238531)
            ·
              refine ⟨5550129375404462559357797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700086250269641706238531 5550129375404462559357797)
              ·
                refine ⟨1040649257888336729879587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5550129375404462559357797 1040649257888336729879587)
                ·
                  refine ⟨1560973886832505094819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040649257888336729879587 1560973886832505094819381)
                  ·
                    refine ⟨146341301890547352639317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1560973886832505094819381 146341301890547352639317)
                    ·
                      rfl

theorem cell23_854996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_854996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_854996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_854996 prefixEnd_854996 := by exact prefixLift 854996
  have htrace : WordTrace (prefixWord ++ tailWord_854996) baseStart_854996 baseEnd_854996 := by
    simpa [prefixWord, tailWord_854996, baseEnd_854996] using wordTrace_append hprefix tailTrace_854996
  have hstable : (prefixWord ++ tailWord_854996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854996).length < 2 ^ (prefixWord ++ tailWord_854996).sum := by decide
  have hdescent : baseEnd_854996 < baseStart_854996 := by decide
  rcases family_descends (prefixWord ++ tailWord_854996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855016 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_855016 : Nat := 118140960795 + 855016 * 2 ^ 59
def prefixEnd_855016 : Nat := 4983230072969 + 3 ^ 40 * 855016 * 2
def baseEnd_855016 : Nat := 439034175284731979667859

theorem tailTrace_855016 : CollatzResearch.WordTrace tailWord_855016 prefixEnd_855016 439034175284731979667859 := by
  unfold tailWord_855016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15592497735215265976128451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20789996980287021301504601 15592497735215265976128451)
  ·
    refine ⟨23388746602822898964192677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15592497735215265976128451 23388746602822898964192677)
    ·
      refine ⟨4385389988029293555786127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23388746602822898964192677 4385389988029293555786127)
      ·
        refine ⟨6578084982043940333679191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385389988029293555786127 6578084982043940333679191)
        ·
          refine ⟨9867127473065910500518787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578084982043940333679191 9867127473065910500518787)
          ·
            refine ⟨14800691209598865750778181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867127473065910500518787 14800691209598865750778181)
            ·
              refine ⟨2775129601799787328270909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14800691209598865750778181 2775129601799787328270909)
              ·
                refine ⟨1040673600674920248101591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775129601799787328270909 1040673600674920248101591)
                ·
                  refine ⟨1561010401012380372152387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040673600674920248101591 1561010401012380372152387)
                  ·
                    refine ⟨2341515601518570558228581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561010401012380372152387 2341515601518570558228581)
                    ·
                      refine ⟨439034175284731979667859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2341515601518570558228581 439034175284731979667859)
                      ·
                        rfl

theorem cell23_855016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_855016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855016 prefixEnd_855016 := by exact prefixLift 855016
  have htrace : WordTrace (prefixWord ++ tailWord_855016) baseStart_855016 baseEnd_855016 := by
    simpa [prefixWord, tailWord_855016, baseEnd_855016] using wordTrace_append hprefix tailTrace_855016
  have hstable : (prefixWord ++ tailWord_855016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855016).length < 2 ^ (prefixWord ++ tailWord_855016).sum := by decide
  have hdescent : baseEnd_855016 < baseStart_855016 := by decide
  rcases family_descends (prefixWord ++ tailWord_855016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855019 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3]
def baseStart_855019 : Nat := 118140960795 + 855019 * 2 ^ 59
def prefixEnd_855019 : Nat := 4983230072969 + 3 ^ 40 * 855019 * 2
def baseEnd_855019 : Nat := 439035715726695467930345

theorem tailTrace_855019 : CollatzResearch.WordTrace tailWord_855019 prefixEnd_855019 439035715726695467930345 := by
  unfold tailWord_855019
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185104889419663464616111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20790069926279775643077407 31185104889419663464616111)
  ·
    refine ⟨46777657334129495196924167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31185104889419663464616111 46777657334129495196924167)
    ·
      refine ⟨70166486001194242795386251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46777657334129495196924167 70166486001194242795386251)
      ·
        refine ⟨105249729001791364193079377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70166486001194242795386251 105249729001791364193079377)
        ·
          refine ⟨78937296751343523144809533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105249729001791364193079377 78937296751343523144809533)
          ·
            refine ⟨29601486281753821179303575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78937296751343523144809533 29601486281753821179303575)
            ·
              refine ⟨44402229422630731768955363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29601486281753821179303575 44402229422630731768955363)
              ·
                refine ⟨66603344133946097653433045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44402229422630731768955363 66603344133946097653433045)
                ·
                  refine ⟨1561015878139361663752337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66603344133946097653433045 1561015878139361663752337)
                  ·
                    refine ⟨1170761908604521247814253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561015878139361663752337 1170761908604521247814253)
                    ·
                      refine ⟨439035715726695467930345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170761908604521247814253 439035715726695467930345)
                      ·
                        rfl

theorem cell23_855019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 3].length) (baseStart_855019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855019 prefixEnd_855019 := by exact prefixLift 855019
  have htrace : WordTrace (prefixWord ++ tailWord_855019) baseStart_855019 baseEnd_855019 := by
    simpa [prefixWord, tailWord_855019, baseEnd_855019] using wordTrace_append hprefix tailTrace_855019
  have hstable : (prefixWord ++ tailWord_855019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855019).length < 2 ^ (prefixWord ++ tailWord_855019).sum := by decide
  have hdescent : baseEnd_855019 < baseStart_855019 := by decide
  rcases family_descends (prefixWord ++ tailWord_855019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855049 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_855049 : Nat := 118140960795 + 855049 * 2 ^ 59
def prefixEnd_855049 : Nat := 4983230072969 + 3 ^ 40 * 855049 * 2
def baseEnd_855049 : Nat := 439051120146330350555207

theorem tailTrace_855049 : CollatzResearch.WordTrace tailWord_855049 prefixEnd_855049 439051120146330350555207 := by
  unfold tailWord_855049
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186199079310978588208201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20790799386207319058805467 31186199079310978588208201)
  ·
    refine ⟨23389649309483233941156151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31186199079310978588208201 23389649309483233941156151)
    ·
      refine ⟨35084473964224850911734227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23389649309483233941156151 35084473964224850911734227)
      ·
        refine ⟨52626710946337276367601341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35084473964224850911734227 52626710946337276367601341)
        ·
          refine ⟨19735016604876478637850503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52626710946337276367601341 19735016604876478637850503)
          ·
            refine ⟨29602524907314717956775755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735016604876478637850503 29602524907314717956775755)
            ·
              refine ⟨44403787360972076935163633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29602524907314717956775755 44403787360972076935163633)
              ·
                refine ⟨33302840520729057701372725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44403787360972076935163633 33302840520729057701372725)
                ·
                  refine ⟨3122141298818349159503693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33302840520729057701372725 3122141298818349159503693)
                  ·
                    refine ⟨1170802987056880934813885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122141298818349159503693 1170802987056880934813885)
                    ·
                      refine ⟨439051120146330350555207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170802987056880934813885 439051120146330350555207)
                      ·
                        rfl

theorem cell23_855049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_855049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855049 prefixEnd_855049 := by exact prefixLift 855049
  have htrace : WordTrace (prefixWord ++ tailWord_855049) baseStart_855049 baseEnd_855049 := by
    simpa [prefixWord, tailWord_855049, baseEnd_855049] using wordTrace_append hprefix tailTrace_855049
  have hstable : (prefixWord ++ tailWord_855049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855049).length < 2 ^ (prefixWord ++ tailWord_855049).sum := by decide
  have hdescent : baseEnd_855049 < baseStart_855049 := by decide
  rcases family_descends (prefixWord ++ tailWord_855049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855066 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_855066 : Nat := 118140960795 + 855066 * 2 ^ 59
def prefixEnd_855066 : Nat := 4983230072969 + 3 ^ 40 * 855066 * 2
def baseEnd_855066 : Nat := 439059849317456784042629

theorem tailTrace_855066 : CollatzResearch.WordTrace tailWord_855066 prefixEnd_855066 439059849317456784042629 := by
  unfold tailWord_855066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796704780062347622894263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20791212746832926994384701 7796704780062347622894263)
  ·
    refine ⟨11695057170093521434341395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7796704780062347622894263 11695057170093521434341395)
    ·
      refine ⟨17542585755140282151512093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695057170093521434341395 17542585755140282151512093)
      ·
        refine ⟨6578469658177605806817035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17542585755140282151512093 6578469658177605806817035)
        ·
          refine ⟨9867704487266408710225553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578469658177605806817035 9867704487266408710225553)
          ·
            refine ⟨7400778365449806532669165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867704487266408710225553 7400778365449806532669165)
            ·
              refine ⟨2775291887043677449750937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7400778365449806532669165 2775291887043677449750937)
              ·
                refine ⟨2081468915282758087313203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775291887043677449750937 2081468915282758087313203)
                ·
                  refine ⟨3122203372924137130969805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081468915282758087313203 3122203372924137130969805)
                  ·
                    refine ⟨1170826264846551424113677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122203372924137130969805 1170826264846551424113677)
                    ·
                      refine ⟨439059849317456784042629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170826264846551424113677 439059849317456784042629)
                      ·
                        rfl

theorem cell23_855066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_855066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855066 prefixEnd_855066 := by exact prefixLift 855066
  have htrace : WordTrace (prefixWord ++ tailWord_855066) baseStart_855066 baseEnd_855066 := by
    simpa [prefixWord, tailWord_855066, baseEnd_855066] using wordTrace_append hprefix tailTrace_855066
  have hstable : (prefixWord ++ tailWord_855066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855066).length < 2 ^ (prefixWord ++ tailWord_855066).sum := by decide
  have hdescent : baseEnd_855066 < baseStart_855066 := by decide
  rcases family_descends (prefixWord ++ tailWord_855066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855083 : List Nat := [1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 3]
def baseStart_855083 : Nat := 118140960795 + 855083 * 2 ^ 59
def prefixEnd_855083 : Nat := 4983230072969 + 3 ^ 40 * 855083 * 2
def baseEnd_855083 : Nat := 439068578488583217530051

theorem tailTrace_855083 : CollatzResearch.WordTrace tailWord_855083 prefixEnd_855083 439068578488583217530051 := by
  unfold tailWord_855083
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187439161187802394945903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20791626107458534929963935 31187439161187802394945903)
  ·
    refine ⟨46781158741781703592418855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187439161187802394945903 46781158741781703592418855)
    ·
      refine ⟨70171738112672555388628283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46781158741781703592418855 70171738112672555388628283)
      ·
        refine ⟨105257607169008833082942425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70171738112672555388628283 105257607169008833082942425)
        ·
          refine ⟨78943205376756624812206819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105257607169008833082942425 78943205376756624812206819)
          ·
            refine ⟨118414808065134937218310229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78943205376756624812206819 118414808065134937218310229)
            ·
              refine ⟨1387673532013300045527073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 118414808065134937218310229 1387673532013300045527073)
              ·
                refine ⟨1040755149009975034145305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387673532013300045527073 1040755149009975034145305)
                ·
                  refine ⟨780566361757481275608979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040755149009975034145305 780566361757481275608979)
                  ·
                    refine ⟨1170849542636221913413469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 780566361757481275608979 1170849542636221913413469)
                    ·
                      refine ⟨439068578488583217530051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170849542636221913413469 439068578488583217530051)
                      ·
                        rfl

theorem cell23_855083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 3].length) (baseStart_855083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855083 prefixEnd_855083 := by exact prefixLift 855083
  have htrace : WordTrace (prefixWord ++ tailWord_855083) baseStart_855083 baseEnd_855083 := by
    simpa [prefixWord, tailWord_855083, baseEnd_855083] using wordTrace_append hprefix tailTrace_855083
  have hstable : (prefixWord ++ tailWord_855083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855083).length < 2 ^ (prefixWord ++ tailWord_855083).sum := by decide
  have hdescent : baseEnd_855083 < baseStart_855083 := by decide
  rcases family_descends (prefixWord ++ tailWord_855083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855089 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_855089 : Nat := 118140960795 + 855089 * 2 ^ 59
def prefixEnd_855089 : Nat := 4983230072969 + 3 ^ 40 * 855089 * 2
def baseEnd_855089 : Nat := 439071659372510194055023

theorem tailTrace_855089 : CollatzResearch.WordTrace tailWord_855089 prefixEnd_855089 439071659372510194055023 := by
  unfold tailWord_855089
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187657999166065419664321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20791771999444043613109547 31187657999166065419664321)
  ·
    refine ⟨23390743499374549064748241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31187657999166065419664321 23390743499374549064748241)
    ·
      refine ⟨17543057624530911798561181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23390743499374549064748241 17543057624530911798561181)
      ·
        refine ⟨6578646609199091924460443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17543057624530911798561181 6578646609199091924460443)
        ·
          refine ⟨9867969913798637886690665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578646609199091924460443 9867969913798637886690665)
          ·
            refine ⟨7400977435348978415017999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9867969913798637886690665 7400977435348978415017999)
            ·
              refine ⟨11101466153023467622526999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400977435348978415017999 11101466153023467622526999)
              ·
                refine ⟨16652199229535201433790499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101466153023467622526999 16652199229535201433790499)
                ·
                  refine ⟨24978298844302802150685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16652199229535201433790499 24978298844302802150685749)
                  ·
                    refine ⟨2341715516653387701626789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24978298844302802150685749 2341715516653387701626789)
                    ·
                      refine ⟨439071659372510194055023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2341715516653387701626789 439071659372510194055023)
                      ·
                        rfl

theorem cell23_855089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_855089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855089 prefixEnd_855089 := by exact prefixLift 855089
  have htrace : WordTrace (prefixWord ++ tailWord_855089) baseStart_855089 baseEnd_855089 := by
    simpa [prefixWord, tailWord_855089, baseEnd_855089] using wordTrace_append hprefix tailTrace_855089
  have hstable : (prefixWord ++ tailWord_855089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855089).length < 2 ^ (prefixWord ++ tailWord_855089).sum := by decide
  have hdescent : baseEnd_855089 < baseStart_855089 := by decide
  rcases family_descends (prefixWord ++ tailWord_855089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855109 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_855109 : Nat := 118140960795 + 855109 * 2 ^ 59
def prefixEnd_855109 : Nat := 4983230072969 + 3 ^ 40 * 855109 * 2
def baseEnd_855109 : Nat := 439081928985600115804931

theorem tailTrace_855109 : CollatzResearch.WordTrace tailWord_855109 prefixEnd_855109 439081928985600115804931 := by
  unfold tailWord_855109
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188387459093608835392381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792258306062405890261587 31188387459093608835392381)
  ·
    refine ⟨11695645297160103313272143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31188387459093608835392381 11695645297160103313272143)
    ·
      refine ⟨17543467945740154969908215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11695645297160103313272143 17543467945740154969908215)
      ·
        refine ⟨26315201918610232454862323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543467945740154969908215 26315201918610232454862323)
        ·
          refine ⟨39472802877915348682293485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26315201918610232454862323 39472802877915348682293485)
          ·
            refine ⟨14802301079218255755860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39472802877915348682293485 14802301079218255755860057)
            ·
              refine ⟨11101725809413691816895043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14802301079218255755860057 11101725809413691816895043)
              ·
                refine ⟨16652588714120537725342565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101725809413691816895043 16652588714120537725342565)
                ·
                  refine ⟨3122360383897600823501731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16652588714120537725342565 3122360383897600823501731)
                  ·
                    refine ⟨4683540575846401235252597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3122360383897600823501731 4683540575846401235252597)
                    ·
                      refine ⟨439081928985600115804931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4683540575846401235252597 439081928985600115804931)
                      ·
                        rfl

theorem cell23_855109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_855109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855109 prefixEnd_855109 := by exact prefixLift 855109
  have htrace : WordTrace (prefixWord ++ tailWord_855109) baseStart_855109 baseEnd_855109 := by
    simpa [prefixWord, tailWord_855109, baseEnd_855109] using wordTrace_append hprefix tailTrace_855109
  have hstable : (prefixWord ++ tailWord_855109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855109).length < 2 ^ (prefixWord ++ tailWord_855109).sum := by decide
  have hdescent : baseEnd_855109 < baseStart_855109 := by decide
  rcases family_descends (prefixWord ++ tailWord_855109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855119 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_855119 : Nat := 118140960795 + 855119 * 2 ^ 59
def prefixEnd_855119 : Nat := 4983230072969 + 3 ^ 40 * 855119 * 2
def baseEnd_855119 : Nat := 439087063792145076679885

theorem tailTrace_855119 : CollatzResearch.WordTrace tailWord_855119 prefixEnd_855119 439087063792145076679885 := by
  unfold tailWord_855119
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188752189057380543256411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792501459371587028837607 31188752189057380543256411)
  ·
    refine ⟨46783128283586070814884617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31188752189057380543256411 46783128283586070814884617)
    ·
      refine ⟨35087346212689553111163463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46783128283586070814884617 35087346212689553111163463)
      ·
        refine ⟨52631019319034329666745195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35087346212689553111163463 52631019319034329666745195)
        ·
          refine ⟨78946528978551494500117793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52631019319034329666745195 78946528978551494500117793)
          ·
            refine ⟨59209896733913620875088345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78946528978551494500117793 59209896733913620875088345)
            ·
              refine ⟨44407422550435215656316259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59209896733913620875088345 44407422550435215656316259)
              ·
                refine ⟨66611133825652823484474389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44407422550435215656316259 66611133825652823484474389)
                ·
                  refine ⟨3122396898077476100834737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66611133825652823484474389 3122396898077476100834737)
                  ·
                    refine ⟨2341797673558107075626053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122396898077476100834737 2341797673558107075626053)
                    ·
                      refine ⟨439087063792145076679885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2341797673558107075626053 439087063792145076679885)
                      ·
                        rfl

theorem cell23_855119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_855119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855119 prefixEnd_855119 := by exact prefixLift 855119
  have htrace : WordTrace (prefixWord ++ tailWord_855119) baseStart_855119 baseEnd_855119 := by
    simpa [prefixWord, tailWord_855119, baseEnd_855119] using wordTrace_append hprefix tailTrace_855119
  have hstable : (prefixWord ++ tailWord_855119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855119).length < 2 ^ (prefixWord ++ tailWord_855119).sum := by decide
  have hdescent : baseEnd_855119 < baseStart_855119 := by decide
  rcases family_descends (prefixWord ++ tailWord_855119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855134 : List Nat := [4, 4, 1, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_855134 : Nat := 118140960795 + 855134 * 2 ^ 59
def prefixEnd_855134 : Nat := 4983230072969 + 3 ^ 40 * 855134 * 2
def baseEnd_855134 : Nat := 439094766001962517992317

theorem tailTrace_855134 : CollatzResearch.WordTrace tailWord_855134 prefixEnd_855134 439094766001962517992317 := by
  unfold tailWord_855134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898662410500379763131557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20792866189335358736701637 3898662410500379763131557)
  ·
    refine ⟨730999201968821205587167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3898662410500379763131557 730999201968821205587167)
    ·
      refine ⟨1096498802953231808380751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730999201968821205587167 1096498802953231808380751)
      ·
        refine ⟨1644748204429847712571127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096498802953231808380751 1644748204429847712571127)
        ·
          refine ⟨2467122306644771568856691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644748204429847712571127 2467122306644771568856691)
          ·
            refine ⟨3700683459967157353285037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467122306644771568856691 3700683459967157353285037)
            ·
              refine ⟨1387756297487684007481889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700683459967157353285037 1387756297487684007481889)
              ·
                refine ⟨1040817223115763005611417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387756297487684007481889 1040817223115763005611417)
                ·
                  refine ⟨780612917336822254208563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040817223115763005611417 780612917336822254208563)
                  ·
                    refine ⟨1170919376005233381312845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 780612917336822254208563 1170919376005233381312845)
                    ·
                      refine ⟨439094766001962517992317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1170919376005233381312845 439094766001962517992317)
                      ·
                        rfl

theorem cell23_855134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_855134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855134 prefixEnd_855134 := by exact prefixLift 855134
  have htrace : WordTrace (prefixWord ++ tailWord_855134) baseStart_855134 baseEnd_855134 := by
    simpa [prefixWord, tailWord_855134, baseEnd_855134] using wordTrace_append hprefix tailTrace_855134
  have hstable : (prefixWord ++ tailWord_855134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855134).length < 2 ^ (prefixWord ++ tailWord_855134).sum := by decide
  have hdescent : baseEnd_855134 < baseStart_855134 := by decide
  rcases family_descends (prefixWord ++ tailWord_855134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855146 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_855146 : Nat := 118140960795 + 855146 * 2 ^ 59
def prefixEnd_855146 : Nat := 4983230072969 + 3 ^ 40 * 855146 * 2
def baseEnd_855146 : Nat := 48788991974424052338029

theorem tailTrace_855146 : CollatzResearch.WordTrace tailWord_855146 prefixEnd_855146 48788991974424052338029 := by
  unfold tailWord_855146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7797434239989891038622323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20793157973306376102992861 7797434239989891038622323)
  ·
    refine ⟨11696151359984836557933485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7797434239989891038622323 11696151359984836557933485)
    ·
      refine ⟨4386056759994313709225057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11696151359984836557933485 4386056759994313709225057)
      ·
        refine ⟨3289542569995735281918793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4386056759994313709225057 3289542569995735281918793)
        ·
          refine ⟨2467156927496801461439095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3289542569995735281918793 2467156927496801461439095)
          ·
            refine ⟨3700735391245202192158643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467156927496801461439095 3700735391245202192158643)
            ·
              refine ⟨5551103086867803288237965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700735391245202192158643 5551103086867803288237965)
              ·
                refine ⟨2081663657575426233089237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5551103086867803288237965 2081663657575426233089237)
                ·
                  refine ⟨48788991974424052338029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2081663657575426233089237 48788991974424052338029)
                  ·
                    rfl

theorem cell23_855146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_855146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855146 prefixEnd_855146 := by exact prefixLift 855146
  have htrace : WordTrace (prefixWord ++ tailWord_855146) baseStart_855146 baseEnd_855146 := by
    simpa [prefixWord, tailWord_855146, baseEnd_855146] using wordTrace_append hprefix tailTrace_855146
  have hstable : (prefixWord ++ tailWord_855146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855146).length < 2 ^ (prefixWord ++ tailWord_855146).sum := by decide
  have hdescent : baseEnd_855146 < baseStart_855146 := by decide
  rcases family_descends (prefixWord ++ tailWord_855146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855159 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 3, 7]
def baseStart_855159 : Nat := 118140960795 + 855159 * 2 ^ 59
def prefixEnd_855159 : Nat := 4983230072969 + 3 ^ 40 * 855159 * 2
def baseEnd_855159 : Nat := 146369201006108306726567

theorem tailTrace_855159 : CollatzResearch.WordTrace tailWord_855159 prefixEnd_855159 146369201006108306726567 := by
  unfold tailWord_855159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31190211108912467374712531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20793474072608311583141687 31190211108912467374712531)
  ·
    refine ⟨46785316663368701062068797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31190211108912467374712531 46785316663368701062068797)
    ·
      refine ⟨17544493748763262898275799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46785316663368701062068797 17544493748763262898275799)
      ·
        refine ⟨26316740623144894347413699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17544493748763262898275799 26316740623144894347413699)
        ·
          refine ⟨39475110934717341521120549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26316740623144894347413699 39475110934717341521120549)
          ·
            refine ⟨7401583300259501535210103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39475110934717341521120549 7401583300259501535210103)
            ·
              refine ⟨11102374950389252302815155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401583300259501535210103 11102374950389252302815155)
              ·
                refine ⟨16653562425583878454222733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102374950389252302815155 16653562425583878454222733)
                ·
                  refine ⟨6245085909593954420333525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16653562425583878454222733 6245085909593954420333525)
                  ·
                    refine ⟨146369201006108306726567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6245085909593954420333525 146369201006108306726567)
                    ·
                      rfl

theorem cell23_855159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_855159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855159 prefixEnd_855159 := by exact prefixLift 855159
  have htrace : WordTrace (prefixWord ++ tailWord_855159) baseStart_855159 baseEnd_855159 := by
    simpa [prefixWord, tailWord_855159, baseEnd_855159] using wordTrace_append hprefix tailTrace_855159
  have hstable : (prefixWord ++ tailWord_855159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855159).length < 2 ^ (prefixWord ++ tailWord_855159).sum := by decide
  have hdescent : baseEnd_855159 < baseStart_855159 := by decide
  rcases family_descends (prefixWord ++ tailWord_855159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855230 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_855230 : Nat := 118140960795 + 855230 * 2 ^ 59
def prefixEnd_855230 : Nat := 4983230072969 + 3 ^ 40 * 855230 * 2
def baseEnd_855230 : Nat := 439144060144794142391875

theorem tailTrace_855230 : CollatzResearch.WordTrace tailWord_855230 prefixEnd_855230 439144060144794142391875 := by
  unfold tailWord_855230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899100086456905812568393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20795200461103497667031429 3899100086456905812568393)
  ·
    refine ⟨2924325064842679359426295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3899100086456905812568393 2924325064842679359426295)
    ·
      refine ⟨4386487597264019039139443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924325064842679359426295 4386487597264019039139443)
      ·
        refine ⟨6579731395896028558709165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386487597264019039139443 6579731395896028558709165)
        ·
          refine ⟨2467399273461010709515937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6579731395896028558709165 2467399273461010709515937)
          ·
            refine ⟨1850549455095758032136953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467399273461010709515937 1850549455095758032136953)
            ·
              refine ⟨1387912091321818524102715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850549455095758032136953 1387912091321818524102715)
              ·
                refine ⟨2081868136982727786154073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387912091321818524102715 2081868136982727786154073)
                ·
                  refine ⟨1561401102737045839615555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081868136982727786154073 1561401102737045839615555)
                  ·
                    refine ⟨2342101654105568759423333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561401102737045839615555 2342101654105568759423333)
                    ·
                      refine ⟨439144060144794142391875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2342101654105568759423333 439144060144794142391875)
                      ·
                        rfl

theorem cell23_855230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_855230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855230 prefixEnd_855230 := by exact prefixLift 855230
  have htrace : WordTrace (prefixWord ++ tailWord_855230) baseStart_855230 baseEnd_855230 := by
    simpa [prefixWord, tailWord_855230, baseEnd_855230] using wordTrace_append hprefix tailTrace_855230
  have hstable : (prefixWord ++ tailWord_855230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855230).length < 2 ^ (prefixWord ++ tailWord_855230).sum := by decide
  have hdescent : baseEnd_855230 < baseStart_855230 := by decide
  rcases family_descends (prefixWord ++ tailWord_855230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855253 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 6]
def baseStart_855253 : Nat := 118140960795 + 855253 * 2 ^ 59
def prefixEnd_855253 : Nat := 4983230072969 + 3 ^ 40 * 855253 * 2
def baseEnd_855253 : Nat := 48795096688871950267141

theorem tailTrace_855253 : CollatzResearch.WordTrace tailWord_855253 prefixEnd_855253 48795096688871950267141 := by
  unfold tailWord_855253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31193639570571921428634413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20795759713714614285756275 31193639570571921428634413)
  ·
    refine ⟨11697614838964470535737905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31193639570571921428634413 11697614838964470535737905)
    ·
      refine ⟨8773211129223352901803429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11697614838964470535737905 8773211129223352901803429)
      ·
        refine ⟨1644977086729378669088143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8773211129223352901803429 1644977086729378669088143)
        ·
          refine ⟨2467465630094068003632215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644977086729378669088143 2467465630094068003632215)
          ·
            refine ⟨3701198445141102005448323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467465630094068003632215 3701198445141102005448323)
            ·
              refine ⟨5551797667711653008172485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701198445141102005448323 5551797667711653008172485)
              ·
                refine ⟨1040962062695934939032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5551797667711653008172485 1040962062695934939032341)
                ·
                  refine ⟨48795096688871950267141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1040962062695934939032341 48795096688871950267141)
                  ·
                    rfl

theorem cell23_855253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_855253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855253 prefixEnd_855253 := by exact prefixLift 855253
  have htrace : WordTrace (prefixWord ++ tailWord_855253) baseStart_855253 baseEnd_855253 := by
    simpa [prefixWord, tailWord_855253, baseEnd_855253] using wordTrace_append hprefix tailTrace_855253
  have hstable : (prefixWord ++ tailWord_855253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855253).length < 2 ^ (prefixWord ++ tailWord_855253).sum := by decide
  have hdescent : baseEnd_855253 < baseStart_855253 := by decide
  rcases family_descends (prefixWord ++ tailWord_855253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855284 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_855284 : Nat := 118140960795 + 855284 * 2 ^ 59
def prefixEnd_855284 : Nat := 4983230072969 + 3 ^ 40 * 855284 * 2
def baseEnd_855284 : Nat := 439171788100136931116627

theorem tailTrace_855284 : CollatzResearch.WordTrace tailWord_855284 prefixEnd_855284 439171788100136931116627 := by
  unfold tailWord_855284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597385116729806861506453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20796513488973075815341937 15597385116729806861506453)
  ·
    refine ⟨731127427346709696633115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15597385116729806861506453 731127427346709696633115)
    ·
      refine ⟨1096691141020064544949673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731127427346709696633115 1096691141020064544949673)
      ·
        refine ⟨822518355765048408712255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1096691141020064544949673 822518355765048408712255)
        ·
          refine ⟨1233777533647572613068383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822518355765048408712255 1233777533647572613068383)
          ·
            refine ⟨1850666300471358919602575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233777533647572613068383 1850666300471358919602575)
            ·
              refine ⟨2775999450707038379403863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850666300471358919602575 2775999450707038379403863)
              ·
                refine ⟨4163999176060557569105795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775999450707038379403863 4163999176060557569105795)
                ·
                  refine ⟨6245998764090836353658693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163999176060557569105795 6245998764090836353658693)
                  ·
                    refine ⟨1171124768267031816311005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245998764090836353658693 1171124768267031816311005)
                    ·
                      refine ⟨439171788100136931116627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1171124768267031816311005 439171788100136931116627)
                      ·
                        rfl

theorem cell23_855284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_855284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855284 prefixEnd_855284 := by exact prefixLift 855284
  have htrace : WordTrace (prefixWord ++ tailWord_855284) baseStart_855284 baseEnd_855284 := by
    simpa [prefixWord, tailWord_855284, baseEnd_855284] using wordTrace_append hprefix tailTrace_855284
  have hstable : (prefixWord ++ tailWord_855284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855284).length < 2 ^ (prefixWord ++ tailWord_855284).sum := by decide
  have hdescent : baseEnd_855284 < baseStart_855284 := by decide
  rcases family_descends (prefixWord ++ tailWord_855284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855297 : List Nat := [1, 2, 4, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_855297 : Nat := 118140960795 + 855297 * 2 ^ 59
def prefixEnd_855297 : Nat := 4983230072969 + 3 ^ 40 * 855297 * 2
def baseEnd_855297 : Nat := 439178463348645380254067

theorem tailTrace_855297 : CollatzResearch.WordTrace tailWord_855297 prefixEnd_855297 439178463348645380254067 := by
  unfold tailWord_855297
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195244382412516943236145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20796829588275011295490763 31195244382412516943236145)
  ·
    refine ⟨23396433286809387707427109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31195244382412516943236145 23396433286809387707427109)
    ·
      refine ⟨4386831241276760195142583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23396433286809387707427109 4386831241276760195142583)
      ·
        refine ⟨6580246861915140292713875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386831241276760195142583 6580246861915140292713875)
        ·
          refine ⟨9870370292872710439070813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580246861915140292713875 9870370292872710439070813)
          ·
            refine ⟨3701388859827266414651555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9870370292872710439070813 3701388859827266414651555)
            ·
              refine ⟨5552083289740899621977333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701388859827266414651555 5552083289740899621977333)
              ·
                refine ⟨520507808413209339560375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5552083289740899621977333 520507808413209339560375)
                ·
                  refine ⟨780761712619814009340563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520507808413209339560375 780761712619814009340563)
                  ·
                    refine ⟨1171142568929721014010845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 780761712619814009340563 1171142568929721014010845)
                    ·
                      refine ⟨439178463348645380254067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1171142568929721014010845 439178463348645380254067)
                      ·
                        rfl

theorem cell23_855297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_855297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855297 prefixEnd_855297 := by exact prefixLift 855297
  have htrace : WordTrace (prefixWord ++ tailWord_855297) baseStart_855297 baseEnd_855297 := by
    simpa [prefixWord, tailWord_855297, baseEnd_855297] using wordTrace_append hprefix tailTrace_855297
  have hstable : (prefixWord ++ tailWord_855297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855297).length < 2 ^ (prefixWord ++ tailWord_855297).sum := by decide
  have hdescent : baseEnd_855297 < baseStart_855297 := by decide
  rcases family_descends (prefixWord ++ tailWord_855297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855300 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_855300 : Nat := 118140960795 + 855300 * 2 ^ 59
def prefixEnd_855300 : Nat := 4983230072969 + 3 ^ 40 * 855300 * 2
def baseEnd_855300 : Nat := 146393334596869622838851

theorem tailTrace_855300 : CollatzResearch.WordTrace tailWord_855300 prefixEnd_855300 146393334596869622838851 := by
  unfold tailWord_855300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597676900700824227797677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20796902534267765637063569 15597676900700824227797677)
  ·
    refine ⟨5849128837762809085424129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15597676900700824227797677 5849128837762809085424129)
    ·
      refine ⟨4386846628322106814068097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5849128837762809085424129 4386846628322106814068097)
      ·
        refine ⟨3290134971241580110551073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4386846628322106814068097 3290134971241580110551073)
        ·
          refine ⟨2467601228431185082913305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290134971241580110551073 2467601228431185082913305)
          ·
            refine ⟨1850700921323388812184979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467601228431185082913305 1850700921323388812184979)
            ·
              refine ⟨2776051381985083218277469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850700921323388812184979 2776051381985083218277469)
              ·
                refine ⟨1041019268244406206854051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776051381985083218277469 1041019268244406206854051)
                ·
                  refine ⟨1561528902366609310281077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041019268244406206854051 1561528902366609310281077)
                  ·
                    refine ⟨146393334596869622838851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1561528902366609310281077 146393334596869622838851)
                    ·
                      rfl

theorem cell23_855300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_855300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855300 prefixEnd_855300 := by exact prefixLift 855300
  have htrace : WordTrace (prefixWord ++ tailWord_855300) baseStart_855300 baseEnd_855300 := by
    simpa [prefixWord, tailWord_855300, baseEnd_855300] using wordTrace_append hprefix tailTrace_855300
  have hstable : (prefixWord ++ tailWord_855300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855300).length < 2 ^ (prefixWord ++ tailWord_855300).sum := by decide
  have hdescent : baseEnd_855300 < baseStart_855300 := by decide
  rcases family_descends (prefixWord ++ tailWord_855300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855313 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_855313 : Nat := 118140960795 + 855313 * 2 ^ 59
def prefixEnd_855313 : Nat := 4983230072969 + 3 ^ 40 * 855313 * 2
def baseEnd_855313 : Nat := 146395559679705772551331

theorem tailTrace_855313 : CollatzResearch.WordTrace tailWord_855313 prefixEnd_855313 146395559679705772551331 := by
  unfold tailWord_855313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195827950354551675818593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20797218633569701117212395 31195827950354551675818593)
  ·
    refine ⟨23396870962765913756863945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31195827950354551675818593 23396870962765913756863945)
    ·
      refine ⟨17547653222074435317647959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23396870962765913756863945 17547653222074435317647959)
      ·
        refine ⟨26321479833111652976471939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17547653222074435317647959 26321479833111652976471939)
        ·
          refine ⟨39482219749667479464707909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26321479833111652976471939 39482219749667479464707909)
          ·
            refine ⟨7402916203062652399632733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39482219749667479464707909 7402916203062652399632733)
            ·
              refine ⟨2776093576148494649862275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7402916203062652399632733 2776093576148494649862275)
              ·
                refine ⟨4164140364222741974793413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776093576148494649862275 4164140364222741974793413)
                ·
                  refine ⟨780776318291764120273765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4164140364222741974793413 780776318291764120273765)
                  ·
                    refine ⟨146395559679705772551331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780776318291764120273765 146395559679705772551331)
                    ·
                      rfl

theorem cell23_855313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_855313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855313 prefixEnd_855313 := by exact prefixLift 855313
  have htrace : WordTrace (prefixWord ++ tailWord_855313) baseStart_855313 baseEnd_855313 := by
    simpa [prefixWord, tailWord_855313, baseEnd_855313] using wordTrace_append hprefix tailTrace_855313
  have hstable : (prefixWord ++ tailWord_855313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855313).length < 2 ^ (prefixWord ++ tailWord_855313).sum := by decide
  have hdescent : baseEnd_855313 < baseStart_855313 := by decide
  rcases family_descends (prefixWord ++ tailWord_855313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855333 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_855333 : Nat := 118140960795 + 855333 * 2 ^ 59
def prefixEnd_855333 : Nat := 4983230072969 + 3 ^ 40 * 855333 * 2
def baseEnd_855333 : Nat := 439196948652207239403901

theorem tailTrace_855333 : CollatzResearch.WordTrace tailWord_855333 prefixEnd_855333 439196948652207239403901 := by
  unfold tailWord_855333
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196557410282095091546653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20797704940188063394364435 31196557410282095091546653)
  ·
    refine ⟨11698709028855785659329995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31196557410282095091546653 11698709028855785659329995)
    ·
      refine ⟨17548063543283678488994993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11698709028855785659329995 17548063543283678488994993)
      ·
        refine ⟨13161047657462758866746245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17548063543283678488994993 13161047657462758866746245)
        ·
          refine ⟨2467696435774267287514921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13161047657462758866746245 2467696435774267287514921)
          ·
            refine ⟨1850772326830700465636191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467696435774267287514921 1850772326830700465636191)
            ·
              refine ⟨2776158490246050698454287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850772326830700465636191 2776158490246050698454287)
              ·
                refine ⟨4164237735369076047681431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776158490246050698454287 4164237735369076047681431)
                ·
                  refine ⟨6246356603053614071522147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164237735369076047681431 6246356603053614071522147)
                  ·
                    refine ⟨9369534904580421107283221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246356603053614071522147 9369534904580421107283221)
                    ·
                      refine ⟨439196948652207239403901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9369534904580421107283221 439196948652207239403901)
                      ·
                        rfl

theorem cell23_855333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_855333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855333 prefixEnd_855333 := by exact prefixLift 855333
  have htrace : WordTrace (prefixWord ++ tailWord_855333) baseStart_855333 baseEnd_855333 := by
    simpa [prefixWord, tailWord_855333, baseEnd_855333] using wordTrace_append hprefix tailTrace_855333
  have hstable : (prefixWord ++ tailWord_855333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855333).length < 2 ^ (prefixWord ++ tailWord_855333).sum := by decide
  have hdescent : baseEnd_855333 < baseStart_855333 := by decide
  rcases family_descends (prefixWord ++ tailWord_855333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855357 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_855357 : Nat := 118140960795 + 855357 * 2 ^ 59
def prefixEnd_855357 : Nat := 4983230072969 + 3 ^ 40 * 855357 * 2
def baseEnd_855357 : Nat := 439209272187915145503791

theorem tailTrace_855357 : CollatzResearch.WordTrace tailWord_855357 prefixEnd_855357 439209272187915145503791 := by
  unfold tailWord_855357
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197432762195147190420325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20798288508130098126946883 31197432762195147190420325)
  ·
    refine ⟨5849518642911590098203811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31197432762195147190420325 5849518642911590098203811)
    ·
      refine ⟨8774277964367385147305717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849518642911590098203811 8774277964367385147305717)
      ·
        refine ⟨822588559159442357559911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8774277964367385147305717 822588559159442357559911)
        ·
          refine ⟨1233882838739163536339867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822588559159442357559911 1233882838739163536339867)
          ·
            refine ⟨1850824258108745304509801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233882838739163536339867 1850824258108745304509801)
            ·
              refine ⟨1388118193581558978382351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850824258108745304509801 1388118193581558978382351)
              ·
                refine ⟨2082177290372338467573527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388118193581558978382351 2082177290372338467573527)
                ·
                  refine ⟨3123265935558507701360291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082177290372338467573527 3123265935558507701360291)
                  ·
                    refine ⟨4684898903337761552040437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123265935558507701360291 4684898903337761552040437)
                    ·
                      refine ⟨439209272187915145503791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4684898903337761552040437 439209272187915145503791)
                      ·
                        rfl

theorem cell23_855357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_855357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855357 prefixEnd_855357 := by exact prefixLift 855357
  have htrace : WordTrace (prefixWord ++ tailWord_855357) baseStart_855357 baseEnd_855357 := by
    simpa [prefixWord, tailWord_855357, baseEnd_855357] using wordTrace_append hprefix tailTrace_855357
  have hstable : (prefixWord ++ tailWord_855357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855357).length < 2 ^ (prefixWord ++ tailWord_855357).sum := by decide
  have hdescent : baseEnd_855357 < baseStart_855357 := by decide
  rcases family_descends (prefixWord ++ tailWord_855357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855422 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_855422 : Nat := 118140960795 + 855422 * 2 ^ 59
def prefixEnd_855422 : Nat := 4983230072969 + 3 ^ 40 * 855422 * 2
def baseEnd_855422 : Nat := 439242648430457391190993

theorem tailTrace_855422 : CollatzResearch.WordTrace tailWord_855422 prefixEnd_855422 439242648430457391190993 := by
  unfold tailWord_855422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899975438369957911442065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20799869004639775527691013 3899975438369957911442065)
  ·
    refine ⟨2924981578777468433581549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3899975438369957911442065 2924981578777468433581549)
    ·
      refine ⟨1096868092041550662593081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2924981578777468433581549 1096868092041550662593081)
      ·
        refine ⟨822651069031162996944811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1096868092041550662593081 822651069031162996944811)
        ·
          refine ⟨1233976603546744495417217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822651069031162996944811 1233976603546744495417217)
          ·
            refine ⟨925482452660058371562913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233976603546744495417217 925482452660058371562913)
            ·
              refine ⟨694111839495043778672185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925482452660058371562913 694111839495043778672185)
              ·
                refine ⟨520583879621282834004139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694111839495043778672185 520583879621282834004139)
                ·
                  refine ⟨780875819431924251006209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520583879621282834004139 780875819431924251006209)
                  ·
                    refine ⟨585656864573943188254657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 780875819431924251006209 585656864573943188254657)
                    ·
                      refine ⟨439242648430457391190993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585656864573943188254657 439242648430457391190993)
                      ·
                        rfl

theorem cell23_855422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_855422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855422 prefixEnd_855422 := by exact prefixLift 855422
  have htrace : WordTrace (prefixWord ++ tailWord_855422) baseStart_855422 baseEnd_855422 := by
    simpa [prefixWord, tailWord_855422, baseEnd_855422] using wordTrace_append hprefix tailTrace_855422
  have hstable : (prefixWord ++ tailWord_855422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855422).length < 2 ^ (prefixWord ++ tailWord_855422).sum := by decide
  have hdescent : baseEnd_855422 < baseStart_855422 := by decide
  rcases family_descends (prefixWord ++ tailWord_855422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855444 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_855444 : Nat := 118140960795 + 855444 * 2 ^ 59
def prefixEnd_855444 : Nat := 4983230072969 + 3 ^ 40 * 855444 * 2
def baseEnd_855444 : Nat := 439253945004856305115891

theorem tailTrace_855444 : CollatzResearch.WordTrace tailWord_855444 prefixEnd_855444 439253945004856305115891 := by
  unfold tailWord_855444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600302956439980524418693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20800403941919974032558257 15600302956439980524418693)
  ·
    refine ⟨2925056804332496348328505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15600302956439980524418693 2925056804332496348328505)
    ·
      refine ⟨2193792603249372261246379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2925056804332496348328505 2193792603249372261246379)
      ·
        refine ⟨3290688904874058391869569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193792603249372261246379 3290688904874058391869569)
        ·
          refine ⟨2468016678655543793902177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290688904874058391869569 2468016678655543793902177)
          ·
            refine ⟨1851012508991657845426633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468016678655543793902177 1851012508991657845426633)
            ·
              refine ⟨1388259381743743384069975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851012508991657845426633 1388259381743743384069975)
              ·
                refine ⟨2082389072615615076104963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388259381743743384069975 2082389072615615076104963)
                ·
                  refine ⟨3123583608923422614157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082389072615615076104963 3123583608923422614157445)
                  ·
                    refine ⟨585671926673141740154521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3123583608923422614157445 585671926673141740154521)
                    ·
                      refine ⟨439253945004856305115891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585671926673141740154521 439253945004856305115891)
                      ·
                        rfl

theorem cell23_855444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_855444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855444 prefixEnd_855444 := by exact prefixLift 855444
  have htrace : WordTrace (prefixWord ++ tailWord_855444) baseStart_855444 baseEnd_855444 := by
    simpa [prefixWord, tailWord_855444, baseEnd_855444] using wordTrace_append hprefix tailTrace_855444
  have hstable : (prefixWord ++ tailWord_855444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855444).length < 2 ^ (prefixWord ++ tailWord_855444).sum := by decide
  have hdescent : baseEnd_855444 < baseStart_855444 := by decide
  rcases family_descends (prefixWord ++ tailWord_855444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855500 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_855500 : Nat := 118140960795 + 855500 * 2 ^ 59
def prefixEnd_855500 : Nat := 4983230072969 + 3 ^ 40 * 855500 * 2
def baseEnd_855500 : Nat := 439282699921508086015633

theorem tailTrace_855500 : CollatzResearch.WordTrace tailWord_855500 prefixEnd_855500 439282699921508086015633 := by
  unfold tailWord_855500
  simp only [CollatzResearch.WordTrace]
  refine ⟨15601324200338541306437977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20801765600451388408583969 15601324200338541306437977)
  ·
    refine ⟨11700993150253905979828483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15601324200338541306437977 11700993150253905979828483)
    ·
      refine ⟨17551489725380858969742725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11700993150253905979828483 17551489725380858969742725)
      ·
        refine ⟨3290904323508911056826761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17551489725380858969742725 3290904323508911056826761)
        ·
          refine ⟨2468178242631683292620071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290904323508911056826761 2468178242631683292620071)
          ·
            refine ⟨3702267363947524938930107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468178242631683292620071 3702267363947524938930107)
            ·
              refine ⟨5553401045921287408395161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702267363947524938930107 5553401045921287408395161)
              ·
                refine ⟨4165050784440965556296371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553401045921287408395161 4165050784440965556296371)
                ·
                  refine ⟨6247576176661448334444557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165050784440965556296371 6247576176661448334444557)
                  ·
                    refine ⟨2342841066248043125416709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6247576176661448334444557 2342841066248043125416709)
                    ·
                      refine ⟨439282699921508086015633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2342841066248043125416709 439282699921508086015633)
                      ·
                        rfl

theorem cell23_855500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_855500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855500 prefixEnd_855500 := by exact prefixLift 855500
  have htrace : WordTrace (prefixWord ++ tailWord_855500) baseStart_855500 baseEnd_855500 := by
    simpa [prefixWord, tailWord_855500, baseEnd_855500] using wordTrace_append hprefix tailTrace_855500
  have hstable : (prefixWord ++ tailWord_855500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855500).length < 2 ^ (prefixWord ++ tailWord_855500).sum := by decide
  have hdescent : baseEnd_855500 < baseStart_855500 := by decide
  rcases family_descends (prefixWord ++ tailWord_855500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855537 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_855537 : Nat := 118140960795 + 855537 * 2 ^ 59
def prefixEnd_855537 : Nat := 4983230072969 + 3 ^ 40 * 855537 * 2
def baseEnd_855537 : Nat := 439301698705724441252963

theorem tailTrace_855537 : CollatzResearch.WordTrace tailWord_855537 prefixEnd_855537 439301698705724441252963 := by
  unfold tailWord_855537
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203997901543037931972865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20802665267695358621315243 31203997901543037931972865)
  ·
    refine ⟨23402998426157278448979649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31203997901543037931972865 23402998426157278448979649)
    ·
      refine ⟨17552248819617958836734737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23402998426157278448979649 17552248819617958836734737)
      ·
        refine ⟨13164186614713469127551053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17552248819617958836734737 13164186614713469127551053)
        ·
          refine ⟨4936569980517550922831645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13164186614713469127551053 4936569980517550922831645)
          ·
            refine ⟨1851213742694081596061867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4936569980517550922831645 1851213742694081596061867)
            ·
              refine ⟨2776820614041122394092801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851213742694081596061867 2776820614041122394092801)
              ·
                refine ⟨2082615460530841795569601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776820614041122394092801 2082615460530841795569601)
                ·
                  refine ⟨1561961595398131346677201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082615460530841795569601 1561961595398131346677201)
                  ·
                    refine ⟨1171471196548598510007901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561961595398131346677201 1171471196548598510007901)
                    ·
                      refine ⟨439301698705724441252963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1171471196548598510007901 439301698705724441252963)
                      ·
                        rfl

theorem cell23_855537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_855537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855537 prefixEnd_855537 := by exact prefixLift 855537
  have htrace : WordTrace (prefixWord ++ tailWord_855537) baseStart_855537 baseEnd_855537 := by
    simpa [prefixWord, tailWord_855537, baseEnd_855537] using wordTrace_append hprefix tailTrace_855537
  have hstable : (prefixWord ++ tailWord_855537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855537).length < 2 ^ (prefixWord ++ tailWord_855537).sum := by decide
  have hdescent : baseEnd_855537 < baseStart_855537 := by decide
  rcases family_descends (prefixWord ++ tailWord_855537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_855543 : Nat := 118140960795 + 855543 * 2 ^ 59
def prefixEnd_855543 : Nat := 4983230072969 + 3 ^ 40 * 855543 * 2
def baseEnd_855543 : Nat := 439304779589651417777935

theorem tailTrace_855543 : CollatzResearch.WordTrace tailWord_855543 prefixEnd_855543 439304779589651417777935 := by
  unfold tailWord_855543
  simp only [CollatzResearch.WordTrace]
  refine ⟨31204216739521300956691283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20802811159680867304460855 31204216739521300956691283)
  ·
    refine ⟨46806325109281951435036925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31204216739521300956691283 46806325109281951435036925)
    ·
      refine ⟨17552371915980731788138847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46806325109281951435036925 17552371915980731788138847)
      ·
        refine ⟨26328557873971097682208271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17552371915980731788138847 26328557873971097682208271)
        ·
          refine ⟨39492836810956646523312407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26328557873971097682208271 39492836810956646523312407)
          ·
            refine ⟨59239255216434969784968611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39492836810956646523312407 59239255216434969784968611)
            ·
              refine ⟨88858882824652454677452917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59239255216434969784968611 88858882824652454677452917)
              ·
                refine ⟨8330520264811167626011211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88858882824652454677452917 8330520264811167626011211)
                ·
                  refine ⟨12495780397216751439016817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330520264811167626011211 12495780397216751439016817)
                  ·
                    refine ⟨9371835297912563579262613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12495780397216751439016817 9371835297912563579262613)
                    ·
                      refine ⟨439304779589651417777935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9371835297912563579262613 439304779589651417777935)
                      ·
                        rfl

theorem cell23_855543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_855543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855543 prefixEnd_855543 := by exact prefixLift 855543
  have htrace : WordTrace (prefixWord ++ tailWord_855543) baseStart_855543 baseEnd_855543 := by
    simpa [prefixWord, tailWord_855543, baseEnd_855543] using wordTrace_append hprefix tailTrace_855543
  have hstable : (prefixWord ++ tailWord_855543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855543).length < 2 ^ (prefixWord ++ tailWord_855543).sum := by decide
  have hdescent : baseEnd_855543 < baseStart_855543 := by decide
  rcases family_descends (prefixWord ++ tailWord_855543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855594 : List Nat := [3, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_855594 : Nat := 118140960795 + 855594 * 2 ^ 59
def prefixEnd_855594 : Nat := 4983230072969 + 3 ^ 40 * 855594 * 2
def baseEnd_855594 : Nat := 439330967103030718240201

theorem tailTrace_855594 : CollatzResearch.WordTrace tailWord_855594 prefixEnd_855594 439330967103030718240201 := by
  unfold tailWord_855594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801519215584134166699459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20804051241557691111198557 7801519215584134166699459)
  ·
    refine ⟨11702278823376201250049189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7801519215584134166699459 11702278823376201250049189)
    ·
      refine ⟨2194177279383037734384223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11702278823376201250049189 2194177279383037734384223)
      ·
        refine ⟨3291265919074556601576335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194177279383037734384223 3291265919074556601576335)
        ·
          refine ⟨4936898878611834902364503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291265919074556601576335 4936898878611834902364503)
          ·
            refine ⟨7405348317917752353546755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936898878611834902364503 7405348317917752353546755)
            ·
              refine ⟨11108022476876628530320133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405348317917752353546755 11108022476876628530320133)
              ·
                refine ⟨2082754214414367849435025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11108022476876628530320133 2082754214414367849435025)
                ·
                  refine ⟨1562065660810775887076269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2082754214414367849435025 1562065660810775887076269)
                  ·
                    refine ⟨585774622804040957653601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562065660810775887076269 585774622804040957653601)
                    ·
                      refine ⟨439330967103030718240201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585774622804040957653601 439330967103030718240201)
                      ·
                        rfl

theorem cell23_855594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_855594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855594 prefixEnd_855594 := by exact prefixLift 855594
  have htrace : WordTrace (prefixWord ++ tailWord_855594) baseStart_855594 baseEnd_855594 := by
    simpa [prefixWord, tailWord_855594, baseEnd_855594] using wordTrace_append hprefix tailTrace_855594
  have hstable : (prefixWord ++ tailWord_855594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855594).length < 2 ^ (prefixWord ++ tailWord_855594).sum := by decide
  have hdescent : baseEnd_855594 < baseStart_855594 := by decide
  rcases family_descends (prefixWord ++ tailWord_855594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855610 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_855610 : Nat := 118140960795 + 855610 * 2 ^ 59
def prefixEnd_855610 : Nat := 4983230072969 + 3 ^ 40 * 855610 * 2
def baseEnd_855610 : Nat := 439339182793502655640127

theorem tailTrace_855610 : CollatzResearch.WordTrace tailWord_855610 prefixEnd_855610 439339182793502655640127 := by
  unfold tailWord_855610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801665107569642849845071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20804440286852380932920189 7801665107569642849845071)
  ·
    refine ⟨11702497661354464274767607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7801665107569642849845071 11702497661354464274767607)
    ·
      refine ⟨17553746492031696412151411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702497661354464274767607 17553746492031696412151411)
      ·
        refine ⟨26330619738047544618227117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17553746492031696412151411 26330619738047544618227117)
        ·
          refine ⟨9873982401767829231835169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26330619738047544618227117 9873982401767829231835169)
          ·
            refine ⟨7405486801325871923876377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9873982401767829231835169 7405486801325871923876377)
            ·
              refine ⟨5554115100994403942907283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7405486801325871923876377 5554115100994403942907283)
              ·
                refine ⟨8331172651491605914360925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554115100994403942907283 8331172651491605914360925)
                ·
                  refine ⟨3124189744309352217885347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8331172651491605914360925 3124189744309352217885347)
                  ·
                    refine ⟨4686284616464028326828021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124189744309352217885347 4686284616464028326828021)
                    ·
                      refine ⟨439339182793502655640127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4686284616464028326828021 439339182793502655640127)
                      ·
                        rfl

theorem cell23_855610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_855610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855610 prefixEnd_855610 := by exact prefixLift 855610
  have htrace : WordTrace (prefixWord ++ tailWord_855610) baseStart_855610 baseEnd_855610 := by
    simpa [prefixWord, tailWord_855610, baseEnd_855610] using wordTrace_append hprefix tailTrace_855610
  have hstable : (prefixWord ++ tailWord_855610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855610).length < 2 ^ (prefixWord ++ tailWord_855610).sum := by decide
  have hdescent : baseEnd_855610 < baseStart_855610 := by decide
  rcases family_descends (prefixWord ++ tailWord_855610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855617 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_855617 : Nat := 118140960795 + 855617 * 2 ^ 59
def prefixEnd_855617 : Nat := 4983230072969 + 3 ^ 40 * 855617 * 2
def baseEnd_855617 : Nat := 146447592386028042750865

theorem tailTrace_855617 : CollatzResearch.WordTrace tailWord_855617 prefixEnd_855617 146447592386028042750865 := by
  unfold tailWord_855617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31206915741253211594885105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20804610494168807729923403 31206915741253211594885105)
  ·
    refine ⟨23405186805939908696163829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31206915741253211594885105 23405186805939908696163829)
    ·
      refine ⟨2194236263056866440265359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23405186805939908696163829 2194236263056866440265359)
      ·
        refine ⟨3291354394585299660398039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194236263056866440265359 3291354394585299660398039)
        ·
          refine ⟨4937031591877949490597059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291354394585299660398039 4937031591877949490597059)
          ·
            refine ⟨7405547387816924235895589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937031591877949490597059 7405547387816924235895589)
            ·
              refine ⟨1388540135215673294230423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7405547387816924235895589 1388540135215673294230423)
              ·
                refine ⟨2082810202823509941345635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388540135215673294230423 2082810202823509941345635)
                ·
                  refine ⟨3124215304235264912018453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082810202823509941345635 3124215304235264912018453)
                  ·
                    refine ⟨146447592386028042750865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3124215304235264912018453 146447592386028042750865)
                    ·
                      rfl

theorem cell23_855617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_855617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855617 prefixEnd_855617 := by exact prefixLift 855617
  have htrace : WordTrace (prefixWord ++ tailWord_855617) baseStart_855617 baseEnd_855617 := by
    simpa [prefixWord, tailWord_855617, baseEnd_855617] using wordTrace_append hprefix tailTrace_855617
  have hstable : (prefixWord ++ tailWord_855617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855617).length < 2 ^ (prefixWord ++ tailWord_855617).sum := by decide
  have hdescent : baseEnd_855617 < baseStart_855617 := by decide
  rcases family_descends (prefixWord ++ tailWord_855617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855627 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 3]
def baseStart_855627 : Nat := 118140960795 + 855627 * 2 ^ 59
def prefixEnd_855627 : Nat := 4983230072969 + 3 ^ 40 * 855627 * 2
def baseEnd_855627 : Nat := 439347911964629089127549

theorem tailTrace_855627 : CollatzResearch.WordTrace tailWord_855627 prefixEnd_855627 439347911964629089127549 := by
  unfold tailWord_855627
  simp only [CollatzResearch.WordTrace]
  refine ⟨31207280471216983302749135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20804853647477988868499423 31207280471216983302749135)
  ·
    refine ⟨46810920706825474954123703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31207280471216983302749135 46810920706825474954123703)
    ·
      refine ⟨70216381060238212431185555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46810920706825474954123703 70216381060238212431185555)
      ·
        refine ⟨105324571590357318646778333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70216381060238212431185555 105324571590357318646778333)
        ·
          refine ⟨39496714346383994492541875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105324571590357318646778333 39496714346383994492541875)
          ·
            refine ⟨59245071519575991738812813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39496714346383994492541875 59245071519575991738812813)
            ·
              refine ⟨22216901819840996902054805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59245071519575991738812813 22216901819840996902054805)
              ·
                refine ⟨1041417272805046729783819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22216901819840996902054805 1041417272805046729783819)
                ·
                  refine ⟨1562125909207570094675729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041417272805046729783819 1562125909207570094675729)
                  ·
                    refine ⟨1171594431905677571006797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562125909207570094675729 1171594431905677571006797)
                    ·
                      refine ⟨439347911964629089127549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1171594431905677571006797 439347911964629089127549)
                      ·
                        rfl

theorem cell23_855627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 3].length) (baseStart_855627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855627 prefixEnd_855627 := by exact prefixLift 855627
  have htrace : WordTrace (prefixWord ++ tailWord_855627) baseStart_855627 baseEnd_855627 := by
    simpa [prefixWord, tailWord_855627, baseEnd_855627] using wordTrace_append hprefix tailTrace_855627
  have hstable : (prefixWord ++ tailWord_855627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855627).length < 2 ^ (prefixWord ++ tailWord_855627).sum := by decide
  have hdescent : baseEnd_855627 < baseStart_855627 := by decide
  rcases family_descends (prefixWord ++ tailWord_855627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855638 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_855638 : Nat := 118140960795 + 855638 * 2 ^ 59
def prefixEnd_855638 : Nat := 4983230072969 + 3 ^ 40 * 855638 * 2
def baseEnd_855638 : Nat := 146451186750609515363333

theorem tailTrace_855638 : CollatzResearch.WordTrace tailWord_855638 prefixEnd_855638 146451186750609515363333 := by
  unfold tailWord_855638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950480104636070761337473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20805121116118088120933045 1950480104636070761337473)
  ·
    refine ⟨1462860078477053071003105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950480104636070761337473 1462860078477053071003105)
    ·
      refine ⟨1097145058857789803252329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462860078477053071003105 1097145058857789803252329)
      ·
        refine ⟨822858794143342352439247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097145058857789803252329 822858794143342352439247)
        ·
          refine ⟨1234288191215013528658871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822858794143342352439247 1234288191215013528658871)
          ·
            refine ⟨1851432286822520292988307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234288191215013528658871 1851432286822520292988307)
            ·
              refine ⟨2777148430233780439482461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851432286822520292988307 2777148430233780439482461)
              ·
                refine ⟨1041430661337667664805923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2777148430233780439482461 1041430661337667664805923)
                ·
                  refine ⟨1562145992006501497208885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041430661337667664805923 1562145992006501497208885)
                  ·
                    refine ⟨146451186750609515363333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1562145992006501497208885 146451186750609515363333)
                    ·
                      rfl

theorem cell23_855638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_855638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855638 prefixEnd_855638 := by exact prefixLift 855638
  have htrace : WordTrace (prefixWord ++ tailWord_855638) baseStart_855638 baseEnd_855638 := by
    simpa [prefixWord, tailWord_855638, baseEnd_855638] using wordTrace_append hprefix tailTrace_855638
  have hstable : (prefixWord ++ tailWord_855638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855638).length < 2 ^ (prefixWord ++ tailWord_855638).sum := by decide
  have hdescent : baseEnd_855638 < baseStart_855638 := by decide
  rcases family_descends (prefixWord ++ tailWord_855638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855658 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_855658 : Nat := 118140960795 + 855658 * 2 ^ 59
def prefixEnd_855658 : Nat := 4983230072969 + 3 ^ 40 * 855658 * 2
def baseEnd_855658 : Nat := 439363829864918467839907

theorem tailTrace_855658 : CollatzResearch.WordTrace tailWord_855658 prefixEnd_855658 439363829864918467839907 := by
  unfold tailWord_855658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802102783526168899281907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20805607422736450398085085 7802102783526168899281907)
  ·
    refine ⟨11703154175289253348922861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7802102783526168899281907 11703154175289253348922861)
    ·
      refine ⟨4388682815733470005846073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11703154175289253348922861 4388682815733470005846073)
      ·
        refine ⟨3291512111800102504384555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388682815733470005846073 3291512111800102504384555)
        ·
          refine ⟨4937268167700153756576833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291512111800102504384555 4937268167700153756576833)
          ·
            refine ⟨3702951125775115317432625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4937268167700153756576833 3702951125775115317432625)
            ·
              refine ⟨2777213344331336488074469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702951125775115317432625 2777213344331336488074469)
              ·
                refine ⟨520727502062125591513963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2777213344331336488074469 520727502062125591513963)
                ·
                  refine ⟨781091253093188387270945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520727502062125591513963 781091253093188387270945)
                  ·
                    refine ⟨585818439819891290453209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781091253093188387270945 585818439819891290453209)
                    ·
                      refine ⟨439363829864918467839907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585818439819891290453209 439363829864918467839907)
                      ·
                        rfl

theorem cell23_855658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_855658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855658 prefixEnd_855658 := by exact prefixLift 855658
  have htrace : WordTrace (prefixWord ++ tailWord_855658) baseStart_855658 baseEnd_855658 := by
    simpa [prefixWord, tailWord_855658, baseEnd_855658] using wordTrace_append hprefix tailTrace_855658
  have hstable : (prefixWord ++ tailWord_855658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855658).length < 2 ^ (prefixWord ++ tailWord_855658).sum := by decide
  have hdescent : baseEnd_855658 < baseStart_855658 := by decide
  rcases family_descends (prefixWord ++ tailWord_855658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855731 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 2, 2, 2]
def baseStart_855731 : Nat := 118140960795 + 855731 * 2 ^ 59
def prefixEnd_855731 : Nat := 4983230072969 + 3 ^ 40 * 855731 * 2
def baseEnd_855731 : Nat := 439401313952696682227071

theorem tailTrace_855731 : CollatzResearch.WordTrace tailWord_855731 prefixEnd_855731 439401313952696682227071 := by
  unfold tailWord_855731
  simp only [CollatzResearch.WordTrace]
  refine ⟨31211073662840209064535047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20807382441893472709690031 31211073662840209064535047)
  ·
    refine ⟨46816610494260313596802571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31211073662840209064535047 46816610494260313596802571)
    ·
      refine ⟨70224915741390470395203857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46816610494260313596802571 70224915741390470395203857)
      ·
        refine ⟨52668686806042852796402893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70224915741390470395203857 52668686806042852796402893)
        ·
          refine ⟨19750757552266069798651085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52668686806042852796402893 19750757552266069798651085)
          ·
            refine ⟨7406534082099776174494157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19750757552266069798651085 7406534082099776174494157)
            ·
              refine ⟨2777450280787416065435309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7406534082099776174494157 2777450280787416065435309)
              ·
                refine ⟨1041543855295281024538241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2777450280787416065435309 1041543855295281024538241)
                ·
                  refine ⟨781157891471460768403681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1041543855295281024538241 781157891471460768403681)
                  ·
                    refine ⟨585868418603595576302761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781157891471460768403681 585868418603595576302761)
                    ·
                      refine ⟨439401313952696682227071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585868418603595576302761 439401313952696682227071)
                      ·
                        rfl

theorem cell23_855731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2, 2].length) (baseStart_855731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855731 prefixEnd_855731 := by exact prefixLift 855731
  have htrace : WordTrace (prefixWord ++ tailWord_855731) baseStart_855731 baseEnd_855731 := by
    simpa [prefixWord, tailWord_855731, baseEnd_855731] using wordTrace_append hprefix tailTrace_855731
  have hstable : (prefixWord ++ tailWord_855731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855731).length < 2 ^ (prefixWord ++ tailWord_855731).sum := by decide
  have hdescent : baseEnd_855731 < baseStart_855731 := by decide
  rcases family_descends (prefixWord ++ tailWord_855731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855767 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 2, 5]
def baseStart_855767 : Nat := 118140960795 + 855767 * 2 ^ 59
def prefixEnd_855767 : Nat := 4983230072969 + 3 ^ 40 * 855767 * 2
def baseEnd_855767 : Nat := 146473266418752847125635

theorem tailTrace_855767 : CollatzResearch.WordTrace tailWord_855767 prefixEnd_855767 146473266418752847125635 := by
  unfold tailWord_855767
  simp only [CollatzResearch.WordTrace]
  refine ⟨31212386690709787212845555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20808257793806524808563703 31212386690709787212845555)
  ·
    refine ⟨46818580036064680819268333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31212386690709787212845555 46818580036064680819268333)
    ·
      refine ⟨17556967513524255307225625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46818580036064680819268333 17556967513524255307225625)
      ·
        refine ⟨13167725635143191480419219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17556967513524255307225625 13167725635143191480419219)
        ·
          refine ⟨19751588452714787220628829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13167725635143191480419219 19751588452714787220628829)
          ·
            refine ⟨7406845669768045207735811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19751588452714787220628829 7406845669768045207735811)
            ·
              refine ⟨11110268504652067811603717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406845669768045207735811 11110268504652067811603717)
              ·
                refine ⟨2083175344622262714675697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11110268504652067811603717 2083175344622262714675697)
                ·
                  refine ⟨1562381508466697036006773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083175344622262714675697 1562381508466697036006773)
                  ·
                    refine ⟨146473266418752847125635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1562381508466697036006773 146473266418752847125635)
                    ·
                      rfl

theorem cell23_855767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_855767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855767 prefixEnd_855767 := by exact prefixLift 855767
  have htrace : WordTrace (prefixWord ++ tailWord_855767) baseStart_855767 baseEnd_855767 := by
    simpa [prefixWord, tailWord_855767, baseEnd_855767] using wordTrace_append hprefix tailTrace_855767
  have hstable : (prefixWord ++ tailWord_855767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855767).length < 2 ^ (prefixWord ++ tailWord_855767).sum := by decide
  have hdescent : baseEnd_855767 < baseStart_855767 := by decide
  rcases family_descends (prefixWord ++ tailWord_855767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855787 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4]
def baseStart_855787 : Nat := 118140960795 + 855787 * 2 ^ 59
def prefixEnd_855787 : Nat := 4983230072969 + 3 ^ 40 * 855787 * 2
def baseEnd_855787 : Nat := 439430068869348463126813

theorem tailTrace_855787 : CollatzResearch.WordTrace tailWord_855787 prefixEnd_855787 439430068869348463126813 := by
  unfold tailWord_855787
  simp only [CollatzResearch.WordTrace]
  refine ⟨31213116150637330628573615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20808744100424887085715743 31213116150637330628573615)
  ·
    refine ⟨46819674225955995942860423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31213116150637330628573615 46819674225955995942860423)
    ·
      refine ⟨70229511338933993914290635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46819674225955995942860423 70229511338933993914290635)
      ·
        refine ⟨105344267008400990871435953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70229511338933993914290635 105344267008400990871435953)
        ·
          refine ⟨79008200256300743153576965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105344267008400990871435953 79008200256300743153576965)
          ·
            refine ⟨14814037548056389341295681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79008200256300743153576965 14814037548056389341295681)
            ·
              refine ⟨11110528161042292005971761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14814037548056389341295681 11110528161042292005971761)
              ·
                refine ⟨8332896120781719004478821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110528161042292005971761 8332896120781719004478821)
                ·
                  refine ⟨1562418022646572313339779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8332896120781719004478821 1562418022646572313339779)
                  ·
                    refine ⟨2343627033969858470009669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562418022646572313339779 2343627033969858470009669)
                    ·
                      refine ⟨439430068869348463126813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2343627033969858470009669 439430068869348463126813)
                      ·
                        rfl

theorem cell23_855787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 4].length) (baseStart_855787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855787 prefixEnd_855787 := by exact prefixLift 855787
  have htrace : WordTrace (prefixWord ++ tailWord_855787) baseStart_855787 baseEnd_855787 := by
    simpa [prefixWord, tailWord_855787, baseEnd_855787] using wordTrace_append hprefix tailTrace_855787
  have hstable : (prefixWord ++ tailWord_855787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855787).length < 2 ^ (prefixWord ++ tailWord_855787).sum := by decide
  have hdescent : baseEnd_855787 < baseStart_855787 := by decide
  rcases family_descends (prefixWord ++ tailWord_855787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855804 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_855804 : Nat := 118140960795 + 855804 * 2 ^ 59
def prefixEnd_855804 : Nat := 4983230072969 + 3 ^ 40 * 855804 * 2
def baseEnd_855804 : Nat := 439438798040474896614235

theorem tailTrace_855804 : CollatzResearch.WordTrace tailWord_855804 prefixEnd_855804 439438798040474896614235 := by
  unfold tailWord_855804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15606868095787871265971233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20809157461050495021294977 15606868095787871265971233)
  ·
    refine ⟨11705151071840903449478425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15606868095787871265971233 11705151071840903449478425)
    ·
      refine ⟨8778863303880677587108819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11705151071840903449478425 8778863303880677587108819)
      ·
        refine ⟨13168294955821016380663229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8778863303880677587108819 13168294955821016380663229)
        ·
          refine ⟨4938110608432881142748711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13168294955821016380663229 4938110608432881142748711)
          ·
            refine ⟨7407165912649321714123067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938110608432881142748711 7407165912649321714123067)
            ·
              refine ⟨11110748868973982571184601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407165912649321714123067 11110748868973982571184601)
              ·
                refine ⟨8333061651730486928388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110748868973982571184601 8333061651730486928388451)
                ·
                  refine ⟨12499592477595730392582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333061651730486928388451 12499592477595730392582677)
                  ·
                    refine ⟨585918397387299862152313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12499592477595730392582677 585918397387299862152313)
                    ·
                      refine ⟨439438798040474896614235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585918397387299862152313 439438798040474896614235)
                      ·
                        rfl

theorem cell23_855804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_855804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855804 prefixEnd_855804 := by exact prefixLift 855804
  have htrace : WordTrace (prefixWord ++ tailWord_855804) baseStart_855804 baseEnd_855804 := by
    simpa [prefixWord, tailWord_855804, baseEnd_855804] using wordTrace_append hprefix tailTrace_855804
  have hstable : (prefixWord ++ tailWord_855804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855804).length < 2 ^ (prefixWord ++ tailWord_855804).sum := by decide
  have hdescent : baseEnd_855804 < baseStart_855804 := by decide
  rcases family_descends (prefixWord ++ tailWord_855804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855827 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 6]
def baseStart_855827 : Nat := 118140960795 + 855827 * 2 ^ 59
def prefixEnd_855827 : Nat := 4983230072969 + 3 ^ 40 * 855827 * 2
def baseEnd_855827 : Nat := 48827845343947589625181

theorem tailTrace_855827 : CollatzResearch.WordTrace tailWord_855827 prefixEnd_855827 48827845343947589625181 := by
  unfold tailWord_855827
  simp only [CollatzResearch.WordTrace]
  refine ⟨31214575070492417460029735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20809716713661611640019823 31214575070492417460029735)
  ·
    refine ⟨46821862605738626190044603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31214575070492417460029735 46821862605738626190044603)
    ·
      refine ⟨70232793908607939285066905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46821862605738626190044603 70232793908607939285066905)
      ·
        refine ⟨52674595431455954463800179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70232793908607939285066905 52674595431455954463800179)
        ·
          refine ⟨79011893147183931695700269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52674595431455954463800179 79011893147183931695700269)
          ·
            refine ⟨29629459930193974385887601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79011893147183931695700269 29629459930193974385887601)
            ·
              refine ⟨22222094947645480789415701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29629459930193974385887601 22222094947645480789415701)
              ·
                refine ⟨1041660700670881912003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22222094947645480789415701 1041660700670881912003861)
                ·
                  refine ⟨48827845343947589625181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1041660700670881912003861 48827845343947589625181)
                  ·
                    rfl

theorem cell23_855827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 6].length) (baseStart_855827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855827 prefixEnd_855827 := by exact prefixLift 855827
  have htrace : WordTrace (prefixWord ++ tailWord_855827) baseStart_855827 baseEnd_855827 := by
    simpa [prefixWord, tailWord_855827, baseEnd_855827] using wordTrace_append hprefix tailTrace_855827
  have hstable : (prefixWord ++ tailWord_855827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855827).length < 2 ^ (prefixWord ++ tailWord_855827).sum := by decide
  have hdescent : baseEnd_855827 < baseStart_855827 := by decide
  rcases family_descends (prefixWord ++ tailWord_855827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855831 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 3, 4]
def baseStart_855831 : Nat := 118140960795 + 855831 * 2 ^ 59
def prefixEnd_855831 : Nat := 4983230072969 + 3 ^ 40 * 855831 * 2
def baseEnd_855831 : Nat := 146484220672715430325537

theorem tailTrace_855831 : CollatzResearch.WordTrace tailWord_855831 prefixEnd_855831 146484220672715430325537 := by
  unfold tailWord_855831
  simp only [CollatzResearch.WordTrace]
  refine ⟨31214720962477926143175347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20809813974985284095450231 31214720962477926143175347)
  ·
    refine ⟨46822081443716889214763021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31214720962477926143175347 46822081443716889214763021)
    ·
      refine ⟨17558280541393833455536133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46822081443716889214763021 17558280541393833455536133)
      ·
        refine ⟨3292177601511343772913025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17558280541393833455536133 3292177601511343772913025)
        ·
          refine ⟨2469133201133507829684769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292177601511343772913025 2469133201133507829684769)
          ·
            refine ⟨1851849900850130872263577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469133201133507829684769 1851849900850130872263577)
            ·
              refine ⟨1388887425637598154197683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851849900850130872263577 1388887425637598154197683)
              ·
                refine ⟨2083331138456397231296525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388887425637598154197683 2083331138456397231296525)
                ·
                  refine ⟨781249176921148961736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2083331138456397231296525 781249176921148961736197)
                  ·
                    refine ⟨146484220672715430325537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781249176921148961736197 146484220672715430325537)
                    ·
                      rfl

theorem cell23_855831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_855831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855831 prefixEnd_855831 := by exact prefixLift 855831
  have htrace : WordTrace (prefixWord ++ tailWord_855831) baseStart_855831 baseEnd_855831 := by
    simpa [prefixWord, tailWord_855831, baseEnd_855831] using wordTrace_append hprefix tailTrace_855831
  have hstable : (prefixWord ++ tailWord_855831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855831).length < 2 ^ (prefixWord ++ tailWord_855831).sum := by decide
  have hdescent : baseEnd_855831 < baseStart_855831 := by decide
  rcases family_descends (prefixWord ++ tailWord_855831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855881 : List Nat := [1, 2, 1, 1, 2, 4, 3, 2, 2, 3, 2]
def baseStart_855881 : Nat := 118140960795 + 855881 * 2 ^ 59
def prefixEnd_855881 : Nat := 4983230072969 + 3 ^ 40 * 855881 * 2
def baseEnd_855881 : Nat := 439478336050871095351381

theorem tailTrace_855881 : CollatzResearch.WordTrace tailWord_855881 prefixEnd_855881 439478336050871095351381 := by
  unfold tailWord_855881
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216544612296784682495497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20811029741531189788330331 31216544612296784682495497)
  ·
    refine ⟨23412408459222588511871623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31216544612296784682495497 23412408459222588511871623)
    ·
      refine ⟨35118612688833882767807435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23412408459222588511871623 35118612688833882767807435)
      ·
        refine ⟨52677919033250824151711153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35118612688833882767807435 52677919033250824151711153)
        ·
          refine ⟨39508439274938118113783365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52677919033250824151711153 39508439274938118113783365)
          ·
            refine ⟨7407832364050897146334381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39508439274938118113783365 7407832364050897146334381)
            ·
              refine ⟨2777937136519086429875393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7407832364050897146334381 2777937136519086429875393)
              ·
                refine ⟨2083452852389314822406545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777937136519086429875393 2083452852389314822406545)
                ·
                  refine ⟨1562589639291986116804909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083452852389314822406545 1562589639291986116804909)
                  ·
                    refine ⟨585971114734494793801841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562589639291986116804909 585971114734494793801841)
                    ·
                      refine ⟨439478336050871095351381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 585971114734494793801841 439478336050871095351381)
                      ·
                        rfl

theorem cell23_855881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3, 2].length) (baseStart_855881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855881 prefixEnd_855881 := by exact prefixLift 855881
  have htrace : WordTrace (prefixWord ++ tailWord_855881) baseStart_855881 baseEnd_855881 := by
    simpa [prefixWord, tailWord_855881, baseEnd_855881] using wordTrace_append hprefix tailTrace_855881
  have hstable : (prefixWord ++ tailWord_855881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855881).length < 2 ^ (prefixWord ++ tailWord_855881).sum := by decide
  have hdescent : baseEnd_855881 < baseStart_855881 := by decide
  rcases family_descends (prefixWord ++ tailWord_855881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855908 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_855908 : Nat := 118140960795 + 855908 * 2 ^ 59
def prefixEnd_855908 : Nat := 4983230072969 + 3 ^ 40 * 855908 * 2
def baseEnd_855908 : Nat := 146497400009514163237919

theorem tailTrace_855908 : CollatzResearch.WordTrace tailWord_855908 prefixEnd_855908 146497400009514163237919 := by
  unfold tailWord_855908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608764691599484146864189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20811686255465978862485585 15608764691599484146864189)
  ·
    refine ⟨5853286759349806555074071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15608764691599484146864189 5853286759349806555074071)
    ·
      refine ⟨8779930139024709832611107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853286759349806555074071 8779930139024709832611107)
      ·
        refine ⟨13169895208537064748916661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779930139024709832611107 13169895208537064748916661)
        ·
          refine ⟨1234677675800349820210937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13169895208537064748916661 1234677675800349820210937)
          ·
            refine ⟨926008256850262365158203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234677675800349820210937 926008256850262365158203)
            ·
              refine ⟨1389012385275393547737305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926008256850262365158203 1389012385275393547737305)
              ·
                refine ⟨1041759288956545160802979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389012385275393547737305 1041759288956545160802979)
                ·
                  refine ⟨1562638933434817741204469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041759288956545160802979 1562638933434817741204469)
                  ·
                    refine ⟨146497400009514163237919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1562638933434817741204469 146497400009514163237919)
                    ·
                      rfl

theorem cell23_855908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_855908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855908 prefixEnd_855908 := by exact prefixLift 855908
  have htrace : WordTrace (prefixWord ++ tailWord_855908) baseStart_855908 baseEnd_855908 := by
    simpa [prefixWord, tailWord_855908, baseEnd_855908] using wordTrace_append hprefix tailTrace_855908
  have hstable : (prefixWord ++ tailWord_855908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855908).length < 2 ^ (prefixWord ++ tailWord_855908).sum := by decide
  have hdescent : baseEnd_855908 < baseStart_855908 := by decide
  rcases family_descends (prefixWord ++ tailWord_855908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855945 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 1, 2, 2]
def baseStart_855945 : Nat := 118140960795 + 855945 * 2 ^ 59
def prefixEnd_855945 : Nat := 4983230072969 + 3 ^ 40 * 855945 * 2
def baseEnd_855945 : Nat := 439511198812758844951087

theorem tailTrace_855945 : CollatzResearch.WordTrace tailWord_855945 prefixEnd_855945 439511198812758844951087 := by
  unfold tailWord_855945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218878884064923612825289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20812585922709949075216859 31218878884064923612825289)
  ·
    refine ⟨23414159163048692709618967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31218878884064923612825289 23414159163048692709618967)
    ·
      refine ⟨35121238744573039064428451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23414159163048692709618967 35121238744573039064428451)
      ·
        refine ⟨52681858116859558596642677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35121238744573039064428451 52681858116859558596642677)
        ·
          refine ⟨4938924198455583618435251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52681858116859558596642677 4938924198455583618435251)
          ·
            refine ⟨7408386297683375427652877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938924198455583618435251 7408386297683375427652877)
            ·
              refine ⟨2778144861631265785369829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408386297683375427652877 2778144861631265785369829)
              ·
                refine ⟨520902161555862334756843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2778144861631265785369829 520902161555862334756843)
                ·
                  refine ⟨781353242333793502135265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 520902161555862334756843 781353242333793502135265)
                  ·
                    refine ⟨586014931750345126601449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781353242333793502135265 586014931750345126601449)
                    ·
                      refine ⟨439511198812758844951087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586014931750345126601449 439511198812758844951087)
                      ·
                        rfl

theorem cell23_855945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 2, 2].length) (baseStart_855945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_855945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_855945 prefixEnd_855945 := by exact prefixLift 855945
  have htrace : WordTrace (prefixWord ++ tailWord_855945) baseStart_855945 baseEnd_855945 := by
    simpa [prefixWord, tailWord_855945, baseEnd_855945] using wordTrace_append hprefix tailTrace_855945
  have hstable : (prefixWord ++ tailWord_855945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855945).length < 2 ^ (prefixWord ++ tailWord_855945).sum := by decide
  have hdescent : baseEnd_855945 < baseStart_855945 := by decide
  rcases family_descends (prefixWord ++ tailWord_855945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856024 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 7]
def baseStart_856024 : Nat := 118140960795 + 856024 * 2 ^ 59
def prefixEnd_856024 : Nat := 4983230072969 + 3 ^ 40 * 856024 * 2
def baseEnd_856024 : Nat := 48839084864940448429247

theorem tailTrace_856024 : CollatzResearch.WordTrace tailWord_856024 prefixEnd_856024 48839084864940448429247 := by
  unfold tailWord_856024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15610880125389360052475563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20814506833852480069967417 15610880125389360052475563)
  ·
    refine ⟨23416320188084040078713345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15610880125389360052475563 23416320188084040078713345)
    ·
      refine ⟨17562240141063030059035009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23416320188084040078713345 17562240141063030059035009)
      ·
        refine ⟨13171680105797272544276257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17562240141063030059035009 13171680105797272544276257)
        ·
          refine ⟨9878760079347954408207193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13171680105797272544276257 9878760079347954408207193)
          ·
            refine ⟨7409070059510965806155395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9878760079347954408207193 7409070059510965806155395)
            ·
              refine ⟨11113605089266448709233093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409070059510965806155395 11113605089266448709233093)
              ·
                refine ⟨2083800954237459132981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11113605089266448709233093 2083800954237459132981205)
                ·
                  refine ⟨48839084864940448429247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2083800954237459132981205 48839084864940448429247)
                  ·
                    rfl

theorem cell23_856024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_856024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856024 prefixEnd_856024 := by exact prefixLift 856024
  have htrace : WordTrace (prefixWord ++ tailWord_856024) baseStart_856024 baseEnd_856024 := by
    simpa [prefixWord, tailWord_856024, baseEnd_856024] using wordTrace_append hprefix tailTrace_856024
  have hstable : (prefixWord ++ tailWord_856024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856024).length < 2 ^ (prefixWord ++ tailWord_856024).sum := by decide
  have hdescent : baseEnd_856024 < baseStart_856024 := by decide
  rcases family_descends (prefixWord ++ tailWord_856024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856091 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 6, 2]
def baseStart_856091 : Nat := 118140960795 + 856091 * 2 ^ 59
def prefixEnd_856091 : Nat := 4983230072969 + 3 ^ 40 * 856091 * 2
def baseEnd_856091 : Nat := 439586166988315273725415

theorem tailTrace_856091 : CollatzResearch.WordTrace tailWord_856091 prefixEnd_856091 439586166988315273725415 := by
  unfold tailWord_856091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31224203941535990547640127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20816135961023993698426751 31224203941535990547640127)
  ·
    refine ⟨46836305912303985821460191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31224203941535990547640127 46836305912303985821460191)
    ·
      refine ⟨70254458868455978732190287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46836305912303985821460191 70254458868455978732190287)
      ·
        refine ⟨105381688302683968098285431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70254458868455978732190287 105381688302683968098285431)
        ·
          refine ⟨158072532454025952147428147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105381688302683968098285431 158072532454025952147428147)
          ·
            refine ⟨237108798681038928221142221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158072532454025952147428147 237108798681038928221142221)
            ·
              refine ⟨88915799505389598082928333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237108798681038928221142221 88915799505389598082928333)
              ·
                refine ⟨33343424814521099281098125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88915799505389598082928333 33343424814521099281098125)
                ·
                  refine ⟨12503784305445412230411797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33343424814521099281098125 12503784305445412230411797)
                  ·
                    refine ⟨586114889317753698300553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12503784305445412230411797 586114889317753698300553)
                    ·
                      refine ⟨439586166988315273725415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586114889317753698300553 439586166988315273725415)
                      ·
                        rfl

theorem cell23_856091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6, 2].length) (baseStart_856091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856091 prefixEnd_856091 := by exact prefixLift 856091
  have htrace : WordTrace (prefixWord ++ tailWord_856091) baseStart_856091 baseEnd_856091 := by
    simpa [prefixWord, tailWord_856091, baseEnd_856091] using wordTrace_append hprefix tailTrace_856091
  have hstable : (prefixWord ++ tailWord_856091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856091).length < 2 ^ (prefixWord ++ tailWord_856091).sum := by decide
  have hdescent : baseEnd_856091 < baseStart_856091 := by decide
  rcases family_descends (prefixWord ++ tailWord_856091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856111 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3]
def baseStart_856111 : Nat := 118140960795 + 856111 * 2 ^ 59
def prefixEnd_856111 : Nat := 4983230072969 + 3 ^ 40 * 856111 * 2
def baseEnd_856111 : Nat := 439596436601405195475323

theorem tailTrace_856111 : CollatzResearch.WordTrace tailWord_856111 prefixEnd_856111 439596436601405195475323 := by
  unfold tailWord_856111
  simp only [CollatzResearch.WordTrace]
  refine ⟨31224933401463533963368187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20816622267642355975578791 31224933401463533963368187)
  ·
    refine ⟨46837400102195300945052281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31224933401463533963368187 46837400102195300945052281)
    ·
      refine ⟨35128050076646475708789211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46837400102195300945052281 35128050076646475708789211)
      ·
        refine ⟨52692075114969713563183817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35128050076646475708789211 52692075114969713563183817)
        ·
          refine ⟨39519056336227285172387863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52692075114969713563183817 39519056336227285172387863)
          ·
            refine ⟨59278584504340927758581795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39519056336227285172387863 59278584504340927758581795)
            ·
              refine ⟨88917876756511391637872693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59278584504340927758581795 88917876756511391637872693)
              ·
                refine ⟨8336050945922942966050565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88917876756511391637872693 8336050945922942966050565)
                ·
                  refine ⟨1563009552360551806134481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8336050945922942966050565 1563009552360551806134481)
                  ·
                    refine ⟨1172257164270413854600861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563009552360551806134481 1172257164270413854600861)
                    ·
                      refine ⟨439596436601405195475323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1172257164270413854600861 439596436601405195475323)
                      ·
                        rfl

theorem cell23_856111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_856111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856111 prefixEnd_856111 := by exact prefixLift 856111
  have htrace : WordTrace (prefixWord ++ tailWord_856111) baseStart_856111 baseEnd_856111 := by
    simpa [prefixWord, tailWord_856111, baseEnd_856111] using wordTrace_append hprefix tailTrace_856111
  have hstable : (prefixWord ++ tailWord_856111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856111).length < 2 ^ (prefixWord ++ tailWord_856111).sum := by decide
  have hdescent : baseEnd_856111 < baseStart_856111 := by decide
  rcases family_descends (prefixWord ++ tailWord_856111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856175 : List Nat := [1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 3]
def baseStart_856175 : Nat := 118140960795 + 856175 * 2 ^ 59
def prefixEnd_856175 : Nat := 4983230072969 + 3 ^ 40 * 856175 * 2
def baseEnd_856175 : Nat := 439629299363292945075029

theorem tailTrace_856175 : CollatzResearch.WordTrace tailWord_856175 prefixEnd_856175 439629299363292945075029 := by
  unfold tailWord_856175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31227267673231672893697979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20818178448821115262465319 31227267673231672893697979)
  ·
    refine ⟨46840901509847509340546969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31227267673231672893697979 46840901509847509340546969)
    ·
      refine ⟨35130676132385632005410227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46840901509847509340546969 35130676132385632005410227)
      ·
        refine ⟨52696014198578448008115341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35130676132385632005410227 52696014198578448008115341)
        ·
          refine ⟨19761005324466918003043253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52696014198578448008115341 19761005324466918003043253)
          ·
            refine ⟨1852594249168773562785305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19761005324466918003043253 1852594249168773562785305)
            ·
              refine ⟨1389445686876580172088979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852594249168773562785305 1389445686876580172088979)
              ·
                refine ⟨2084168530314870258133469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389445686876580172088979 2084168530314870258133469)
                ·
                  refine ⟨781563198868076346800051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2084168530314870258133469 781563198868076346800051)
                  ·
                    refine ⟨1172344798302114520200077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781563198868076346800051 1172344798302114520200077)
                    ·
                      refine ⟨439629299363292945075029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1172344798302114520200077 439629299363292945075029)
                      ·
                        rfl

theorem cell23_856175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 3].length) (baseStart_856175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856175 prefixEnd_856175 := by exact prefixLift 856175
  have htrace : WordTrace (prefixWord ++ tailWord_856175) baseStart_856175 baseEnd_856175 := by
    simpa [prefixWord, tailWord_856175, baseEnd_856175] using wordTrace_append hprefix tailTrace_856175
  have hstable : (prefixWord ++ tailWord_856175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856175).length < 2 ^ (prefixWord ++ tailWord_856175).sum := by decide
  have hdescent : baseEnd_856175 < baseStart_856175 := by decide
  rcases family_descends (prefixWord ++ tailWord_856175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856201 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_856201 : Nat := 118140960795 + 856201 * 2 ^ 59
def prefixEnd_856201 : Nat := 4983230072969 + 3 ^ 40 * 856201 * 2
def baseEnd_856201 : Nat := 439642649860309843349909

theorem tailTrace_856201 : CollatzResearch.WordTrace tailWord_856201 prefixEnd_856201 439642649860309843349909 := by
  unfold tailWord_856201
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228215971137479334144457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20818810647424986222762971 31228215971137479334144457)
  ·
    refine ⟨23421161978353109500608343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31228215971137479334144457 23421161978353109500608343)
    ·
      refine ⟨35131742967529664250912515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23421161978353109500608343 35131742967529664250912515)
      ·
        refine ⟨52697614451294496376368773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35131742967529664250912515 52697614451294496376368773)
        ·
          refine ⟨9880802709617718070569145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52697614451294496376368773 9880802709617718070569145)
          ·
            refine ⟨7410602032213288552926859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9880802709617718070569145 7410602032213288552926859)
            ·
              refine ⟨11115903048319932829390289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410602032213288552926859 11115903048319932829390289)
              ·
                refine ⟨8336927286239949622042717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115903048319932829390289 8336927286239949622042717)
                ·
                  refine ⟨3126347732339981108266019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8336927286239949622042717 3126347732339981108266019)
                  ·
                    refine ⟨4689521598509971662399029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3126347732339981108266019 4689521598509971662399029)
                    ·
                      refine ⟨439642649860309843349909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4689521598509971662399029 439642649860309843349909)
                      ·
                        rfl

theorem cell23_856201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_856201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856201 prefixEnd_856201 := by exact prefixLift 856201
  have htrace : WordTrace (prefixWord ++ tailWord_856201) baseStart_856201 baseEnd_856201 := by
    simpa [prefixWord, tailWord_856201, baseEnd_856201] using wordTrace_append hprefix tailTrace_856201
  have hstable : (prefixWord ++ tailWord_856201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856201).length < 2 ^ (prefixWord ++ tailWord_856201).sum := by decide
  have hdescent : baseEnd_856201 < baseStart_856201 := by decide
  rcases family_descends (prefixWord ++ tailWord_856201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856211 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_856211 : Nat := 118140960795 + 856211 * 2 ^ 59
def prefixEnd_856211 : Nat := 4983230072969 + 3 ^ 40 * 856211 * 2
def baseEnd_856211 : Nat := 439647784666854804224863

theorem tailTrace_856211 : CollatzResearch.WordTrace tailWord_856211 prefixEnd_856211 439647784666854804224863 := by
  unfold tailWord_856211
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228580701101251042008487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20819053800734167361338991 31228580701101251042008487)
  ·
    refine ⟨46842871051651876563012731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31228580701101251042008487 46842871051651876563012731)
    ·
      refine ⟨70264306577477814844519097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46842871051651876563012731 70264306577477814844519097)
      ·
        refine ⟨52698229933108361133389323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70264306577477814844519097 52698229933108361133389323)
        ·
          refine ⟨79047344899662541700083985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52698229933108361133389323 79047344899662541700083985)
          ·
            refine ⟨59285508674746906275062989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79047344899662541700083985 59285508674746906275062989)
            ·
              refine ⟨22232065753030089853148621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59285508674746906275062989 22232065753030089853148621)
              ·
                refine ⟨8337024657386283694930733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22232065753030089853148621 8337024657386283694930733)
                ·
                  refine ⟨3126384246519856385599025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8337024657386283694930733 3126384246519856385599025)
                  ·
                    refine ⟨2344788184889892289199269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126384246519856385599025 2344788184889892289199269)
                    ·
                      refine ⟨439647784666854804224863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2344788184889892289199269 439647784666854804224863)
                      ·
                        rfl

theorem cell23_856211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_856211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856211 prefixEnd_856211 := by exact prefixLift 856211
  have htrace : WordTrace (prefixWord ++ tailWord_856211) baseStart_856211 baseEnd_856211 := by
    simpa [prefixWord, tailWord_856211, baseEnd_856211] using wordTrace_append hprefix tailTrace_856211
  have hstable : (prefixWord ++ tailWord_856211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856211).length < 2 ^ (prefixWord ++ tailWord_856211).sum := by decide
  have hdescent : baseEnd_856211 < baseStart_856211 := by decide
  rcases family_descends (prefixWord ++ tailWord_856211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856221 : List Nat := [1, 4, 2, 1, 1, 3, 11]
def baseStart_856221 : Nat := 118140960795 + 856221 * 2 ^ 59
def prefixEnd_856221 : Nat := 4983230072969 + 3 ^ 40 * 856221 * 2
def baseEnd_856221 : Nat := 5427813820659256359257

theorem tailTrace_856221 : CollatzResearch.WordTrace tailWord_856221 prefixEnd_856221 5427813820659256359257 := by
  unfold tailWord_856221
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228945431065022749872517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20819296954043348499915011 31228945431065022749872517)
  ·
    refine ⟨5855427268324691765601097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31228945431065022749872517 5855427268324691765601097)
    ·
      refine ⟨4391570451243518824200823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855427268324691765601097 4391570451243518824200823)
      ·
        refine ⟨6587355676865278236301235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391570451243518824200823 6587355676865278236301235)
        ·
          refine ⟨9881033515297917354451853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587355676865278236301235 9881033515297917354451853)
          ·
            refine ⟨3705387568236719007919445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9881033515297917354451853 3705387568236719007919445)
            ·
              refine ⟨5427813820659256359257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3705387568236719007919445 5427813820659256359257)
              ·
                rfl

theorem cell23_856221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 11].length) (baseStart_856221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856221 prefixEnd_856221 := by exact prefixLift 856221
  have htrace : WordTrace (prefixWord ++ tailWord_856221) baseStart_856221 baseEnd_856221 := by
    simpa [prefixWord, tailWord_856221, baseEnd_856221] using wordTrace_append hprefix tailTrace_856221
  have hstable : (prefixWord ++ tailWord_856221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856221).length < 2 ^ (prefixWord ++ tailWord_856221).sum := by decide
  have hdescent : baseEnd_856221 < baseStart_856221 := by decide
  rcases family_descends (prefixWord ++ tailWord_856221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856226 : List Nat := [3, 3, 1, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_856226 : Nat := 118140960795 + 856226 * 2 ^ 59
def prefixEnd_856226 : Nat := 4983230072969 + 3 ^ 40 * 856226 * 2
def baseEnd_856226 : Nat := 439655486876672245537295

theorem tailTrace_856226 : CollatzResearch.WordTrace tailWord_856226 prefixEnd_856226 439655486876672245537295 := by
  unfold tailWord_856226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807281949011727150951133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20819418530697939069203021 7807281949011727150951133)
  ·
    refine ⟨2927730730879397681606675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7807281949011727150951133 2927730730879397681606675)
    ·
      refine ⟨4391596096319096522410013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927730730879397681606675 4391596096319096522410013)
      ·
        refine ⟨1646848536119661195903755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4391596096319096522410013 1646848536119661195903755)
        ·
          refine ⟨2470272804179491793855633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646848536119661195903755 2470272804179491793855633)
          ·
            refine ⟨1852704603134618845391725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470272804179491793855633 1852704603134618845391725)
            ·
              refine ⟨694764226175482067021897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852704603134618845391725 694764226175482067021897)
              ·
                refine ⟨521073169631611550266423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694764226175482067021897 521073169631611550266423)
                ·
                  refine ⟨781609754447417325399635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521073169631611550266423 781609754447417325399635)
                  ·
                    refine ⟨1172414631671125988099453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 781609754447417325399635 1172414631671125988099453)
                    ·
                      refine ⟨439655486876672245537295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1172414631671125988099453 439655486876672245537295)
                      ·
                        rfl

theorem cell23_856226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_856226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856226 prefixEnd_856226 := by exact prefixLift 856226
  have htrace : WordTrace (prefixWord ++ tailWord_856226) baseStart_856226 baseEnd_856226 := by
    simpa [prefixWord, tailWord_856226, baseEnd_856226] using wordTrace_append hprefix tailTrace_856226
  have hstable : (prefixWord ++ tailWord_856226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856226).length < 2 ^ (prefixWord ++ tailWord_856226).sum := by decide
  have hdescent : baseEnd_856226 < baseStart_856226 := by decide
  rcases family_descends (prefixWord ++ tailWord_856226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856248 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_856248 : Nat := 118140960795 + 856248 * 2 ^ 59
def prefixEnd_856248 : Nat := 4983230072969 + 3 ^ 40 * 856248 * 2
def baseEnd_856248 : Nat := 439666783451071159462193

theorem tailTrace_856248 : CollatzResearch.WordTrace tailWord_856248 prefixEnd_856248 439666783451071159462193 := by
  unfold tailWord_856248
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614965100983603180552699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20819953467978137574070265 15614965100983603180552699)
  ·
    refine ⟨23422447651475404770829049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15614965100983603180552699 23422447651475404770829049)
    ·
      refine ⟨17566835738606553578121787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23422447651475404770829049 17566835738606553578121787)
      ·
        refine ⟨26350253607909830367182681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566835738606553578121787 26350253607909830367182681)
        ·
          refine ⟨19762690205932372775387011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26350253607909830367182681 19762690205932372775387011)
          ·
            refine ⟨29644035308898559163080517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762690205932372775387011 29644035308898559163080517)
            ·
              refine ⟨5558256620418479843077597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29644035308898559163080517 5558256620418479843077597)
              ·
                refine ⟨2084346232656929941154099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558256620418479843077597 2084346232656929941154099)
                ·
                  refine ⟨3126519348985394911731149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084346232656929941154099 3126519348985394911731149)
                  ·
                    refine ⟨1172444755869523091899181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3126519348985394911731149 1172444755869523091899181)
                    ·
                      refine ⟨439666783451071159462193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1172444755869523091899181 439666783451071159462193)
                      ·
                        rfl

theorem cell23_856248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_856248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856248 prefixEnd_856248 := by exact prefixLift 856248
  have htrace : WordTrace (prefixWord ++ tailWord_856248) baseStart_856248 baseEnd_856248 := by
    simpa [prefixWord, tailWord_856248, baseEnd_856248] using wordTrace_append hprefix tailTrace_856248
  have hstable : (prefixWord ++ tailWord_856248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856248).length < 2 ^ (prefixWord ++ tailWord_856248).sum := by decide
  have hdescent : baseEnd_856248 < baseStart_856248 := by decide
  rcases family_descends (prefixWord ++ tailWord_856248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856261 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_856261 : Nat := 118140960795 + 856261 * 2 ^ 59
def prefixEnd_856261 : Nat := 4983230072969 + 3 ^ 40 * 856261 * 2
def baseEnd_856261 : Nat := 439673458699579608599633

theorem tailTrace_856261 : CollatzResearch.WordTrace tailWord_856261 prefixEnd_856261 439673458699579608599633 := by
  unfold tailWord_856261
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230404350920109581328637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20820269567280073054219091 31230404350920109581328637)
  ·
    refine ⟨11711401631595041092998239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31230404350920109581328637 11711401631595041092998239)
    ·
      refine ⟨17567102447392561639497359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711401631595041092998239 17567102447392561639497359)
      ·
        refine ⟨26350653671088842459246039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17567102447392561639497359 26350653671088842459246039)
        ·
          refine ⟨39525980506633263688869059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26350653671088842459246039 39525980506633263688869059)
          ·
            refine ⟨59288970759949895533303589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39525980506633263688869059 59288970759949895533303589)
            ·
              refine ⟨11116682017490605412494423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59288970759949895533303589 11116682017490605412494423)
              ·
                refine ⟨16675023026235908118741635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116682017490605412494423 16675023026235908118741635)
                ·
                  refine ⟨25012534539353862178112453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16675023026235908118741635 25012534539353862178112453)
                  ·
                    refine ⟨4689850226128849158396085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25012534539353862178112453 4689850226128849158396085)
                    ·
                      refine ⟨439673458699579608599633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4689850226128849158396085 439673458699579608599633)
                      ·
                        rfl

theorem cell23_856261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_856261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856261 prefixEnd_856261 := by exact prefixLift 856261
  have htrace : WordTrace (prefixWord ++ tailWord_856261) baseStart_856261 baseEnd_856261 := by
    simpa [prefixWord, tailWord_856261, baseEnd_856261] using wordTrace_append hprefix tailTrace_856261
  have hstable : (prefixWord ++ tailWord_856261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856261).length < 2 ^ (prefixWord ++ tailWord_856261).sum := by decide
  have hdescent : baseEnd_856261 < baseStart_856261 := by decide
  rcases family_descends (prefixWord ++ tailWord_856261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856298 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_856298 : Nat := 118140960795 + 856298 * 2 ^ 59
def prefixEnd_856298 : Nat := 4983230072969 + 3 ^ 40 * 856298 * 2
def baseEnd_856298 : Nat := 146564152494598654612321

theorem tailTrace_856298 : CollatzResearch.WordTrace tailWord_856298 prefixEnd_856298 146564152494598654612321 := by
  unfold tailWord_856298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807938462946516225106387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20821169234524043266950365 7807938462946516225106387)
  ·
    refine ⟨11711907694419774337659581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807938462946516225106387 11711907694419774337659581)
    ·
      refine ⟨4391965385407415376622343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11711907694419774337659581 4391965385407415376622343)
      ·
        refine ⟨6587948078111123064933515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391965385407415376622343 6587948078111123064933515)
        ·
          refine ⟨9881922117166684597400273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587948078111123064933515 9881922117166684597400273)
          ·
            refine ⟨7411441587875013448050205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9881922117166684597400273 7411441587875013448050205)
            ·
              refine ⟨2779290595453130043018827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7411441587875013448050205 2779290595453130043018827)
              ·
                refine ⟨4168935893179695064528241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779290595453130043018827 4168935893179695064528241)
                ·
                  refine ⟨3126701919884771298396181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168935893179695064528241 3126701919884771298396181)
                  ·
                    refine ⟨146564152494598654612321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3126701919884771298396181 146564152494598654612321)
                    ·
                      rfl

theorem cell23_856298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_856298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856298 prefixEnd_856298 := by exact prefixLift 856298
  have htrace : WordTrace (prefixWord ++ tailWord_856298) baseStart_856298 baseEnd_856298 := by
    simpa [prefixWord, tailWord_856298, baseEnd_856298] using wordTrace_append hprefix tailTrace_856298
  have hstable : (prefixWord ++ tailWord_856298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856298).length < 2 ^ (prefixWord ++ tailWord_856298).sum := by decide
  have hdescent : baseEnd_856298 < baseStart_856298 := by decide
  rcases family_descends (prefixWord ++ tailWord_856298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856305 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 1, 4, 2]
def baseStart_856305 : Nat := 118140960795 + 856305 * 2 ^ 59
def prefixEnd_856305 : Nat := 4983230072969 + 3 ^ 40 * 856305 * 2
def baseEnd_856305 : Nat := 439696051848377436449431

theorem tailTrace_856305 : CollatzResearch.WordTrace tailWord_856305 prefixEnd_856305 439696051848377436449431 := by
  unfold tailWord_856305
  simp only [CollatzResearch.WordTrace]
  refine ⟨31232009162760705095930369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20821339441840470063953579 31232009162760705095930369)
  ·
    refine ⟨23424006872070528821947777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31232009162760705095930369 23424006872070528821947777)
    ·
      refine ⟨17568005154052896616460833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23424006872070528821947777 17568005154052896616460833)
      ·
        refine ⟨13176003865539672462345625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17568005154052896616460833 13176003865539672462345625)
        ·
          refine ⟨9882002899154754346759219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13176003865539672462345625 9882002899154754346759219)
          ·
            refine ⟨14823004348732131520138829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882002899154754346759219 14823004348732131520138829)
            ·
              refine ⟨5558626630774549320052061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14823004348732131520138829 5558626630774549320052061)
              ·
                refine ⟨2084484986540455995019523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558626630774549320052061 2084484986540455995019523)
                ·
                  refine ⟨3126727479810683992529285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084484986540455995019523 3126727479810683992529285)
                  ·
                    refine ⟨586261402464503248599241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126727479810683992529285 586261402464503248599241)
                    ·
                      refine ⟨439696051848377436449431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586261402464503248599241 439696051848377436449431)
                      ·
                        rfl

theorem cell23_856305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_856305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856305 prefixEnd_856305 := by exact prefixLift 856305
  have htrace : WordTrace (prefixWord ++ tailWord_856305) baseStart_856305 baseEnd_856305 := by
    simpa [prefixWord, tailWord_856305, baseEnd_856305] using wordTrace_append hprefix tailTrace_856305
  have hstable : (prefixWord ++ tailWord_856305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856305).length < 2 ^ (prefixWord ++ tailWord_856305).sum := by decide
  have hdescent : baseEnd_856305 < baseStart_856305 := by decide
  rcases family_descends (prefixWord ++ tailWord_856305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856356 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_856356 : Nat := 118140960795 + 856356 * 2 ^ 59
def prefixEnd_856356 : Nat := 4983230072969 + 3 ^ 40 * 856356 * 2
def baseEnd_856356 : Nat := 439722239361756736911697

theorem tailTrace_856356 : CollatzResearch.WordTrace tailWord_856356 prefixEnd_856356 439722239361756736911697 := by
  unfold tailWord_856356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616934642787970403018461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20822579523717293870691281 15616934642787970403018461)
  ·
    refine ⟨5856350491045488901131923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15616934642787970403018461 5856350491045488901131923)
    ·
      refine ⟨8784525736568233351697885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856350491045488901131923 8784525736568233351697885)
      ·
        refine ⟨3294197151213087506886707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8784525736568233351697885 3294197151213087506886707)
        ·
          refine ⟨4941295726819631260330061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294197151213087506886707 4941295726819631260330061)
          ·
            refine ⟨1852985897557361722623773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4941295726819631260330061 1852985897557361722623773)
            ·
              refine ⟨694869711584010645983915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852985897557361722623773 694869711584010645983915)
              ·
                refine ⟨1042304567376015968975873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694869711584010645983915 1042304567376015968975873)
                ·
                  refine ⟨781728425532011976731905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042304567376015968975873 781728425532011976731905)
                  ·
                    refine ⟨586296319149008982548929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781728425532011976731905 586296319149008982548929)
                    ·
                      refine ⟨439722239361756736911697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586296319149008982548929 439722239361756736911697)
                      ·
                        rfl

theorem cell23_856356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_856356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856356 prefixEnd_856356 := by exact prefixLift 856356
  have htrace : WordTrace (prefixWord ++ tailWord_856356) baseStart_856356 baseEnd_856356 := by
    simpa [prefixWord, tailWord_856356, baseEnd_856356] using wordTrace_append hprefix tailTrace_856356
  have hstable : (prefixWord ++ tailWord_856356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856356).length < 2 ^ (prefixWord ++ tailWord_856356).sum := by decide
  have hdescent : baseEnd_856356 < baseStart_856356 := by decide
  rcases family_descends (prefixWord ++ tailWord_856356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856395 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 2, 4, 2]
def baseStart_856395 : Nat := 118140960795 + 856395 * 2 ^ 59
def prefixEnd_856395 : Nat := 4983230072969 + 3 ^ 40 * 856395 * 2
def baseEnd_856395 : Nat := 439742265107282084324017

theorem tailTrace_856395 : CollatzResearch.WordTrace tailWord_856395 prefixEnd_856395 439742265107282084324017 := by
  unfold tailWord_856395
  simp only [CollatzResearch.WordTrace]
  refine ⟨31235291732434650466706639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20823527821623100311137759 31235291732434650466706639)
  ·
    refine ⟨46852937598651975700059959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31235291732434650466706639 46852937598651975700059959)
    ·
      refine ⟨70279406397977963550089939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46852937598651975700059959 70279406397977963550089939)
      ·
        refine ⟨105419109596966945325134909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70279406397977963550089939 105419109596966945325134909)
        ·
          refine ⟨39532166098862604496925591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105419109596966945325134909 39532166098862604496925591)
          ·
            refine ⟨59298249148293906745388387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39532166098862604496925591 59298249148293906745388387)
            ·
              refine ⟨88947373722440860118082581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59298249148293906745388387 88947373722440860118082581)
              ·
                refine ⟨4169408143239415318035121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88947373722440860118082581 4169408143239415318035121)
                ·
                  refine ⟨3127056107429561488526341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169408143239415318035121 3127056107429561488526341)
                  ·
                    refine ⟨586323020143042779098689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127056107429561488526341 586323020143042779098689)
                    ·
                      refine ⟨439742265107282084324017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586323020143042779098689 439742265107282084324017)
                      ·
                        rfl

theorem cell23_856395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4, 2].length) (baseStart_856395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856395 prefixEnd_856395 := by exact prefixLift 856395
  have htrace : WordTrace (prefixWord ++ tailWord_856395) baseStart_856395 baseEnd_856395 := by
    simpa [prefixWord, tailWord_856395, baseEnd_856395] using wordTrace_append hprefix tailTrace_856395
  have hstable : (prefixWord ++ tailWord_856395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856395).length < 2 ^ (prefixWord ++ tailWord_856395).sum := by decide
  have hdescent : baseEnd_856395 < baseStart_856395 := by decide
  rcases family_descends (prefixWord ++ tailWord_856395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856398 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_856398 : Nat := 118140960795 + 856398 * 2 ^ 59
def prefixEnd_856398 : Nat := 4983230072969 + 3 ^ 40 * 856398 * 2
def baseEnd_856398 : Nat := 439743805549245572586503

theorem tailTrace_856398 : CollatzResearch.WordTrace tailWord_856398 prefixEnd_856398 439743805549245572586503 := by
  unfold tailWord_856398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904425143927972747383231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20823600767615854652710565 3904425143927972747383231)
  ·
    refine ⟨5856637715891959121074847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3904425143927972747383231 5856637715891959121074847)
    ·
      refine ⟨8784956573837938681612271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856637715891959121074847 8784956573837938681612271)
      ·
        refine ⟨13177434860756908022418407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8784956573837938681612271 13177434860756908022418407)
        ·
          refine ⟨19766152291135362033627611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13177434860756908022418407 19766152291135362033627611)
          ·
            refine ⟨29649228436703043050441417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19766152291135362033627611 29649228436703043050441417)
            ·
              refine ⟨22236921327527282287831063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29649228436703043050441417 22236921327527282287831063)
              ·
                refine ⟨33355381991290923431746595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22236921327527282287831063 33355381991290923431746595)
                ·
                  refine ⟨50033072986936385147619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33355381991290923431746595 50033072986936385147619893)
                  ·
                    refine ⟨4690600592525286107589365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50033072986936385147619893 4690600592525286107589365)
                    ·
                      refine ⟨439743805549245572586503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4690600592525286107589365 439743805549245572586503)
                      ·
                        rfl

theorem cell23_856398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_856398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856398 prefixEnd_856398 := by exact prefixLift 856398
  have htrace : WordTrace (prefixWord ++ tailWord_856398) baseStart_856398 baseEnd_856398 := by
    simpa [prefixWord, tailWord_856398, baseEnd_856398] using wordTrace_append hprefix tailTrace_856398
  have hstable : (prefixWord ++ tailWord_856398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856398).length < 2 ^ (prefixWord ++ tailWord_856398).sum := by decide
  have hdescent : baseEnd_856398 < baseStart_856398 := by decide
  rcases family_descends (prefixWord ++ tailWord_856398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856408 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_856408 : Nat := 118140960795 + 856408 * 2 ^ 59
def prefixEnd_856408 : Nat := 4983230072969 + 3 ^ 40 * 856408 * 2
def baseEnd_856408 : Nat := 439748940355790533461457

theorem tailTrace_856408 : CollatzResearch.WordTrace tailWord_856408 prefixEnd_856408 439748940355790533461457 := by
  unfold tailWord_856408
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617882940693776843464939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20823843920925035791286585 15617882940693776843464939)
  ·
    refine ⟨23426824411040665265197409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15617882940693776843464939 23426824411040665265197409)
    ·
      refine ⟨17570118308280498948898057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23426824411040665265197409 17570118308280498948898057)
      ·
        refine ⟨13177588731210374211673543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17570118308280498948898057 13177588731210374211673543)
        ·
          refine ⟨19766383096815561317510315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13177588731210374211673543 19766383096815561317510315)
          ·
            refine ⟨29649574645223341976265473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19766383096815561317510315 29649574645223341976265473)
            ·
              refine ⟨22237180983917506482199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29649574645223341976265473 22237180983917506482199105)
              ·
                refine ⟨16677885737938129861649329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22237180983917506482199105 16677885737938129861649329)
                ·
                  refine ⟨12508414303453597396236997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16677885737938129861649329 12508414303453597396236997)
                  ·
                    refine ⟨2345327681897549511794437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12508414303453597396236997 2345327681897549511794437)
                    ·
                      refine ⟨439748940355790533461457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2345327681897549511794437 439748940355790533461457)
                      ·
                        rfl

theorem cell23_856408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_856408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856408 prefixEnd_856408 := by exact prefixLift 856408
  have htrace : WordTrace (prefixWord ++ tailWord_856408) baseStart_856408 baseEnd_856408 := by
    simpa [prefixWord, tailWord_856408, baseEnd_856408] using wordTrace_append hprefix tailTrace_856408
  have hstable : (prefixWord ++ tailWord_856408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856408).length < 2 ^ (prefixWord ++ tailWord_856408).sum := by decide
  have hdescent : baseEnd_856408 < baseStart_856408 := by decide
  rcases family_descends (prefixWord ++ tailWord_856408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856432 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_856432 : Nat := 118140960795 + 856432 * 2 ^ 59
def prefixEnd_856432 : Nat := 4983230072969 + 3 ^ 40 * 856432 * 2
def baseEnd_856432 : Nat := 439761263891498439561347

theorem tailTrace_856432 : CollatzResearch.WordTrace tailWord_856432 prefixEnd_856432 439761263891498439561347 := by
  unfold tailWord_856432
  simp only [CollatzResearch.WordTrace]
  refine ⟨15618320616650302892901775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20824427488867070523869033 15618320616650302892901775)
  ·
    refine ⟨23427480924975454339352663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15618320616650302892901775 23427480924975454339352663)
    ·
      refine ⟨35141221387463181509028995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23427480924975454339352663 35141221387463181509028995)
      ·
        refine ⟨52711832081194772263543493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35141221387463181509028995 52711832081194772263543493)
        ·
          refine ⟨9883468515224019799414405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52711832081194772263543493 9883468515224019799414405)
          ·
            refine ⟨1853150346604503712390201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9883468515224019799414405 1853150346604503712390201)
            ·
              refine ⟨1389862759953377784292651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853150346604503712390201 1389862759953377784292651)
              ·
                refine ⟨2084794139930066676438977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389862759953377784292651 2084794139930066676438977)
                ·
                  refine ⟨1563595604947550007329233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084794139930066676438977 1563595604947550007329233)
                  ·
                    refine ⟨1172696703710662505496925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563595604947550007329233 1172696703710662505496925)
                    ·
                      refine ⟨439761263891498439561347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1172696703710662505496925 439761263891498439561347)
                      ·
                        rfl

theorem cell23_856432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_856432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856432 prefixEnd_856432 := by exact prefixLift 856432
  have htrace : WordTrace (prefixWord ++ tailWord_856432) baseStart_856432 baseEnd_856432 := by
    simpa [prefixWord, tailWord_856432, baseEnd_856432] using wordTrace_append hprefix tailTrace_856432
  have hstable : (prefixWord ++ tailWord_856432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856432).length < 2 ^ (prefixWord ++ tailWord_856432).sum := by decide
  have hdescent : baseEnd_856432 < baseStart_856432 := by decide
  rcases family_descends (prefixWord ++ tailWord_856432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856482 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_856482 : Nat := 118140960795 + 856482 * 2 ^ 59
def prefixEnd_856482 : Nat := 4983230072969 + 3 ^ 40 * 856482 * 2
def baseEnd_856482 : Nat := 146595645974741081312039

theorem tailTrace_856482 : CollatzResearch.WordTrace tailWord_856482 prefixEnd_856482 146595645974741081312039 := by
  unfold tailWord_856482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809616220779866081280925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20825643255412976216749133 7809616220779866081280925)
  ·
    refine ⟨2928606082792449780480347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7809616220779866081280925 2928606082792449780480347)
    ·
      refine ⟨4392909124188674670720521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928606082792449780480347 4392909124188674670720521)
      ·
        refine ⟨3294681843141506003040391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4392909124188674670720521 3294681843141506003040391)
        ·
          refine ⟨4942022764712259004560587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294681843141506003040391 4942022764712259004560587)
          ·
            refine ⟨7413034147068388506840881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942022764712259004560587 7413034147068388506840881)
            ·
              refine ⟨5559775610301291380130661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7413034147068388506840881 5559775610301291380130661)
              ·
                refine ⟨1042457926931492133774499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5559775610301291380130661 1042457926931492133774499)
                ·
                  refine ⟨1563686890397238200661749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042457926931492133774499 1563686890397238200661749)
                  ·
                    refine ⟨146595645974741081312039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1563686890397238200661749 146595645974741081312039)
                    ·
                      rfl

theorem cell23_856482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_856482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856482 prefixEnd_856482 := by exact prefixLift 856482
  have htrace : WordTrace (prefixWord ++ tailWord_856482) baseStart_856482 baseEnd_856482 := by
    simpa [prefixWord, tailWord_856482, baseEnd_856482] using wordTrace_append hprefix tailTrace_856482
  have hstable : (prefixWord ++ tailWord_856482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856482).length < 2 ^ (prefixWord ++ tailWord_856482).sum := by decide
  have hdescent : baseEnd_856482 < baseStart_856482 := by decide
  rcases family_descends (prefixWord ++ tailWord_856482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856485 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_856485 : Nat := 118140960795 + 856485 * 2 ^ 59
def prefixEnd_856485 : Nat := 4983230072969 + 3 ^ 40 * 856485 * 2
def baseEnd_856485 : Nat := 439788478366186732198603

theorem tailTrace_856485 : CollatzResearch.WordTrace tailWord_856485 prefixEnd_856485 439788478366186732198603 := by
  unfold tailWord_856485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238574302108595837482909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825716201405730558321939 31238574302108595837482909)
  ·
    refine ⟨11714465363290723439056091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31238574302108595837482909 11714465363290723439056091)
    ·
      refine ⟨17571698044936085158584137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11714465363290723439056091 17571698044936085158584137)
      ·
        refine ⟨13178773533702063868938103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17571698044936085158584137 13178773533702063868938103)
        ·
          refine ⟨19768160300553095803407155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178773533702063868938103 19768160300553095803407155)
          ·
            refine ⟨29652240450829643705110733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19768160300553095803407155 29652240450829643705110733)
            ·
              refine ⟨11119590169061116389416525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29652240450829643705110733 11119590169061116389416525)
              ·
                refine ⟨4169846313397918646031197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11119590169061116389416525 4169846313397918646031197)
                ·
                  refine ⟨1563692367524219492261699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4169846313397918646031197 1563692367524219492261699)
                  ·
                    refine ⟨2345538551286329238392549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563692367524219492261699 2345538551286329238392549)
                    ·
                      refine ⟨439788478366186732198603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2345538551286329238392549 439788478366186732198603)
                      ·
                        rfl

theorem cell23_856485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_856485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856485 prefixEnd_856485 := by exact prefixLift 856485
  have htrace : WordTrace (prefixWord ++ tailWord_856485) baseStart_856485 baseEnd_856485 := by
    simpa [prefixWord, tailWord_856485, baseEnd_856485] using wordTrace_append hprefix tailTrace_856485
  have hstable : (prefixWord ++ tailWord_856485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856485).length < 2 ^ (prefixWord ++ tailWord_856485).sum := by decide
  have hdescent : baseEnd_856485 < baseStart_856485 := by decide
  rcases family_descends (prefixWord ++ tailWord_856485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856490 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_856490 : Nat := 118140960795 + 856490 * 2 ^ 59
def prefixEnd_856490 : Nat := 4983230072969 + 3 ^ 40 * 856490 * 2
def baseEnd_856490 : Nat := 146597015256486404212027

theorem tailTrace_856490 : CollatzResearch.WordTrace tailWord_856490 prefixEnd_856490 146597015256486404212027 := by
  unfold tailWord_856490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809689166772620422853731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20825837778060321127609949 7809689166772620422853731)
  ·
    refine ⟨11714533750158930634280597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7809689166772620422853731 11714533750158930634280597)
    ·
      refine ⟨549118769538699873481903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11714533750158930634280597 549118769538699873481903)
      ·
        refine ⟨823678154308049810222855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549118769538699873481903 823678154308049810222855)
        ·
          refine ⟨1235517231462074715334283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823678154308049810222855 1235517231462074715334283)
          ·
            refine ⟨1853275847193112073001425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235517231462074715334283 1853275847193112073001425)
            ·
              refine ⟨1389956885394834054751069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853275847193112073001425 1389956885394834054751069)
              ·
                refine ⟨521233832023062770531651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389956885394834054751069 521233832023062770531651)
                ·
                  refine ⟨781850748034594155797477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521233832023062770531651 781850748034594155797477)
                  ·
                    refine ⟨146597015256486404212027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781850748034594155797477 146597015256486404212027)
                    ·
                      rfl

theorem cell23_856490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_856490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856490 prefixEnd_856490 := by exact prefixLift 856490
  have htrace : WordTrace (prefixWord ++ tailWord_856490) baseStart_856490 baseEnd_856490 := by
    simpa [prefixWord, tailWord_856490, baseEnd_856490] using wordTrace_append hprefix tailTrace_856490
  have hstable : (prefixWord ++ tailWord_856490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856490).length < 2 ^ (prefixWord ++ tailWord_856490).sum := by decide
  have hdescent : baseEnd_856490 < baseStart_856490 := by decide
  rcases family_descends (prefixWord ++ tailWord_856490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856519 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_856519 : Nat := 118140960795 + 856519 * 2 ^ 59
def prefixEnd_856519 : Nat := 4983230072969 + 3 ^ 40 * 856519 * 2
def baseEnd_856519 : Nat := 439805936708439599173447

theorem tailTrace_856519 : CollatzResearch.WordTrace tailWord_856519 prefixEnd_856519 439805936708439599173447 := by
  unfold tailWord_856519
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239814383985419644220611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20826542922656946429480407 31239814383985419644220611)
  ·
    refine ⟨46859721575978129466330917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31239814383985419644220611 46859721575978129466330917)
    ·
      refine ⟨8786197795495899274937047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46859721575978129466330917 8786197795495899274937047)
      ·
        refine ⟨13179296693243848912405571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786197795495899274937047 13179296693243848912405571)
        ·
          refine ⟨19768945039865773368608357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13179296693243848912405571 19768945039865773368608357)
          ·
            refine ⟨3706677194974832506614067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19768945039865773368608357 3706677194974832506614067)
            ·
              refine ⟨5560015792462248759921101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706677194974832506614067 5560015792462248759921101)
              ·
                refine ⟨2085005922173343284970413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5560015792462248759921101 2085005922173343284970413)
                ·
                  refine ⟨781877220815003731863905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2085005922173343284970413 781877220815003731863905)
                  ·
                    refine ⟨586407915611252798897929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781877220815003731863905 586407915611252798897929)
                    ·
                      refine ⟨439805936708439599173447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586407915611252798897929 439805936708439599173447)
                      ·
                        rfl

theorem cell23_856519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_856519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856519 prefixEnd_856519 := by exact prefixLift 856519
  have htrace : WordTrace (prefixWord ++ tailWord_856519) baseStart_856519 baseEnd_856519 := by
    simpa [prefixWord, tailWord_856519, baseEnd_856519] using wordTrace_append hprefix tailTrace_856519
  have hstable : (prefixWord ++ tailWord_856519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856519).length < 2 ^ (prefixWord ++ tailWord_856519).sum := by decide
  have hdescent : baseEnd_856519 < baseStart_856519 := by decide
  rcases family_descends (prefixWord ++ tailWord_856519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856532 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_856532 : Nat := 118140960795 + 856532 * 2 ^ 59
def prefixEnd_856532 : Nat := 4983230072969 + 3 ^ 40 * 856532 * 2
def baseEnd_856532 : Nat := 439812611956948048310887

theorem tailTrace_856532 : CollatzResearch.WordTrace tailWord_856532 prefixEnd_856532 439812611956948048310887 := by
  unfold tailWord_856532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620144266469161432221925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20826859021958881909629233 15620144266469161432221925)
  ·
    refine ⟨2928777049962967768541611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15620144266469161432221925 2928777049962967768541611)
    ·
      refine ⟨4393165574944451652812417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928777049962967768541611 4393165574944451652812417)
      ·
        refine ⟨3294874181208338739609313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4393165574944451652812417 3294874181208338739609313)
        ·
          refine ⟨2471155635906254054706985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3294874181208338739609313 2471155635906254054706985)
          ·
            refine ⟨1853366726929690541030239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471155635906254054706985 1853366726929690541030239)
            ·
              refine ⟨2780050090394535811545359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853366726929690541030239 2780050090394535811545359)
              ·
                refine ⟨4170075135591803717318039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780050090394535811545359 4170075135591803717318039)
                ·
                  refine ⟨6255112703387705575977059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4170075135591803717318039 6255112703387705575977059)
                  ·
                    refine ⟨9382669055081558363965589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6255112703387705575977059 9382669055081558363965589)
                    ·
                      refine ⟨439812611956948048310887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9382669055081558363965589 439812611956948048310887)
                      ·
                        rfl

theorem cell23_856532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_856532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856532 prefixEnd_856532 := by exact prefixLift 856532
  have htrace : WordTrace (prefixWord ++ tailWord_856532) baseStart_856532 baseEnd_856532 := by
    simpa [prefixWord, tailWord_856532, baseEnd_856532] using wordTrace_append hprefix tailTrace_856532
  have hstable : (prefixWord ++ tailWord_856532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856532).length < 2 ^ (prefixWord ++ tailWord_856532).sum := by decide
  have hdescent : baseEnd_856532 < baseStart_856532 := by decide
  rcases family_descends (prefixWord ++ tailWord_856532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856575 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_856575 : Nat := 118140960795 + 856575 * 2 ^ 59
def prefixEnd_856575 : Nat := 4983230072969 + 3 ^ 40 * 856575 * 2
def baseEnd_856575 : Nat := 439834691625091380073189

theorem tailTrace_856575 : CollatzResearch.WordTrace tailWord_856575 prefixEnd_856575 439834691625091380073189 := by
  unfold tailWord_856575
  simp only [CollatzResearch.WordTrace]
  refine ⟨31241856871782541208259179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20827904581188360805506119 31241856871782541208259179)
  ·
    refine ⟨46862785307673811812388769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31241856871782541208259179 46862785307673811812388769)
    ·
      refine ⟨35147088980755358859291577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46862785307673811812388769 35147088980755358859291577)
      ·
        refine ⟨26360316735566519144468683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35147088980755358859291577 26360316735566519144468683)
        ·
          refine ⟨39540475103349778716703025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26360316735566519144468683 39540475103349778716703025)
          ·
            refine ⟨29655356327512334037527269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39540475103349778716703025 29655356327512334037527269)
            ·
              refine ⟨5560379311408562632036363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29655356327512334037527269 5560379311408562632036363)
              ·
                refine ⟨8340568967112843948054545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560379311408562632036363 8340568967112843948054545)
                ·
                  refine ⟨6255426725334632961040909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8340568967112843948054545 6255426725334632961040909)
                  ·
                    refine ⟨2345785022000487360390341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6255426725334632961040909 2345785022000487360390341)
                    ·
                      refine ⟨439834691625091380073189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2345785022000487360390341 439834691625091380073189)
                      ·
                        rfl

theorem cell23_856575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_856575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856575 prefixEnd_856575 := by exact prefixLift 856575
  have htrace : WordTrace (prefixWord ++ tailWord_856575) baseStart_856575 baseEnd_856575 := by
    simpa [prefixWord, tailWord_856575, baseEnd_856575] using wordTrace_append hprefix tailTrace_856575
  have hstable : (prefixWord ++ tailWord_856575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856575).length < 2 ^ (prefixWord ++ tailWord_856575).sum := by decide
  have hdescent : baseEnd_856575 < baseStart_856575 := by decide
  rcases family_descends (prefixWord ++ tailWord_856575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856595 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_856595 : Nat := 118140960795 + 856595 * 2 ^ 59
def prefixEnd_856595 : Nat := 4983230072969 + 3 ^ 40 * 856595 * 2
def baseEnd_856595 : Nat := 439844961238181301823097

theorem tailTrace_856595 : CollatzResearch.WordTrace tailWord_856595 prefixEnd_856595 439844961238181301823097 := by
  unfold tailWord_856595
  simp only [CollatzResearch.WordTrace]
  refine ⟨31242586331710084623987239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20828390887806723082658159 31242586331710084623987239)
  ·
    refine ⟨46863879497565126935980859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31242586331710084623987239 46863879497565126935980859)
    ·
      refine ⟨70295819246347690403971289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46863879497565126935980859 70295819246347690403971289)
      ·
        refine ⟨52721864434760767802978467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70295819246347690403971289 52721864434760767802978467)
        ·
          refine ⟨79082796652141151704467701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52721864434760767802978467 79082796652141151704467701)
          ·
            refine ⟨7414012186138232972293847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79082796652141151704467701 7414012186138232972293847)
            ·
              refine ⟨11121018279207349458440771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7414012186138232972293847 11121018279207349458440771)
              ·
                refine ⟨16681527418811024187661157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121018279207349458440771 16681527418811024187661157)
                ·
                  refine ⟨3127786391027067035186467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16681527418811024187661157 3127786391027067035186467)
                  ·
                    refine ⟨4691679586540600552779701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3127786391027067035186467 4691679586540600552779701)
                    ·
                      refine ⟨439844961238181301823097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4691679586540600552779701 439844961238181301823097)
                      ·
                        rfl

theorem cell23_856595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_856595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856595 prefixEnd_856595 := by exact prefixLift 856595
  have htrace : WordTrace (prefixWord ++ tailWord_856595) baseStart_856595 baseEnd_856595 := by
    simpa [prefixWord, tailWord_856595, baseEnd_856595] using wordTrace_append hprefix tailTrace_856595
  have hstable : (prefixWord ++ tailWord_856595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856595).length < 2 ^ (prefixWord ++ tailWord_856595).sum := by decide
  have hdescent : baseEnd_856595 < baseStart_856595 := by decide
  rcases family_descends (prefixWord ++ tailWord_856595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856609 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_856609 : Nat := 118140960795 + 856609 * 2 ^ 59
def prefixEnd_856609 : Nat := 4983230072969 + 3 ^ 40 * 856609 * 2
def baseEnd_856609 : Nat := 439852149967344247048033

theorem tailTrace_856609 : CollatzResearch.WordTrace tailWord_856609 prefixEnd_856609 439852149967344247048033 := by
  unfold tailWord_856609
  simp only [CollatzResearch.WordTrace]
  refine ⟨31243096953659365014996881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20828731302439576676664587 31243096953659365014996881)
  ·
    refine ⟨23432322715244523761247661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31243096953659365014996881 23432322715244523761247661)
    ·
      refine ⟨8787121018216696410467873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23432322715244523761247661 8787121018216696410467873)
      ·
        refine ⟨6590340763662522307850905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8787121018216696410467873 6590340763662522307850905)
        ·
          refine ⟨4942755572746891730888179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6590340763662522307850905 4942755572746891730888179)
          ·
            refine ⟨7414133359120337596332269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942755572746891730888179 7414133359120337596332269)
            ·
              refine ⟨2780300009670126598624601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7414133359120337596332269 2780300009670126598624601)
              ·
                refine ⟨2085225007252594948968451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780300009670126598624601 2085225007252594948968451)
                ·
                  refine ⟨3127837510878892423452677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085225007252594948968451 3127837510878892423452677)
                  ·
                    refine ⟨586469533289792329397377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127837510878892423452677 586469533289792329397377)
                    ·
                      refine ⟨439852149967344247048033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586469533289792329397377 439852149967344247048033)
                      ·
                        rfl

theorem cell23_856609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_856609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856609 prefixEnd_856609 := by exact prefixLift 856609
  have htrace : WordTrace (prefixWord ++ tailWord_856609) baseStart_856609 baseEnd_856609 := by
    simpa [prefixWord, tailWord_856609, baseEnd_856609] using wordTrace_append hprefix tailTrace_856609
  have hstable : (prefixWord ++ tailWord_856609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856609).length < 2 ^ (prefixWord ++ tailWord_856609).sum := by decide
  have hdescent : baseEnd_856609 < baseStart_856609 := by decide
  rcases family_descends (prefixWord ++ tailWord_856609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856621 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_856621 : Nat := 118140960795 + 856621 * 2 ^ 59
def prefixEnd_856621 : Nat := 4983230072969 + 3 ^ 40 * 856621 * 2
def baseEnd_856621 : Nat := 439858311735198200097979

theorem tailTrace_856621 : CollatzResearch.WordTrace tailWord_856621 prefixEnd_856621 439858311735198200097979 := by
  unfold tailWord_856621
  simp only [CollatzResearch.WordTrace]
  refine ⟨31243534629615891064433717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20829023086410594042955811 31243534629615891064433717)
  ·
    refine ⟨2929081371526489787290661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31243534629615891064433717 2929081371526489787290661)
    ·
      refine ⟨549202757161216835116999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2929081371526489787290661 549202757161216835116999)
      ·
        refine ⟨823804135741825252675499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549202757161216835116999 823804135741825252675499)
        ·
          refine ⟨1235706203612737879013249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823804135741825252675499 1235706203612737879013249)
          ·
            refine ⟨926779652709553409259937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235706203612737879013249 926779652709553409259937)
            ·
              refine ⟨695084739532165056944953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926779652709553409259937 695084739532165056944953)
              ·
                refine ⟨521313554649123792708715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695084739532165056944953 521313554649123792708715)
                ·
                  refine ⟨781970331973685689063073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521313554649123792708715 781970331973685689063073)
                  ·
                    refine ⟨586477748980264266797305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781970331973685689063073 586477748980264266797305)
                    ·
                      refine ⟨439858311735198200097979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586477748980264266797305 439858311735198200097979)
                      ·
                        rfl

theorem cell23_856621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_856621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856621 prefixEnd_856621 := by exact prefixLift 856621
  have htrace : WordTrace (prefixWord ++ tailWord_856621) baseStart_856621 baseEnd_856621 := by
    simpa [prefixWord, tailWord_856621, baseEnd_856621] using wordTrace_append hprefix tailTrace_856621
  have hstable : (prefixWord ++ tailWord_856621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856621).length < 2 ^ (prefixWord ++ tailWord_856621).sum := by decide
  have hdescent : baseEnd_856621 < baseStart_856621 := by decide
  rcases family_descends (prefixWord ++ tailWord_856621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856625 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_856625 : Nat := 118140960795 + 856625 * 2 ^ 59
def prefixEnd_856625 : Nat := 4983230072969 + 3 ^ 40 * 856625 * 2
def baseEnd_856625 : Nat := 439860365657816184447959

theorem tailTrace_856625 : CollatzResearch.WordTrace tailWord_856625 prefixEnd_856625 439860365657816184447959 := by
  unfold tailWord_856625
  simp only [CollatzResearch.WordTrace]
  refine ⟨31243680521601399747579329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20829120347734266498386219 31243680521601399747579329)
  ·
    refine ⟨23432760391201049810684497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31243680521601399747579329 23432760391201049810684497)
    ·
      refine ⟨17574570293400787358013373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23432760391201049810684497 17574570293400787358013373)
      ·
        refine ⟨6590463860025295259255015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17574570293400787358013373 6590463860025295259255015)
        ·
          refine ⟨9885695790037942888882523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590463860025295259255015 9885695790037942888882523)
          ·
            refine ⟨14828543685056914333323785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9885695790037942888882523 14828543685056914333323785)
            ·
              refine ⟨11121407763792685749992839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14828543685056914333323785 11121407763792685749992839)
              ·
                refine ⟨16682111645689028624989259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121407763792685749992839 16682111645689028624989259)
                ·
                  refine ⟨25023167468533542937483889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16682111645689028624989259 25023167468533542937483889)
                  ·
                    refine ⟨18767375601400157203112917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25023167468533542937483889 18767375601400157203112917)
                    ·
                      refine ⟨439860365657816184447959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18767375601400157203112917 439860365657816184447959)
                      ·
                        rfl

theorem cell23_856625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_856625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856625 prefixEnd_856625 := by exact prefixLift 856625
  have htrace : WordTrace (prefixWord ++ tailWord_856625) baseStart_856625 baseEnd_856625 := by
    simpa [prefixWord, tailWord_856625, baseEnd_856625] using wordTrace_append hprefix tailTrace_856625
  have hstable : (prefixWord ++ tailWord_856625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856625).length < 2 ^ (prefixWord ++ tailWord_856625).sum := by decide
  have hdescent : baseEnd_856625 < baseStart_856625 := by decide
  rcases family_descends (prefixWord ++ tailWord_856625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856626 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_856626 : Nat := 118140960795 + 856626 * 2 ^ 59
def prefixEnd_856626 : Nat := 4983230072969 + 3 ^ 40 * 856626 * 2
def baseEnd_856626 : Nat := 439860879138470680535455

theorem tailTrace_856626 : CollatzResearch.WordTrace tailWord_856626 prefixEnd_856626 439860879138470680535455 := by
  unfold tailWord_856626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810929248649444229591433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20829144663065184612243821 7810929248649444229591433)
  ·
    refine ⟨5858196936487083172193575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7810929248649444229591433 5858196936487083172193575)
    ·
      refine ⟨8787295404730624758290363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858196936487083172193575 8787295404730624758290363)
      ·
        refine ⟨13180943107095937137435545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787295404730624758290363 13180943107095937137435545)
        ·
          refine ⟨9885707330321952853076659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13180943107095937137435545 9885707330321952853076659)
          ·
            refine ⟨14828560995482929279614989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9885707330321952853076659 14828560995482929279614989)
            ·
              refine ⟨5560710373306098479855621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14828560995482929279614989 5560710373306098479855621)
              ·
                refine ⟨1042633194994893464972929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5560710373306098479855621 1042633194994893464972929)
                ·
                  refine ⟨781974896246170098729697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042633194994893464972929 781974896246170098729697)
                  ·
                    refine ⟨586481172184627574047273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 781974896246170098729697 586481172184627574047273)
                    ·
                      refine ⟨439860879138470680535455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586481172184627574047273 439860879138470680535455)
                      ·
                        rfl

theorem cell23_856626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_856626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856626 prefixEnd_856626 := by exact prefixLift 856626
  have htrace : WordTrace (prefixWord ++ tailWord_856626) baseStart_856626 baseEnd_856626 := by
    simpa [prefixWord, tailWord_856626, baseEnd_856626] using wordTrace_append hprefix tailTrace_856626
  have hstable : (prefixWord ++ tailWord_856626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856626).length < 2 ^ (prefixWord ++ tailWord_856626).sum := by decide
  have hdescent : baseEnd_856626 < baseStart_856626 := by decide
  rcases family_descends (prefixWord ++ tailWord_856626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856655 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_856655 : Nat := 118140960795 + 856655 * 2 ^ 59
def prefixEnd_856655 : Nat := 4983230072969 + 3 ^ 40 * 856655 * 2
def baseEnd_856655 : Nat := 439875770077451067072821

theorem tailTrace_856655 : CollatzResearch.WordTrace tailWord_856655 prefixEnd_856655 439875770077451067072821 := by
  unfold tailWord_856655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244774711492714871171419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20829849807661809914114279 31244774711492714871171419)
  ·
    refine ⟨46867162067239072306757129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31244774711492714871171419 46867162067239072306757129)
    ·
      refine ⟨35150371550429304230067847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46867162067239072306757129 35150371550429304230067847)
      ·
        refine ⟨52725557325643956345101771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35150371550429304230067847 52725557325643956345101771)
        ·
          refine ⟨79088335988465934517652657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52725557325643956345101771 79088335988465934517652657)
          ·
            refine ⟨59316251991349450888239493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79088335988465934517652657 59316251991349450888239493)
            ·
              refine ⟨11121797248378022041544905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59316251991349450888239493 11121797248378022041544905)
              ·
                refine ⟨8341347936283516531158679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11121797248378022041544905 8341347936283516531158679)
                ·
                  refine ⟨12512021904425274796738019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341347936283516531158679 12512021904425274796738019)
                  ·
                    refine ⟨18768032856637912195107029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12512021904425274796738019 18768032856637912195107029)
                    ·
                      refine ⟨439875770077451067072821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18768032856637912195107029 439875770077451067072821)
                      ·
                        rfl

theorem cell23_856655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_856655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856655 prefixEnd_856655 := by exact prefixLift 856655
  have htrace : WordTrace (prefixWord ++ tailWord_856655) baseStart_856655 baseEnd_856655 := by
    simpa [prefixWord, tailWord_856655, baseEnd_856655] using wordTrace_append hprefix tailTrace_856655
  have hstable : (prefixWord ++ tailWord_856655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856655).length < 2 ^ (prefixWord ++ tailWord_856655).sum := by decide
  have hdescent : baseEnd_856655 < baseStart_856655 := by decide
  rcases family_descends (prefixWord ++ tailWord_856655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856709 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_856709 : Nat := 118140960795 + 856709 * 2 ^ 59
def prefixEnd_856709 : Nat := 4983230072969 + 3 ^ 40 * 856709 * 2
def baseEnd_856709 : Nat := 146634499344264618599191

theorem tailTrace_856709 : CollatzResearch.WordTrace tailWord_856709 prefixEnd_856709 146634499344264618599191 := by
  unfold tailWord_856709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31246744253297082093637181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20831162835531388062424787 31246744253297082093637181)
  ·
    refine ⟨11717529094986405785113943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31246744253297082093637181 11717529094986405785113943)
    ·
      refine ⟨17576293642479608677670915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11717529094986405785113943 17576293642479608677670915)
      ·
        refine ⟨26364440463719413016506373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17576293642479608677670915 26364440463719413016506373)
        ·
          refine ⟨4943332586947389940594945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26364440463719413016506373 4943332586947389940594945)
          ·
            refine ⟨3707499440210542455446209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4943332586947389940594945 3707499440210542455446209)
            ·
              refine ⟨2780624580157906841584657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707499440210542455446209 2780624580157906841584657)
              ·
                refine ⟨2085468435118430131188493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780624580157906841584657 2085468435118430131188493)
                ·
                  refine ⟨782050663169411299195685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2085468435118430131188493 782050663169411299195685)
                  ·
                    refine ⟨146634499344264618599191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782050663169411299195685 146634499344264618599191)
                    ·
                      rfl

theorem cell23_856709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_856709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856709 prefixEnd_856709 := by exact prefixLift 856709
  have htrace : WordTrace (prefixWord ++ tailWord_856709) baseStart_856709 baseEnd_856709 := by
    simpa [prefixWord, tailWord_856709, baseEnd_856709] using wordTrace_append hprefix tailTrace_856709
  have hstable : (prefixWord ++ tailWord_856709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856709).length < 2 ^ (prefixWord ++ tailWord_856709).sum := by decide
  have hdescent : baseEnd_856709 < baseStart_856709 := by decide
  rcases family_descends (prefixWord ++ tailWord_856709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856736 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_856736 : Nat := 118140960795 + 856736 * 2 ^ 59
def prefixEnd_856736 : Nat := 4983230072969 + 3 ^ 40 * 856736 * 2
def baseEnd_856736 : Nat := 439917362010465250159949

theorem tailTrace_856736 : CollatzResearch.WordTrace tailWord_856736 prefixEnd_856736 439917362010465250159949 := by
  unfold tailWord_856736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623864512099632852435031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20831819349466177136580041 15623864512099632852435031)
  ·
    refine ⟨23435796768149449278652547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15623864512099632852435031 23435796768149449278652547)
    ·
      refine ⟨35153695152224173917978821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23435796768149449278652547 35153695152224173917978821)
      ·
        refine ⟨6591317841042032609621029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35153695152224173917978821 6591317841042032609621029)
        ·
          refine ⟨1235872095195381114303943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6591317841042032609621029 1235872095195381114303943)
          ·
            refine ⟨1853808142793071671455915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235872095195381114303943 1853808142793071671455915)
            ·
              refine ⟨2780712214189607507183873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853808142793071671455915 2780712214189607507183873)
              ·
                refine ⟨2085534160642205630387905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780712214189607507183873 2085534160642205630387905)
                ·
                  refine ⟨1564150620481654222790929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085534160642205630387905 1564150620481654222790929)
                  ·
                    refine ⟨1173112965361240667093197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564150620481654222790929 1173112965361240667093197)
                    ·
                      refine ⟨439917362010465250159949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173112965361240667093197 439917362010465250159949)
                      ·
                        rfl

theorem cell23_856736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_856736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856736 prefixEnd_856736 := by exact prefixLift 856736
  have htrace : WordTrace (prefixWord ++ tailWord_856736) baseStart_856736 baseEnd_856736 := by
    simpa [prefixWord, tailWord_856736, baseEnd_856736] using wordTrace_append hprefix tailTrace_856736
  have hstable : (prefixWord ++ tailWord_856736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856736).length < 2 ^ (prefixWord ++ tailWord_856736).sum := by decide
  have hdescent : baseEnd_856736 < baseStart_856736 := by decide
  rcases family_descends (prefixWord ++ tailWord_856736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856752 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_856752 : Nat := 118140960795 + 856752 * 2 ^ 59
def prefixEnd_856752 : Nat := 4983230072969 + 3 ^ 40 * 856752 * 2
def baseEnd_856752 : Nat := 146641859233645729186625

theorem tailTrace_856752 : CollatzResearch.WordTrace tailWord_856752 prefixEnd_856752 146641859233645729186625 := by
  unfold tailWord_856752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624156296070650218726255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20832208394760866958301673 15624156296070650218726255)
  ·
    refine ⟨23436234444105975328089383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15624156296070650218726255 23436234444105975328089383)
    ·
      refine ⟨35154351666158962992134075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23436234444105975328089383 35154351666158962992134075)
      ·
        refine ⟨52731527499238444488201113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35154351666158962992134075 52731527499238444488201113)
        ·
          refine ⟨39548645624428833366150835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52731527499238444488201113 39548645624428833366150835)
          ·
            refine ⟨59322968436643250049226253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39548645624428833366150835 59322968436643250049226253)
            ·
              refine ⟨22246113163741218768459845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59322968436643250049226253 22246113163741218768459845)
              ·
                refine ⟨4171146218201478519086221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22246113163741218768459845 4171146218201478519086221)
                ·
                  refine ⟨1564179831825554444657333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4171146218201478519086221 1564179831825554444657333)
                  ·
                    refine ⟨146641859233645729186625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1564179831825554444657333 146641859233645729186625)
                    ·
                      rfl

theorem cell23_856752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_856752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856752 prefixEnd_856752 := by exact prefixLift 856752
  have htrace : WordTrace (prefixWord ++ tailWord_856752) baseStart_856752 baseEnd_856752 := by
    simpa [prefixWord, tailWord_856752, baseEnd_856752] using wordTrace_append hprefix tailTrace_856752
  have hstable : (prefixWord ++ tailWord_856752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856752).length < 2 ^ (prefixWord ++ tailWord_856752).sum := by decide
  have hdescent : baseEnd_856752 < baseStart_856752 := by decide
  rcases family_descends (prefixWord ++ tailWord_856752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856766 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_856766 : Nat := 118140960795 + 856766 * 2 ^ 59
def prefixEnd_856766 : Nat := 4983230072969 + 3 ^ 40 * 856766 * 2
def baseEnd_856766 : Nat := 439932766430100132784811

theorem tailTrace_856766 : CollatzResearch.WordTrace tailWord_856766 prefixEnd_856766 439932766430100132784811 := by
  unfold tailWord_856766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906102901761322603557769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20832548809393720552308101 3906102901761322603557769)
  ·
    refine ⟨2929577176320991952668327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3906102901761322603557769 2929577176320991952668327)
    ·
      refine ⟨4394365764481487929002491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929577176320991952668327 4394365764481487929002491)
      ·
        refine ⟨6591548646722231893503737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394365764481487929002491 6591548646722231893503737)
        ·
          refine ⟨4943661485041673920127803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6591548646722231893503737 4943661485041673920127803)
          ·
            refine ⟨7415492227562510880191705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943661485041673920127803 7415492227562510880191705)
            ·
              refine ⟨5561619170671883160143779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415492227562510880191705 5561619170671883160143779)
              ·
                refine ⟨8342428756007824740215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561619170671883160143779 8342428756007824740215669)
                ·
                  refine ⟨782102695875733569395219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8342428756007824740215669 782102695875733569395219)
                  ·
                    refine ⟨1173154043813600354092829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 782102695875733569395219 1173154043813600354092829)
                    ·
                      refine ⟨439932766430100132784811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173154043813600354092829 439932766430100132784811)
                      ·
                        rfl

theorem cell23_856766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_856766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856766 prefixEnd_856766 := by exact prefixLift 856766
  have htrace : WordTrace (prefixWord ++ tailWord_856766) baseStart_856766 baseEnd_856766 := by
    simpa [prefixWord, tailWord_856766, baseEnd_856766] using wordTrace_append hprefix tailTrace_856766
  have hstable : (prefixWord ++ tailWord_856766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856766).length < 2 ^ (prefixWord ++ tailWord_856766).sum := by decide
  have hdescent : baseEnd_856766 < baseStart_856766 := by decide
  rcases family_descends (prefixWord ++ tailWord_856766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856776 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_856776 : Nat := 118140960795 + 856776 * 2 ^ 59
def prefixEnd_856776 : Nat := 4983230072969 + 3 ^ 40 * 856776 * 2
def baseEnd_856776 : Nat := 439937901236645093659765

theorem tailTrace_856776 : CollatzResearch.WordTrace tailWord_856776 prefixEnd_856776 439937901236645093659765 := by
  unfold tailWord_856776
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624593972027176268163091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20832791962702901690884121 15624593972027176268163091)
  ·
    refine ⟨23436890958040764402244637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15624593972027176268163091 23436890958040764402244637)
    ·
      refine ⟨8788834109265286650841739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23436890958040764402244637 8788834109265286650841739)
      ·
        refine ⟨13183251163897929976262609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788834109265286650841739 13183251163897929976262609)
        ·
          refine ⟨9887438372923447482196957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183251163897929976262609 9887438372923447482196957)
          ·
            refine ⟨3707789389846292805823859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9887438372923447482196957 3707789389846292805823859)
            ·
              refine ⟨5561684084769439208735789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707789389846292805823859 5561684084769439208735789)
              ·
                refine ⟨2085631531788539703275921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5561684084769439208735789 2085631531788539703275921)
                ·
                  refine ⟨1564223648841404777456941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085631531788539703275921 1564223648841404777456941)
                  ·
                    refine ⟨586583868315526791546353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564223648841404777456941 586583868315526791546353)
                    ·
                      refine ⟨439937901236645093659765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586583868315526791546353 439937901236645093659765)
                      ·
                        rfl

theorem cell23_856776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_856776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856776 prefixEnd_856776 := by exact prefixLift 856776
  have htrace : WordTrace (prefixWord ++ tailWord_856776) baseStart_856776 baseEnd_856776 := by
    simpa [prefixWord, tailWord_856776, baseEnd_856776] using wordTrace_append hprefix tailTrace_856776
  have hstable : (prefixWord ++ tailWord_856776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856776).length < 2 ^ (prefixWord ++ tailWord_856776).sum := by decide
  have hdescent : baseEnd_856776 < baseStart_856776 := by decide
  rcases family_descends (prefixWord ++ tailWord_856776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856809 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_856809 : Nat := 118140960795 + 856809 * 2 ^ 59
def prefixEnd_856809 : Nat := 4983230072969 + 3 ^ 40 * 856809 * 2
def baseEnd_856809 : Nat := 439954846098243464547113

theorem tailTrace_856809 : CollatzResearch.WordTrace tailWord_856809 prefixEnd_856809 439954846098243464547113 := by
  unfold tailWord_856809
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250391552934799172277481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20833594368623199448184987 31250391552934799172277481)
  ·
    refine ⟨23437793664701099379208111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31250391552934799172277481 23437793664701099379208111)
    ·
      refine ⟨35156690497051649068812167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23437793664701099379208111 35156690497051649068812167)
      ·
        refine ⟨52735035745577473603218251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35156690497051649068812167 52735035745577473603218251)
        ·
          refine ⟨79102553618366210404827377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52735035745577473603218251 79102553618366210404827377)
          ·
            refine ⟨59326915213774657803620533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79102553618366210404827377 59326915213774657803620533)
            ·
              refine ⟨5561898301291374169089425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59326915213774657803620533 5561898301291374169089425)
              ·
                refine ⟨4171423725968530626817069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561898301291374169089425 4171423725968530626817069)
                ·
                  refine ⟨1564283897238198985056401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4171423725968530626817069 1564283897238198985056401)
                  ·
                    refine ⟨1173212922928649238792301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564283897238198985056401 1173212922928649238792301)
                    ·
                      refine ⟨439954846098243464547113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173212922928649238792301 439954846098243464547113)
                      ·
                        rfl

theorem cell23_856809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_856809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856809 prefixEnd_856809 := by exact prefixLift 856809
  have htrace : WordTrace (prefixWord ++ tailWord_856809) baseStart_856809 baseEnd_856809 := by
    simpa [prefixWord, tailWord_856809, baseEnd_856809] using wordTrace_append hprefix tailTrace_856809
  have hstable : (prefixWord ++ tailWord_856809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856809).length < 2 ^ (prefixWord ++ tailWord_856809).sum := by decide
  have hdescent : baseEnd_856809 < baseStart_856809 := by decide
  rcases family_descends (prefixWord ++ tailWord_856809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856829 : List Nat := [1, 4, 1, 1, 1, 1, 7, 7]
def baseStart_856829 : Nat := 118140960795 + 856829 * 2 ^ 59
def prefixEnd_856829 : Nat := 4983230072969 + 3 ^ 40 * 856829 * 2
def baseEnd_856829 : Nat := 16295004285604940233223

theorem tailTrace_856829 : CollatzResearch.WordTrace tailWord_856829 prefixEnd_856829 16295004285604940233223 := by
  unfold tailWord_856829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251121012862342588005541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20834080675241561725337027 31251121012862342588005541)
  ·
    refine ⟨5859585189911689235251039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31251121012862342588005541 5859585189911689235251039)
    ·
      refine ⟨8789377784867533852876559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859585189911689235251039 8789377784867533852876559)
      ·
        refine ⟨13184066677301300779314839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789377784867533852876559 13184066677301300779314839)
        ·
          refine ⟨19776100015951951168972259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184066677301300779314839 19776100015951951168972259)
          ·
            refine ⟨29664150023927926753458389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19776100015951951168972259 29664150023927926753458389)
            ·
              refine ⟨695253516185810783284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29664150023927926753458389 695253516185810783284181)
              ·
                refine ⟨16295004285604940233223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 695253516185810783284181 16295004285604940233223)
                ·
                  rfl

theorem cell23_856829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 7].length) (baseStart_856829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856829 prefixEnd_856829 := by exact prefixLift 856829
  have htrace : WordTrace (prefixWord ++ tailWord_856829) baseStart_856829 baseEnd_856829 := by
    simpa [prefixWord, tailWord_856829, baseEnd_856829] using wordTrace_append hprefix tailTrace_856829
  have hstable : (prefixWord ++ tailWord_856829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856829).length < 2 ^ (prefixWord ++ tailWord_856829).sum := by decide
  have hdescent : baseEnd_856829 < baseStart_856829 := by decide
  rcases family_descends (prefixWord ++ tailWord_856829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856840 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_856840 : Nat := 118140960795 + 856840 * 2 ^ 59
def prefixEnd_856840 : Nat := 4983230072969 + 3 ^ 40 * 856840 * 2
def baseEnd_856840 : Nat := 439970763998532843259471

theorem tailTrace_856840 : CollatzResearch.WordTrace tailWord_856840 prefixEnd_856840 439970763998532843259471 := by
  unfold tailWord_856840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625761107911245733327987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20834348143881660977770649 15625761107911245733327987)
  ·
    refine ⟨23438641661866868599991981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625761107911245733327987 23438641661866868599991981)
    ·
      refine ⟨8789490623200075724996993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23438641661866868599991981 8789490623200075724996993)
      ·
        refine ⟨6592117967400056793747745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8789490623200075724996993 6592117967400056793747745)
        ·
          refine ⟨4944088475550042595310809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6592117967400056793747745 4944088475550042595310809)
          ·
            refine ⟨3708066356662531946483107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944088475550042595310809 3708066356662531946483107)
            ·
              refine ⟨5562099534993797919724661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708066356662531946483107 5562099534993797919724661)
              ·
                refine ⟨521446831405668554974187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5562099534993797919724661 521446831405668554974187)
                ·
                  refine ⟨782170247108502832461281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521446831405668554974187 782170247108502832461281)
                  ·
                    refine ⟨586627685331377124345961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782170247108502832461281 586627685331377124345961)
                    ·
                      refine ⟨439970763998532843259471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586627685331377124345961 439970763998532843259471)
                      ·
                        rfl

theorem cell23_856840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_856840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856840 prefixEnd_856840 := by exact prefixLift 856840
  have htrace : WordTrace (prefixWord ++ tailWord_856840) baseStart_856840 baseEnd_856840 := by
    simpa [prefixWord, tailWord_856840, baseEnd_856840] using wordTrace_append hprefix tailTrace_856840
  have hstable : (prefixWord ++ tailWord_856840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856840).length < 2 ^ (prefixWord ++ tailWord_856840).sum := by decide
  have hdescent : baseEnd_856840 < baseStart_856840 := by decide
  rcases family_descends (prefixWord ++ tailWord_856840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856877 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_856877 : Nat := 118140960795 + 856877 * 2 ^ 59
def prefixEnd_856877 : Nat := 4983230072969 + 3 ^ 40 * 856877 * 2
def baseEnd_856877 : Nat := 439989762782749198496801

theorem tailTrace_856877 : CollatzResearch.WordTrace tailWord_856877 prefixEnd_856877 439989762782749198496801 := by
  unfold tailWord_856877
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252871716688446785752885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835247811125631190501923 31252871716688446785752885)
  ·
    refine ⟨2929956723439541886164333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31252871716688446785752885 2929956723439541886164333)
    ·
      refine ⟨1098733771289828207311625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2929956723439541886164333 1098733771289828207311625)
      ·
        refine ⟨824050328467371155483719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098733771289828207311625 824050328467371155483719)
        ·
          refine ⟨1236075492701056733225579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824050328467371155483719 1236075492701056733225579)
          ·
            refine ⟨1854113239051585099838369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236075492701056733225579 1854113239051585099838369)
            ·
              refine ⟨1390584929288688824878777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854113239051585099838369 1390584929288688824878777)
              ·
                refine ⟨1042938696966516618659083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390584929288688824878777 1042938696966516618659083)
                ·
                  refine ⟨1564408045449774927988625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042938696966516618659083 1564408045449774927988625)
                  ·
                    refine ⟨1173306034087331195991469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564408045449774927988625 1173306034087331195991469)
                    ·
                      refine ⟨439989762782749198496801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173306034087331195991469 439989762782749198496801)
                      ·
                        rfl

theorem cell23_856877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_856877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856877 prefixEnd_856877 := by exact prefixLift 856877
  have htrace : WordTrace (prefixWord ++ tailWord_856877) baseStart_856877 baseEnd_856877 := by
    simpa [prefixWord, tailWord_856877, baseEnd_856877] using wordTrace_append hprefix tailTrace_856877
  have hstable : (prefixWord ++ tailWord_856877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856877).length < 2 ^ (prefixWord ++ tailWord_856877).sum := by decide
  have hdescent : baseEnd_856877 < baseStart_856877 := by decide
  rcases family_descends (prefixWord ++ tailWord_856877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856883 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 1, 3, 2]
def baseStart_856883 : Nat := 118140960795 + 856883 * 2 ^ 59
def prefixEnd_856883 : Nat := 4983230072969 + 3 ^ 40 * 856883 * 2
def baseEnd_856883 : Nat := 439992843666676175021773

theorem tailTrace_856883 : CollatzResearch.WordTrace tailWord_856883 prefixEnd_856883 439992843666676175021773 := by
  unfold tailWord_856883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31253090554666709810471303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835393703111139873647535 31253090554666709810471303)
  ·
    refine ⟨46879635832000064715706955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31253090554666709810471303 46879635832000064715706955)
    ·
      refine ⟨70319453748000097073560433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46879635832000064715706955 70319453748000097073560433)
      ·
        refine ⟨52739590311000072805170325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70319453748000097073560433 52739590311000072805170325)
        ·
          refine ⟨2472168295828128412742359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52739590311000072805170325 2472168295828128412742359)
          ·
            refine ⟨3708252443742192619113539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472168295828128412742359 3708252443742192619113539)
            ·
              refine ⟨5562378665613288928670309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708252443742192619113539 5562378665613288928670309)
              ·
                refine ⟨1042945999802491674125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5562378665613288928670309 1042945999802491674125683)
                ·
                  refine ⟨1564418999703737511188525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042945999802491674125683 1564418999703737511188525)
                  ·
                    refine ⟨586657124888901566695697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564418999703737511188525 586657124888901566695697)
                    ·
                      refine ⟨439992843666676175021773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586657124888901566695697 439992843666676175021773)
                      ·
                        rfl

theorem cell23_856883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3, 2].length) (baseStart_856883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856883 prefixEnd_856883 := by exact prefixLift 856883
  have htrace : WordTrace (prefixWord ++ tailWord_856883) baseStart_856883 baseEnd_856883 := by
    simpa [prefixWord, tailWord_856883, baseEnd_856883] using wordTrace_append hprefix tailTrace_856883
  have hstable : (prefixWord ++ tailWord_856883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856883).length < 2 ^ (prefixWord ++ tailWord_856883).sum := by decide
  have hdescent : baseEnd_856883 < baseStart_856883 := by decide
  rcases family_descends (prefixWord ++ tailWord_856883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856896 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2]
def baseStart_856896 : Nat := 118140960795 + 856896 * 2 ^ 59
def prefixEnd_856896 : Nat := 4983230072969 + 3 ^ 40 * 856896 * 2
def baseEnd_856896 : Nat := 439999518915184624159213

theorem tailTrace_856896 : CollatzResearch.WordTrace tailWord_856896 prefixEnd_856896 439999518915184624159213 := by
  unfold tailWord_856896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626782351809806515347271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20835709802413075353796361 15626782351809806515347271)
  ·
    refine ⟨23440173527714709773020907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15626782351809806515347271 23440173527714709773020907)
    ·
      refine ⟨35160260291572064659531361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23440173527714709773020907 35160260291572064659531361)
      ·
        refine ⟨26370195218679048494648521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35160260291572064659531361 26370195218679048494648521)
        ·
          refine ⟨19777646414009286370986391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26370195218679048494648521 19777646414009286370986391)
          ·
            refine ⟨29666469621013929556479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19777646414009286370986391 29666469621013929556479587)
            ·
              refine ⟨44499704431520894334719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29666469621013929556479587 44499704431520894334719381)
              ·
                refine ⟨2085923645227541921939971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44499704431520894334719381 2085923645227541921939971)
                ·
                  refine ⟨3128885467841312882909957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085923645227541921939971 3128885467841312882909957)
                  ·
                    refine ⟨586666025220246165545617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128885467841312882909957 586666025220246165545617)
                    ·
                      refine ⟨439999518915184624159213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586666025220246165545617 439999518915184624159213)
                      ·
                        rfl

theorem cell23_856896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_856896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856896 prefixEnd_856896 := by exact prefixLift 856896
  have htrace : WordTrace (prefixWord ++ tailWord_856896) baseStart_856896 baseEnd_856896 := by
    simpa [prefixWord, tailWord_856896, baseEnd_856896] using wordTrace_append hprefix tailTrace_856896
  have hstable : (prefixWord ++ tailWord_856896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856896).length < 2 ^ (prefixWord ++ tailWord_856896).sum := by decide
  have hdescent : baseEnd_856896 < baseStart_856896 := by decide
  rcases family_descends (prefixWord ++ tailWord_856896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856899 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_856899 : Nat := 118140960795 + 856899 * 2 ^ 59
def prefixEnd_856899 : Nat := 4983230072969 + 3 ^ 40 * 856899 * 2
def baseEnd_856899 : Nat := 440001059357148112421699

theorem tailTrace_856899 : CollatzResearch.WordTrace tailWord_856899 prefixEnd_856899 440001059357148112421699 := by
  unfold tailWord_856899
  simp only [CollatzResearch.WordTrace]
  refine ⟨31253674122608744543053751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835782748405829695369167 31253674122608744543053751)
  ·
    refine ⟨46880511183913116814580627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31253674122608744543053751 46880511183913116814580627)
    ·
      refine ⟨70320766775869675221870941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46880511183913116814580627 70320766775869675221870941)
      ·
        refine ⟨26370287540951128208201603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70320766775869675221870941 26370287540951128208201603)
        ·
          refine ⟨39555431311426692312302405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26370287540951128208201603 39555431311426692312302405)
          ·
            refine ⟨7416643370892504808556701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39555431311426692312302405 7416643370892504808556701)
            ·
              refine ⟨2781241264084689303208763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7416643370892504808556701 2781241264084689303208763)
              ·
                refine ⟨4171861896127033954813145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781241264084689303208763 4171861896127033954813145)
                ·
                  refine ⟨3128896422095275466109859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171861896127033954813145 3128896422095275466109859)
                  ·
                    refine ⟨4693344633142913199164789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128896422095275466109859 4693344633142913199164789)
                    ·
                      refine ⟨440001059357148112421699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4693344633142913199164789 440001059357148112421699)
                      ·
                        rfl

theorem cell23_856899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_856899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856899 prefixEnd_856899 := by exact prefixLift 856899
  have htrace : WordTrace (prefixWord ++ tailWord_856899) baseStart_856899 baseEnd_856899 := by
    simpa [prefixWord, tailWord_856899, baseEnd_856899] using wordTrace_append hprefix tailTrace_856899
  have hstable : (prefixWord ++ tailWord_856899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856899).length < 2 ^ (prefixWord ++ tailWord_856899).sum := by decide
  have hdescent : baseEnd_856899 < baseStart_856899 := by decide
  rcases family_descends (prefixWord ++ tailWord_856899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856956 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_856956 : Nat := 118140960795 + 856956 * 2 ^ 59
def prefixEnd_856956 : Nat := 4983230072969 + 3 ^ 40 * 856956 * 2
def baseEnd_856956 : Nat := 440030327754454389408937

theorem tailTrace_856956 : CollatzResearch.WordTrace tailWord_856956 prefixEnd_856956 440030327754454389408937 := by
  unfold tailWord_856956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15627876541701121638939361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20837168722268162185252481 15627876541701121638939361)
  ·
    refine ⟨11720907406275841229204521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15627876541701121638939361 11720907406275841229204521)
    ·
      refine ⟨8790680554706880921903391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11720907406275841229204521 8790680554706880921903391)
      ·
        refine ⟨13186020832060321382855087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8790680554706880921903391 13186020832060321382855087)
        ·
          refine ⟨19779031248090482074282631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13186020832060321382855087 19779031248090482074282631)
          ·
            refine ⟨29668546872135723111423947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19779031248090482074282631 29668546872135723111423947)
            ·
              refine ⟨44502820308203584667135921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29668546872135723111423947 44502820308203584667135921)
              ·
                refine ⟨33377115231152688500351941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44502820308203584667135921 33377115231152688500351941)
                ·
                  refine ⟨6258209105841129093815989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33377115231152688500351941 6258209105841129093815989)
                  ·
                    refine ⟨586707103672605852545249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6258209105841129093815989 586707103672605852545249)
                    ·
                      refine ⟨440030327754454389408937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586707103672605852545249 440030327754454389408937)
                      ·
                        rfl

theorem cell23_856956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_856956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856956 prefixEnd_856956 := by exact prefixLift 856956
  have htrace : WordTrace (prefixWord ++ tailWord_856956) baseStart_856956 baseEnd_856956 := by
    simpa [prefixWord, tailWord_856956, baseEnd_856956] using wordTrace_append hprefix tailTrace_856956
  have hstable : (prefixWord ++ tailWord_856956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856956).length < 2 ^ (prefixWord ++ tailWord_856956).sum := by decide
  have hdescent : baseEnd_856956 < baseStart_856956 := by decide
  rcases family_descends (prefixWord ++ tailWord_856956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856959 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_856959 : Nat := 118140960795 + 856959 * 2 ^ 59
def prefixEnd_856959 : Nat := 4983230072969 + 3 ^ 40 * 856959 * 2
def baseEnd_856959 : Nat := 440031868196417877671423

theorem tailTrace_856959 : CollatzResearch.WordTrace tailWord_856959 prefixEnd_856959 440031868196417877671423 := by
  unfold tailWord_856959
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255862502391374790237931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20837241668260916526825287 31255862502391374790237931)
  ·
    refine ⟨46883793753587062185356897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31255862502391374790237931 46883793753587062185356897)
    ·
      refine ⟨35162845315190296639017673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46883793753587062185356897 35162845315190296639017673)
      ·
        refine ⟨26372133986392722479263255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35162845315190296639017673 26372133986392722479263255)
        ·
          refine ⟨39558200979589083718894883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26372133986392722479263255 39558200979589083718894883)
          ·
            refine ⟨59337301469383625578342325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39558200979589083718894883 59337301469383625578342325)
            ·
              refine ⟨5562872012754714897969593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59337301469383625578342325 5562872012754714897969593)
              ·
                refine ⟨4172154009566036173477195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562872012754714897969593 4172154009566036173477195)
                ·
                  refine ⟨6258231014349054260215793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172154009566036173477195 6258231014349054260215793)
                  ·
                    refine ⟨4693673260761790695161845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258231014349054260215793 4693673260761790695161845)
                    ·
                      refine ⟨440031868196417877671423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4693673260761790695161845 440031868196417877671423)
                      ·
                        rfl

theorem cell23_856959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_856959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856959 prefixEnd_856959 := by exact prefixLift 856959
  have htrace : WordTrace (prefixWord ++ tailWord_856959) baseStart_856959 baseEnd_856959 := by
    simpa [prefixWord, tailWord_856959, baseEnd_856959] using wordTrace_append hprefix tailTrace_856959
  have hstable : (prefixWord ++ tailWord_856959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856959).length < 2 ^ (prefixWord ++ tailWord_856959).sum := by decide
  have hdescent : baseEnd_856959 < baseStart_856959 := by decide
  rcases family_descends (prefixWord ++ tailWord_856959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856970 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_856970 : Nat := 118140960795 + 856970 * 2 ^ 59
def prefixEnd_856970 : Nat := 4983230072969 + 3 ^ 40 * 856970 * 2
def baseEnd_856970 : Nat := 48893057387068592737097

theorem tailTrace_856970 : CollatzResearch.WordTrace tailWord_856970 prefixEnd_856970 48893057387068592737097 := by
  unfold tailWord_856970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814065926337880917222091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20837509136901015779258909 7814065926337880917222091)
  ·
    refine ⟨11721098889506821375833137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7814065926337880917222091 11721098889506821375833137)
    ·
      refine ⟨8790824167130116031874853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11721098889506821375833137 8790824167130116031874853)
      ·
        refine ⟨1648279531336896755976535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8790824167130116031874853 1648279531336896755976535)
        ·
          refine ⟨2472419297005345133964803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648279531336896755976535 2472419297005345133964803)
          ·
            refine ⟨3708628945508017700947205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472419297005345133964803 3708628945508017700947205)
            ·
              refine ⟨695367927282753318927601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3708628945508017700947205 695367927282753318927601)
              ·
                refine ⟨521525945462064989195701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695367927282753318927601 521525945462064989195701)
                ·
                  refine ⟨48893057387068592737097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521525945462064989195701 48893057387068592737097)
                  ·
                    rfl

theorem cell23_856970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_856970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_856970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_856970 prefixEnd_856970 := by exact prefixLift 856970
  have htrace : WordTrace (prefixWord ++ tailWord_856970) baseStart_856970 baseEnd_856970 := by
    simpa [prefixWord, tailWord_856970, baseEnd_856970] using wordTrace_append hprefix tailTrace_856970
  have hstable : (prefixWord ++ tailWord_856970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856970).length < 2 ^ (prefixWord ++ tailWord_856970).sum := by decide
  have hdescent : baseEnd_856970 < baseStart_856970 := by decide
  rcases family_descends (prefixWord ++ tailWord_856970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857073 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_857073 : Nat := 118140960795 + 857073 * 2 ^ 59
def prefixEnd_857073 : Nat := 4983230072969 + 3 ^ 40 * 857073 * 2
def baseEnd_857073 : Nat := 146696801663676810548633

theorem tailTrace_857073 : CollatzResearch.WordTrace tailWord_857073 prefixEnd_857073 146696801663676810548633 := by
  unfold tailWord_857073
  simp only [CollatzResearch.WordTrace]
  refine ⟨31260020423978372259887873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20840013615985581506591915 31260020423978372259887873)
  ·
    refine ⟨23445015317983779194915905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31260020423978372259887873 23445015317983779194915905)
    ·
      refine ⟨17583761488487834396186929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23445015317983779194915905 17583761488487834396186929)
      ·
        refine ⟨13187821116365875797140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17583761488487834396186929 13187821116365875797140197)
        ·
          refine ⟨2472716459318601711963787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13187821116365875797140197 2472716459318601711963787)
          ·
            refine ⟨3709074688977902567945681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472716459318601711963787 3709074688977902567945681)
            ·
              refine ⟨2781806016733426925959261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709074688977902567945681 2781806016733426925959261)
              ·
                refine ⟨1043177256275035097234723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2781806016733426925959261 1043177256275035097234723)
                ·
                  refine ⟨1564765884412552645852085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043177256275035097234723 1564765884412552645852085)
                  ·
                    refine ⟨146696801663676810548633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1564765884412552645852085 146696801663676810548633)
                    ·
                      rfl

theorem cell23_857073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_857073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857073 prefixEnd_857073 := by exact prefixLift 857073
  have htrace : WordTrace (prefixWord ++ tailWord_857073) baseStart_857073 baseEnd_857073 := by
    simpa [prefixWord, tailWord_857073, baseEnd_857073] using wordTrace_append hprefix tailTrace_857073
  have hstable : (prefixWord ++ tailWord_857073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857073).length < 2 ^ (prefixWord ++ tailWord_857073).sum := by decide
  have hdescent : baseEnd_857073 < baseStart_857073 := by decide
  rcases family_descends (prefixWord ++ tailWord_857073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857120 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_857120 : Nat := 118140960795 + 857120 * 2 ^ 59
def prefixEnd_857120 : Nat := 4983230072969 + 3 ^ 40 * 857120 * 2
def baseEnd_857120 : Nat := 146704846193930582586061

theorem tailTrace_857120 : CollatzResearch.WordTrace tailWord_857120 prefixEnd_857120 146704846193930582586061 := by
  unfold tailWord_857120
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630867327404049643424407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20841156436538732857899209 15630867327404049643424407)
  ·
    refine ⟨23446300991106074465136611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630867327404049643424407 23446300991106074465136611)
    ·
      refine ⟨35169451486659111697704917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446300991106074465136611 35169451486659111697704917)
      ·
        refine ⟨824284019218572930414959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35169451486659111697704917 824284019218572930414959)
        ·
          refine ⟨1236426028827859395622439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824284019218572930414959 1236426028827859395622439)
          ·
            refine ⟨1854639043241789093433659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236426028827859395622439 1854639043241789093433659)
            ·
              refine ⟨2781958564862683640150489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854639043241789093433659 2781958564862683640150489)
              ·
                refine ⟨2086468923647012730112867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781958564862683640150489 2086468923647012730112867)
                ·
                  refine ⟨3129703385470519095169301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086468923647012730112867 3129703385470519095169301)
                  ·
                    refine ⟨146704846193930582586061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3129703385470519095169301 146704846193930582586061)
                    ·
                      rfl

theorem cell23_857120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_857120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857120 prefixEnd_857120 := by exact prefixLift 857120
  have htrace : WordTrace (prefixWord ++ tailWord_857120) baseStart_857120 baseEnd_857120 := by
    simpa [prefixWord, tailWord_857120, baseEnd_857120] using wordTrace_append hprefix tailTrace_857120
  have hstable : (prefixWord ++ tailWord_857120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857120).length < 2 ^ (prefixWord ++ tailWord_857120).sum := by decide
  have hdescent : baseEnd_857120 < baseStart_857120 := by decide
  rcases family_descends (prefixWord ++ tailWord_857120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857123 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_857123 : Nat := 118140960795 + 857123 * 2 ^ 59
def prefixEnd_857123 : Nat := 4983230072969 + 3 ^ 40 * 857123 * 2
def baseEnd_857123 : Nat := 440116079023755236020669

theorem tailTrace_857123 : CollatzResearch.WordTrace tailWord_857123 prefixEnd_857123 440116079023755236020669 := by
  unfold tailWord_857123
  simp only [CollatzResearch.WordTrace]
  refine ⟨31261844073797230799208023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20841229382531487199472015 31261844073797230799208023)
  ·
    refine ⟨46892766110695846198812035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31261844073797230799208023 46892766110695846198812035)
    ·
      refine ⟨70339149166043769298218053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46892766110695846198812035 70339149166043769298218053)
      ·
        refine ⟨13188590468633206743415885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70339149166043769298218053 13188590468633206743415885)
        ·
          refine ⟨4945721425737452528780957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13188590468633206743415885 4945721425737452528780957)
          ·
            refine ⟨1854645534651544698292859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4945721425737452528780957 1854645534651544698292859)
            ·
              refine ⟨2781968301977317047439289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854645534651544698292859 2781968301977317047439289)
              ·
                refine ⟨2086476226482987785579467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781968301977317047439289 2086476226482987785579467)
                ·
                  refine ⟨3129714339724481678369201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086476226482987785579467 3129714339724481678369201)
                  ·
                    refine ⟨2347285754793361258776901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3129714339724481678369201 2347285754793361258776901)
                    ·
                      refine ⟨440116079023755236020669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2347285754793361258776901 440116079023755236020669)
                      ·
                        rfl

theorem cell23_857123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_857123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857123 prefixEnd_857123 := by exact prefixLift 857123
  have htrace : WordTrace (prefixWord ++ tailWord_857123) baseStart_857123 baseEnd_857123 := by
    simpa [prefixWord, tailWord_857123, baseEnd_857123] using wordTrace_append hprefix tailTrace_857123
  have hstable : (prefixWord ++ tailWord_857123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857123).length < 2 ^ (prefixWord ++ tailWord_857123).sum := by decide
  have hdescent : baseEnd_857123 < baseStart_857123 := by decide
  rcases family_descends (prefixWord ++ tailWord_857123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857144 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_857144 : Nat := 118140960795 + 857144 * 2 ^ 59
def prefixEnd_857144 : Nat := 4983230072969 + 3 ^ 40 * 857144 * 2
def baseEnd_857144 : Nat := 440126862117499653858073

theorem tailTrace_857144 : CollatzResearch.WordTrace tailWord_857144 prefixEnd_857144 440126862117499653858073 := by
  unfold tailWord_857144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631305003360575692861243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20841740004480767590481657 15631305003360575692861243)
  ·
    refine ⟨23446957505040863539291865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15631305003360575692861243 23446957505040863539291865)
    ·
      refine ⟨17585218128780647654468899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23446957505040863539291865 17585218128780647654468899)
      ·
        refine ⟨26377827193170971481703349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17585218128780647654468899 26377827193170971481703349)
        ·
          refine ⟨2472921299359778576409689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26377827193170971481703349 2472921299359778576409689)
          ·
            refine ⟨1854690974519833932307267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472921299359778576409689 1854690974519833932307267)
            ·
              refine ⟨2782036461779750898460901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854690974519833932307267 2782036461779750898460901)
              ·
                refine ⟨521631836583703293461419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2782036461779750898460901 521631836583703293461419)
                ·
                  refine ⟨782447754875554940192129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521631836583703293461419 782447754875554940192129)
                  ·
                    refine ⟨586835816156666205144097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 782447754875554940192129 586835816156666205144097)
                    ·
                      refine ⟨440126862117499653858073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 586835816156666205144097 440126862117499653858073)
                      ·
                        rfl

theorem cell23_857144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_857144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857144 prefixEnd_857144 := by exact prefixLift 857144
  have htrace : WordTrace (prefixWord ++ tailWord_857144) baseStart_857144 baseEnd_857144 := by
    simpa [prefixWord, tailWord_857144, baseEnd_857144] using wordTrace_append hprefix tailTrace_857144
  have hstable : (prefixWord ++ tailWord_857144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857144).length < 2 ^ (prefixWord ++ tailWord_857144).sum := by decide
  have hdescent : baseEnd_857144 < baseStart_857144 := by decide
  rcases family_descends (prefixWord ++ tailWord_857144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857146 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_857146 : Nat := 118140960795 + 857146 * 2 ^ 59
def prefixEnd_857146 : Nat := 4983230072969 + 3 ^ 40 * 857146 * 2
def baseEnd_857146 : Nat := 146709296359602882011021

theorem tailTrace_857146 : CollatzResearch.WordTrace tailWord_857146 prefixEnd_857146 146709296359602882011021 := by
  unfold tailWord_857146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815670738178476431823823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20841788635142603818196861 7815670738178476431823823)
  ·
    refine ⟨11723506107267714647735735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815670738178476431823823 11723506107267714647735735)
    ·
      refine ⟨17585259160901571971603603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723506107267714647735735 17585259160901571971603603)
      ·
        refine ⟨26377888741352357957405405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17585259160901571971603603 26377888741352357957405405)
        ·
          refine ⟨9891708278007134234027027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26377888741352357957405405 9891708278007134234027027)
          ·
            refine ⟨14837562417010701351040541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891708278007134234027027 14837562417010701351040541)
            ·
              refine ⟨5564085906379013006640203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14837562417010701351040541 5564085906379013006640203)
              ·
                refine ⟨8346128859568519509960305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564085906379013006640203 8346128859568519509960305)
                ·
                  refine ⟨6259596644676389632470229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8346128859568519509960305 6259596644676389632470229)
                  ·
                    refine ⟨146709296359602882011021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6259596644676389632470229 146709296359602882011021)
                    ·
                      rfl

theorem cell23_857146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_857146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857146 prefixEnd_857146 := by exact prefixLift 857146
  have htrace : WordTrace (prefixWord ++ tailWord_857146) baseStart_857146 baseEnd_857146 := by
    simpa [prefixWord, tailWord_857146, baseEnd_857146] using wordTrace_append hprefix tailTrace_857146
  have hstable : (prefixWord ++ tailWord_857146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857146).length < 2 ^ (prefixWord ++ tailWord_857146).sum := by decide
  have hdescent : baseEnd_857146 < baseStart_857146 := by decide
  rcases family_descends (prefixWord ++ tailWord_857146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857150 : List Nat := [4, 2, 1, 3, 1, 3, 1, 8]
def baseStart_857150 : Nat := 118140960795 + 857150 * 2 ^ 59
def prefixEnd_857150 : Nat := 4983230072969 + 3 ^ 40 * 857150 * 2
def baseEnd_857150 : Nat := 16301109000052838162335

theorem tailTrace_857150 : CollatzResearch.WordTrace tailWord_857150 prefixEnd_857150 16301109000052838162335 := by
  unfold tailWord_857150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907853605587426801305113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20841885896466276273627269 3907853605587426801305113)
  ·
    refine ⟨2930890204190570100978835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907853605587426801305113 2930890204190570100978835)
    ·
      refine ⟨4396335306285855151468253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930890204190570100978835 4396335306285855151468253)
      ·
        refine ⟨1648625739857195681800595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4396335306285855151468253 1648625739857195681800595)
        ·
          refine ⟨2472938609785793522700893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648625739857195681800595 2472938609785793522700893)
          ·
            refine ⟨927351978669672571012835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2472938609785793522700893 927351978669672571012835)
            ·
              refine ⟨1391027968004508856519253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927351978669672571012835 1391027968004508856519253)
              ·
                refine ⟨16301109000052838162335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1391027968004508856519253 16301109000052838162335)
                ·
                  rfl

theorem cell23_857150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_857150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857150 prefixEnd_857150 := by exact prefixLift 857150
  have htrace : WordTrace (prefixWord ++ tailWord_857150) baseStart_857150 baseEnd_857150 := by
    simpa [prefixWord, tailWord_857150, baseEnd_857150] using wordTrace_append hprefix tailTrace_857150
  have hstable : (prefixWord ++ tailWord_857150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857150).length < 2 ^ (prefixWord ++ tailWord_857150).sum := by decide
  have hdescent : baseEnd_857150 < baseStart_857150 := by decide
  rcases family_descends (prefixWord ++ tailWord_857150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857160 : List Nat := [2, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_857160 : Nat := 118140960795 + 857160 * 2 ^ 59
def prefixEnd_857160 : Nat := 4983230072969 + 3 ^ 40 * 857160 * 2
def baseEnd_857160 : Nat := 440135077807971591257999

theorem tailTrace_857160 : CollatzResearch.WordTrace tailWord_857160 prefixEnd_857160 440135077807971591257999 := by
  unfold tailWord_857160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631596787331593059152467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20842129049775457412203289 15631596787331593059152467)
  ·
    refine ⟨23447395180997389588728701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15631596787331593059152467 23447395180997389588728701)
    ·
      refine ⟨8792773192874021095773263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23447395180997389588728701 8792773192874021095773263)
      ·
        refine ⟨13189159789311031643659895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792773192874021095773263 13189159789311031643659895)
        ·
          refine ⟨19783739683966547465489843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189159789311031643659895 19783739683966547465489843)
          ·
            refine ⟨29675609525949821198234765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19783739683966547465489843 29675609525949821198234765)
            ·
              refine ⟨11128353572231182949338037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29675609525949821198234765 11128353572231182949338037)
              ·
                refine ⟨1043283147396673401500441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11128353572231182949338037 1043283147396673401500441)
                ·
                  refine ⟨782462360547505051125331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043283147396673401500441 782462360547505051125331)
                  ·
                    refine ⟨1173693540821257576687997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 782462360547505051125331 1173693540821257576687997)
                    ·
                      refine ⟨440135077807971591257999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173693540821257576687997 440135077807971591257999)
                      ·
                        rfl

theorem cell23_857160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_857160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857160 prefixEnd_857160 := by exact prefixLift 857160
  have htrace : WordTrace (prefixWord ++ tailWord_857160) baseStart_857160 baseEnd_857160 := by
    simpa [prefixWord, tailWord_857160, baseEnd_857160] using wordTrace_append hprefix tailTrace_857160
  have hstable : (prefixWord ++ tailWord_857160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857160).length < 2 ^ (prefixWord ++ tailWord_857160).sum := by decide
  have hdescent : baseEnd_857160 < baseStart_857160 := by decide
  rcases family_descends (prefixWord ++ tailWord_857160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857176 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_857176 : Nat := 118140960795 + 857176 * 2 ^ 59
def prefixEnd_857176 : Nat := 4983230072969 + 3 ^ 40 * 857176 * 2
def baseEnd_857176 : Nat := 146714431166147842885975

theorem tailTrace_857176 : CollatzResearch.WordTrace tailWord_857176 prefixEnd_857176 146714431166147842885975 := by
  unfold tailWord_857176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631888571302610425443691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20842518095070147233924921 15631888571302610425443691)
  ·
    refine ⟨23447832856953915638165537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15631888571302610425443691 23447832856953915638165537)
    ·
      refine ⟨17585874642715436728624153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23447832856953915638165537 17585874642715436728624153)
      ·
        refine ⟨13189405982036577546468115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17585874642715436728624153 13189405982036577546468115)
        ·
          refine ⟨19784108973054866319702173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189405982036577546468115 19784108973054866319702173)
          ·
            refine ⟨7419040864895574869888315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19784108973054866319702173 7419040864895574869888315)
            ·
              refine ⟨11128561297343362304832473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419040864895574869888315 11128561297343362304832473)
              ·
                refine ⟨8346420973007521728624355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11128561297343362304832473 8346420973007521728624355)
                ·
                  refine ⟨12519631459511282592936533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8346420973007521728624355 12519631459511282592936533)
                  ·
                    refine ⟨146714431166147842885975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12519631459511282592936533 146714431166147842885975)
                    ·
                      rfl

theorem cell23_857176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_857176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857176 prefixEnd_857176 := by exact prefixLift 857176
  have htrace : WordTrace (prefixWord ++ tailWord_857176) baseStart_857176 baseEnd_857176 := by
    simpa [prefixWord, tailWord_857176, baseEnd_857176] using wordTrace_append hprefix tailTrace_857176
  have hstable : (prefixWord ++ tailWord_857176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857176).length < 2 ^ (prefixWord ++ tailWord_857176).sum := by decide
  have hdescent : baseEnd_857176 < baseStart_857176 := by decide
  rcases family_descends (prefixWord ++ tailWord_857176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857181 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_857181 : Nat := 118140960795 + 857181 * 2 ^ 59
def prefixEnd_857181 : Nat := 4983230072969 + 3 ^ 40 * 857181 * 2
def baseEnd_857181 : Nat := 440145860901716009095403

theorem tailTrace_857181 : CollatzResearch.WordTrace tailWord_857181 prefixEnd_857181 440145860901716009095403 := by
  unfold tailWord_857181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31263959507587106704819397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20842639671724737803212931 31263959507587106704819397)
  ·
    refine ⟨5861992407672582507153637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31263959507587106704819397 5861992407672582507153637)
    ·
      refine ⟨1099123576438609220091307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5861992407672582507153637 1099123576438609220091307)
      ·
        refine ⟨1648685364657913830136961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099123576438609220091307 1648685364657913830136961)
        ·
          refine ⟨1236514023493435372602721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1648685364657913830136961 1236514023493435372602721)
          ·
            refine ⟨927385517620076529452041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236514023493435372602721 927385517620076529452041)
            ·
              refine ⟨695539138215057397089031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927385517620076529452041 695539138215057397089031)
              ·
                refine ⟨1043308707322586095633547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695539138215057397089031 1043308707322586095633547)
                ·
                  refine ⟨1564963060983879143450321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043308707322586095633547 1564963060983879143450321)
                  ·
                    refine ⟨1173722295737909357587741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564963060983879143450321 1173722295737909357587741)
                    ·
                      refine ⟨440145860901716009095403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173722295737909357587741 440145860901716009095403)
                      ·
                        rfl

theorem cell23_857181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_857181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857181 prefixEnd_857181 := by exact prefixLift 857181
  have htrace : WordTrace (prefixWord ++ tailWord_857181) baseStart_857181 baseEnd_857181 := by
    simpa [prefixWord, tailWord_857181, baseEnd_857181] using wordTrace_append hprefix tailTrace_857181
  have hstable : (prefixWord ++ tailWord_857181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857181).length < 2 ^ (prefixWord ++ tailWord_857181).sum := by decide
  have hdescent : baseEnd_857181 < baseStart_857181 := by decide
  rcases family_descends (prefixWord ++ tailWord_857181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857194 : List Nat := [3, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_857194 : Nat := 118140960795 + 857194 * 2 ^ 59
def prefixEnd_857194 : Nat := 4983230072969 + 3 ^ 40 * 857194 * 2
def baseEnd_857194 : Nat := 440152536150224458232843

theorem tailTrace_857194 : CollatzResearch.WordTrace tailWord_857194 prefixEnd_857194 440152536150224458232843 := by
  unfold tailWord_857194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816108414135002481260659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20842955771026673283361757 7816108414135002481260659)
  ·
    refine ⟨11724162621202503721890989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7816108414135002481260659 11724162621202503721890989)
    ·
      refine ⟨4396560982950938895709121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11724162621202503721890989 4396560982950938895709121)
      ·
        refine ⟨3297420737213204171781841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396560982950938895709121 3297420737213204171781841)
        ·
          refine ⟨2473065552909903128836381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3297420737213204171781841 2473065552909903128836381)
          ·
            refine ⟨927399582341213673313643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2473065552909903128836381 927399582341213673313643)
            ·
              refine ⟨1391099373511820509970465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927399582341213673313643 1391099373511820509970465)
              ·
                refine ⟨1043324530133865382477849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391099373511820509970465 1043324530133865382477849)
                ·
                  refine ⟨782493397600399036858387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043324530133865382477849 782493397600399036858387)
                  ·
                    refine ⟨1173740096400598555287581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 782493397600399036858387 1173740096400598555287581)
                    ·
                      refine ⟨440152536150224458232843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1173740096400598555287581 440152536150224458232843)
                      ·
                        rfl

theorem cell23_857194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_857194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857194 prefixEnd_857194 := by exact prefixLift 857194
  have htrace : WordTrace (prefixWord ++ tailWord_857194) baseStart_857194 baseEnd_857194 := by
    simpa [prefixWord, tailWord_857194, baseEnd_857194] using wordTrace_append hprefix tailTrace_857194
  have hstable : (prefixWord ++ tailWord_857194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857194).length < 2 ^ (prefixWord ++ tailWord_857194).sum := by decide
  have hdescent : baseEnd_857194 < baseStart_857194 := by decide
  rcases family_descends (prefixWord ++ tailWord_857194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857213 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_857213 : Nat := 118140960795 + 857213 * 2 ^ 59
def prefixEnd_857213 : Nat := 4983230072969 + 3 ^ 40 * 857213 * 2
def baseEnd_857213 : Nat := 440162292282659883895255

theorem tailTrace_857213 : CollatzResearch.WordTrace tailWord_857213 prefixEnd_857213 440162292282659883895255 := by
  unfold tailWord_857213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31265126643471176169984293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20843417762314117446656195 31265126643471176169984293)
  ·
    refine ⟨5862211245650845531872055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31265126643471176169984293 5862211245650845531872055)
    ·
      refine ⟨8793316868476268297808083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862211245650845531872055 8793316868476268297808083)
      ·
        refine ⟨13189975302714402446712125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8793316868476268297808083 13189975302714402446712125)
        ·
          refine ⟨4946240738517900917517047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13189975302714402446712125 4946240738517900917517047)
          ·
            refine ⟨7419361107776851376275571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946240738517900917517047 7419361107776851376275571)
            ·
              refine ⟨11129041661665277064413357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419361107776851376275571 11129041661665277064413357)
              ·
                refine ⟨4173390623124478899155009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11129041661665277064413357 4173390623124478899155009)
                ·
                  refine ⟨3130042967343359174366257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173390623124478899155009 3130042967343359174366257)
                  ·
                    refine ⟨2347532225507519380774693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130042967343359174366257 2347532225507519380774693)
                    ·
                      refine ⟨440162292282659883895255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2347532225507519380774693 440162292282659883895255)
                      ·
                        rfl

theorem cell23_857213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_857213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_857213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_857213 prefixEnd_857213 := by exact prefixLift 857213
  have htrace : WordTrace (prefixWord ++ tailWord_857213) baseStart_857213 baseEnd_857213 := by
    simpa [prefixWord, tailWord_857213, baseEnd_857213] using wordTrace_append hprefix tailTrace_857213
  have hstable : (prefixWord ++ tailWord_857213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857213).length < 2 ^ (prefixWord ++ tailWord_857213).sum := by decide
  have hdescent : baseEnd_857213 < baseStart_857213 := by decide
  rcases family_descends (prefixWord ++ tailWord_857213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
