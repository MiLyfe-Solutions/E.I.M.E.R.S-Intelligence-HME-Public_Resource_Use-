import V185TrunkScan22Chunk205

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1835898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1835898 : Nat := 118140960795 + 1835898 * 2 ^ 59
def prefixEnd_1835898 : Nat := 4983230072969 + 3 ^ 40 * 1835898 * 2
def baseEnd_1835898 : Nat := 628465404418775516221243

theorem tailTrace_1835898 : CollatzResearch.WordTrace tailWord_1835898 prefixEnd_1835898 628465404418775516221243 := by
  unfold tailWord_1835898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740175275715641815201087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44640467401908378173869565 16740175275715641815201087)
  ·
    refine ⟨25110262913573462722801631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740175275715641815201087 25110262913573462722801631)
    ·
      refine ⟨37665394370360194084202447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25110262913573462722801631 37665394370360194084202447)
      ·
        refine ⟨56498091555540291126303671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37665394370360194084202447 56498091555540291126303671)
        ·
          refine ⟨84747137333310436689455507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56498091555540291126303671 84747137333310436689455507)
          ·
            refine ⟨127120705999965655034183261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84747137333310436689455507 127120705999965655034183261)
            ·
              refine ⟨47670264749987120637818723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127120705999965655034183261 47670264749987120637818723)
              ·
                refine ⟨71505397124980680956728085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47670264749987120637818723 71505397124980680956728085)
                ·
                  refine ⟨3351815490233469419846629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71505397124980680956728085 3351815490233469419846629)
                  ·
                    refine ⟨628465404418775516221243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3351815490233469419846629 628465404418775516221243)
                    ·
                      rfl

theorem cell22_1835898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1835898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835898 prefixEnd_1835898 := by exact prefixLift 1835898
  have htrace : WordTrace (prefixWord ++ tailWord_1835898) baseStart_1835898 baseEnd_1835898 := by
    simpa [prefixWord, tailWord_1835898, baseEnd_1835898] using wordTrace_append hprefix tailTrace_1835898
  have hstable : (prefixWord ++ tailWord_1835898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835898).length < 2 ^ (prefixWord ++ tailWord_1835898).sum := by decide
  have hdescent : baseEnd_1835898 < baseStart_1835898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835913 : List Nat := [1, 2, 1, 1, 5, 2, 2, 8]
def baseStart_1835913 : Nat := 118140960795 + 1835913 * 2 ^ 59
def prefixEnd_1835913 : Nat := 4983230072969 + 3 ^ 40 * 1835913 * 2
def baseEnd_1835913 : Nat := 69830059913924497455133

theorem tailTrace_1835913 : CollatzResearch.WordTrace tailWord_1835913 prefixEnd_1835913 69830059913924497455133 := by
  unfold tailWord_1835913
  simp only [CollatzResearch.WordTrace]
  refine ⟨66961248197808224822600393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44640832131872149881733595 66961248197808224822600393)
  ·
    refine ⟨50220936148356168616950295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66961248197808224822600393 50220936148356168616950295)
    ·
      refine ⟨75331404222534252925425443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50220936148356168616950295 75331404222534252925425443)
      ·
        refine ⟨112997106333801379388138165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75331404222534252925425443 112997106333801379388138165)
        ·
          refine ⟨10593478718793879317637953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112997106333801379388138165 10593478718793879317637953)
          ·
            refine ⟨7945109039095409488228465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10593478718793879317637953 7945109039095409488228465)
            ·
              refine ⟨5958831779321557116171349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945109039095409488228465 5958831779321557116171349)
              ·
                refine ⟨69830059913924497455133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5958831779321557116171349 69830059913924497455133)
                ·
                  rfl

theorem cell22_1835913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 8].length) (baseStart_1835913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835913 prefixEnd_1835913 := by exact prefixLift 1835913
  have htrace : WordTrace (prefixWord ++ tailWord_1835913) baseStart_1835913 baseEnd_1835913 := by
    simpa [prefixWord, tailWord_1835913, baseEnd_1835913] using wordTrace_append hprefix tailTrace_1835913
  have hstable : (prefixWord ++ tailWord_1835913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835913).length < 2 ^ (prefixWord ++ tailWord_1835913).sum := by decide
  have hdescent : baseEnd_1835913 < baseStart_1835913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835930 : List Nat := [3, 1, 1, 4, 4, 9]
def baseStart_1835930 : Nat := 118140960795 + 1835930 * 2 ^ 59
def prefixEnd_1835930 : Nat := 4983230072969 + 3 ^ 40 * 1835930 * 2
def baseEnd_1835930 : Nat := 7758967391021458017545

theorem tailTrace_1835930 : CollatzResearch.WordTrace tailWord_1835930 prefixEnd_1835930 7758967391021458017545 := by
  unfold tailWord_1835930
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740467059686659181492311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44641245492497757817312829 16740467059686659181492311)
  ·
    refine ⟨25110700589529988772238467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16740467059686659181492311 25110700589529988772238467)
    ·
      refine ⟨37666050884294983158357701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25110700589529988772238467 37666050884294983158357701)
      ·
        refine ⟨7062384540805309342192069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37666050884294983158357701 7062384540805309342192069)
        ·
          refine ⟨1324197101400995501661013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7062384540805309342192069 1324197101400995501661013)
          ·
            refine ⟨7758967391021458017545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1324197101400995501661013 7758967391021458017545)
            ·
              rfl

theorem cell22_1835930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 9].length) (baseStart_1835930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835930 prefixEnd_1835930 := by exact prefixLift 1835930
  have htrace : WordTrace (prefixWord ++ tailWord_1835930) baseStart_1835930 baseEnd_1835930 := by
    simpa [prefixWord, tailWord_1835930, baseEnd_1835930] using wordTrace_append hprefix tailTrace_1835930
  have hstable : (prefixWord ++ tailWord_1835930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835930).length < 2 ^ (prefixWord ++ tailWord_1835930).sum := by decide
  have hdescent : baseEnd_1835930 < baseStart_1835930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835945 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_1835945 : Nat := 118140960795 + 1835945 * 2 ^ 59
def prefixEnd_1835945 : Nat := 4983230072969 + 3 ^ 40 * 1835945 * 2
def baseEnd_1835945 : Nat := 628481493479283060296099

theorem tailTrace_1835945 : CollatzResearch.WordTrace tailWord_1835945 prefixEnd_1835945 628481493479283060296099 := by
  unfold tailWord_1835945
  simp only [CollatzResearch.WordTrace]
  refine ⟨66962415333692294287765289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44641610222461529525176859 66962415333692294287765289)
  ·
    refine ⟨50221811500269220715823967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66962415333692294287765289 50221811500269220715823967)
    ·
      refine ⟨75332717250403831073735951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50221811500269220715823967 75332717250403831073735951)
      ·
        refine ⟨112999075875605746610603927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75332717250403831073735951 112999075875605746610603927)
        ·
          refine ⟨169498613813408619915905891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112999075875605746610603927 169498613813408619915905891)
          ·
            refine ⟨254247920720112929873858837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169498613813408619915905891 254247920720112929873858837)
            ·
              refine ⟨11917871283755293587837133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254247920720112929873858837 11917871283755293587837133)
              ·
                refine ⟨4469201731408235095438925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11917871283755293587837133 4469201731408235095438925)
                ·
                  refine ⟨1675950649278088160789597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4469201731408235095438925 1675950649278088160789597)
                  ·
                    refine ⟨628481493479283060296099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675950649278088160789597 628481493479283060296099)
                    ·
                      rfl

theorem cell22_1835945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_1835945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835945 prefixEnd_1835945 := by exact prefixLift 1835945
  have htrace : WordTrace (prefixWord ++ tailWord_1835945) baseStart_1835945 baseEnd_1835945 := by
    simpa [prefixWord, tailWord_1835945, baseEnd_1835945] using wordTrace_append hprefix tailTrace_1835945
  have hstable : (prefixWord ++ tailWord_1835945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835945).length < 2 ^ (prefixWord ++ tailWord_1835945).sum := by decide
  have hdescent : baseEnd_1835945 < baseStart_1835945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835979 : List Nat := [1, 1, 1, 1, 3, 6, 2, 3, 1, 3]
def baseStart_1835979 : Nat := 118140960795 + 1835979 * 2 ^ 59
def prefixEnd_1835979 : Nat := 4983230072969 + 3 ^ 40 * 1835979 * 2
def baseEnd_1835979 : Nat := 628493132374118304945995

theorem tailTrace_1835979 : CollatzResearch.WordTrace tailWord_1835979 prefixEnd_1835979 628493132374118304945995 := by
  unfold tailWord_1835979
  simp only [CollatzResearch.WordTrace]
  refine ⟨66963655415569118094502991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44642436943712745396335327 66963655415569118094502991)
  ·
    refine ⟨100445483123353677141754487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66963655415569118094502991 100445483123353677141754487)
    ·
      refine ⟨150668224685030515712631731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100445483123353677141754487 150668224685030515712631731)
      ·
        refine ⟨226002337027545773568947597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150668224685030515712631731 226002337027545773568947597)
        ·
          refine ⟨84750876385329665088355349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226002337027545773568947597 84750876385329665088355349)
          ·
            refine ⟨3972697330562328051016657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84750876385329665088355349 3972697330562328051016657)
            ·
              refine ⟨2979522997921746038262493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972697330562328051016657 2979522997921746038262493)
              ·
                refine ⟨1117321124220654764348435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979522997921746038262493 1117321124220654764348435)
                ·
                  refine ⟨1675981686330982146522653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117321124220654764348435 1675981686330982146522653)
                  ·
                    refine ⟨628493132374118304945995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675981686330982146522653 628493132374118304945995)
                    ·
                      rfl

theorem cell22_1835979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 3, 1, 3].length) (baseStart_1835979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835979 prefixEnd_1835979 := by exact prefixLift 1835979
  have htrace : WordTrace (prefixWord ++ tailWord_1835979) baseStart_1835979 baseEnd_1835979 := by
    simpa [prefixWord, tailWord_1835979, baseEnd_1835979] using wordTrace_append hprefix tailTrace_1835979
  have hstable : (prefixWord ++ tailWord_1835979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835979).length < 2 ^ (prefixWord ++ tailWord_1835979).sum := by decide
  have hdescent : baseEnd_1835979 < baseStart_1835979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835992 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_1835992 : Nat := 118140960795 + 1835992 * 2 ^ 59
def prefixEnd_1835992 : Nat := 4983230072969 + 3 ^ 40 * 1835992 * 2
def baseEnd_1835992 : Nat := 209499194179930201456985

theorem tailTrace_1835992 : CollatzResearch.WordTrace tailWord_1835992 prefixEnd_1835992 209499194179930201456985 := by
  unfold tailWord_1835992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33482064782261010657363115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44642753043014680876484153 33482064782261010657363115)
  ·
    refine ⟨50223097173391515986044673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33482064782261010657363115 50223097173391515986044673)
    ·
      refine ⟨37667322880043636989533505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50223097173391515986044673 37667322880043636989533505)
      ·
        refine ⟨28250492160032727742150129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37667322880043636989533505 28250492160032727742150129)
        ·
          refine ⟨21187869120024545806612597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28250492160032727742150129 21187869120024545806612597)
          ·
            refine ⟨1986362730002301169369931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21187869120024545806612597 1986362730002301169369931)
            ·
              refine ⟨2979544095003451754054897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986362730002301169369931 2979544095003451754054897)
              ·
                refine ⟨2234658071252588815541173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979544095003451754054897 2234658071252588815541173)
                ·
                  refine ⟨209499194179930201456985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234658071252588815541173 209499194179930201456985)
                  ·
                    rfl

theorem cell22_1835992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_1835992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1835992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1835992 prefixEnd_1835992 := by exact prefixLift 1835992
  have htrace : WordTrace (prefixWord ++ tailWord_1835992) baseStart_1835992 baseEnd_1835992 := by
    simpa [prefixWord, tailWord_1835992, baseEnd_1835992] using wordTrace_append hprefix tailTrace_1835992
  have hstable : (prefixWord ++ tailWord_1835992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835992).length < 2 ^ (prefixWord ++ tailWord_1835992).sum := by decide
  have hdescent : baseEnd_1835992 < baseStart_1835992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836030 : List Nat := [4, 2, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1836030 : Nat := 118140960795 + 1836030 * 2 ^ 59
def prefixEnd_1836030 : Nat := 4983230072969 + 3 ^ 40 * 1836030 * 2
def baseEnd_1836030 : Nat := 628510590716371171920839

theorem tailTrace_1836030 : CollatzResearch.WordTrace tailWord_1836030 prefixEnd_1836030 628510590716371171920839 := by
  unfold tailWord_1836030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370689442298044225576193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44643677025589569203073029 8370689442298044225576193)
  ·
    refine ⟨6278017081723533169182145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8370689442298044225576193 6278017081723533169182145)
    ·
      refine ⟨4708512811292649876886609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6278017081723533169182145 4708512811292649876886609)
      ·
        refine ⟨3531384608469487407664957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708512811292649876886609 3531384608469487407664957)
        ·
          refine ⟨1324269228176057777874359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3531384608469487407664957 1324269228176057777874359)
          ·
            refine ⟨1986403842264086666811539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324269228176057777874359 1986403842264086666811539)
            ·
              refine ⟨2979605763396130000217309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986403842264086666811539 2979605763396130000217309)
              ·
                refine ⟨1117352161273548750081491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979605763396130000217309 1117352161273548750081491)
                ·
                  refine ⟨1676028241910323125122237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117352161273548750081491 1676028241910323125122237)
                  ·
                    refine ⟨628510590716371171920839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676028241910323125122237 628510590716371171920839)
                    ·
                      rfl

theorem cell22_1836030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1836030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836030 prefixEnd_1836030 := by exact prefixLift 1836030
  have htrace : WordTrace (prefixWord ++ tailWord_1836030) baseStart_1836030 baseEnd_1836030 := by
    simpa [prefixWord, tailWord_1836030, baseEnd_1836030] using wordTrace_append hprefix tailTrace_1836030
  have hstable : (prefixWord ++ tailWord_1836030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836030).length < 2 ^ (prefixWord ++ tailWord_1836030).sum := by decide
  have hdescent : baseEnd_1836030 < baseStart_1836030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836065 : List Nat := [1, 2, 3, 2, 3, 1, 1, 9]
def baseStart_1836065 : Nat := 118140960795 + 1836065 * 2 ^ 59
def prefixEnd_1836065 : Nat := 4983230072969 + 3 ^ 40 * 1836065 * 2
def baseEnd_1836065 : Nat := 69835841325738083032859

theorem tailTrace_1836065 : CollatzResearch.WordTrace tailWord_1836065 prefixEnd_1836065 69835841325738083032859 := by
  unfold tailWord_1836065
  simp only [CollatzResearch.WordTrace]
  refine ⟨66966792093257554782133649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44644528062171703188089099 66966792093257554782133649)
  ·
    refine ⟨50225094069943166086600237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66966792093257554782133649 50225094069943166086600237)
    ·
      refine ⟨18834410276228687282475089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50225094069943166086600237 18834410276228687282475089)
      ·
        refine ⟨14125807707171515461856317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18834410276228687282475089 14125807707171515461856317)
        ·
          refine ⟨5297177890189318298196119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14125807707171515461856317 5297177890189318298196119)
          ·
            refine ⟨7945766835283977447294179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297177890189318298196119 7945766835283977447294179)
            ·
              refine ⟨11918650252925966170941269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945766835283977447294179 11918650252925966170941269)
              ·
                refine ⟨69835841325738083032859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11918650252925966170941269 69835841325738083032859)
                ·
                  rfl

theorem cell22_1836065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 9].length) (baseStart_1836065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836065 prefixEnd_1836065 := by exact prefixLift 1836065
  have htrace : WordTrace (prefixWord ++ tailWord_1836065) baseStart_1836065 baseEnd_1836065 := by
    simpa [prefixWord, tailWord_1836065, baseEnd_1836065] using wordTrace_append hprefix tailTrace_1836065
  have hstable : (prefixWord ++ tailWord_1836065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836065).length < 2 ^ (prefixWord ++ tailWord_1836065).sum := by decide
  have hdescent : baseEnd_1836065 < baseStart_1836065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836084 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1836084 : Nat := 118140960795 + 1836084 * 2 ^ 59
def prefixEnd_1836084 : Nat := 4983230072969 + 3 ^ 40 * 1836084 * 2
def baseEnd_1836084 : Nat := 628529076019933031070673

theorem tailTrace_1836084 : CollatzResearch.WordTrace tailWord_1836084 prefixEnd_1836084 628529076019933031070673 := by
  unfold tailWord_1836084
  simp only [CollatzResearch.WordTrace]
  refine ⟨33483742540094360513537653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44644990053459147351383537 33483742540094360513537653)
  ·
    refine ⟨3139100863133846298144155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33483742540094360513537653 3139100863133846298144155)
    ·
      refine ⟨4708651294700769447216233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139100863133846298144155 4708651294700769447216233)
      ·
        refine ⟨3531488471025577085412175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708651294700769447216233 3531488471025577085412175)
        ·
          refine ⟨5297232706538365628118263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531488471025577085412175 5297232706538365628118263)
          ·
            refine ⟨7945849059807548442177395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297232706538365628118263 7945849059807548442177395)
            ·
              refine ⟨11918773589711322663266093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945849059807548442177395 11918773589711322663266093)
              ·
                refine ⟨4469540096141745998724785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11918773589711322663266093 4469540096141745998724785)
                ·
                  refine ⟨3352155072106309499043589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4469540096141745998724785 3352155072106309499043589)
                  ·
                    refine ⟨628529076019933031070673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352155072106309499043589 628529076019933031070673)
                    ·
                      rfl

theorem cell22_1836084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1836084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836084 prefixEnd_1836084 := by exact prefixLift 1836084
  have htrace : WordTrace (prefixWord ++ tailWord_1836084) baseStart_1836084 baseEnd_1836084 := by
    simpa [prefixWord, tailWord_1836084, baseEnd_1836084] using wordTrace_append hprefix tailTrace_1836084
  have hstable : (prefixWord ++ tailWord_1836084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836084).length < 2 ^ (prefixWord ++ tailWord_1836084).sum := by decide
  have hdescent : baseEnd_1836084 < baseStart_1836084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836191 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1836191 : Nat := 118140960795 + 1836191 * 2 ^ 59
def prefixEnd_1836191 : Nat := 4983230072969 + 3 ^ 40 * 1836191 * 2
def baseEnd_1836191 : Nat := 628565704306620418645345

theorem tailTrace_1836191 : CollatzResearch.WordTrace tailWord_1836191 prefixEnd_1836191 628565704306620418645345 := by
  unfold tailWord_1836191
  simp only [CollatzResearch.WordTrace]
  refine ⟨66971387690801078301220427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44647591793867385534146951 66971387690801078301220427)
  ·
    refine ⟨100457081536201617451830641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66971387690801078301220427 100457081536201617451830641)
    ·
      refine ⟨75342811152151213088872981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100457081536201617451830641 75342811152151213088872981)
      ·
        refine ⟨3531694272757088113540921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75342811152151213088872981 3531694272757088113540921)
        ·
          refine ⟨2648770704567816085155691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531694272757088113540921 2648770704567816085155691)
          ·
            refine ⟨3973156056851724127733537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648770704567816085155691 3973156056851724127733537)
            ·
              refine ⟨2979867042638793095800153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973156056851724127733537 2979867042638793095800153)
              ·
                refine ⟨2234900281979094821850115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979867042638793095800153 2234900281979094821850115)
                ·
                  refine ⟨3352350422968642232775173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234900281979094821850115 3352350422968642232775173)
                  ·
                    refine ⟨628565704306620418645345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352350422968642232775173 628565704306620418645345)
                    ·
                      rfl

theorem cell22_1836191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1836191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836191 prefixEnd_1836191 := by exact prefixLift 1836191
  have htrace : WordTrace (prefixWord ++ tailWord_1836191) baseStart_1836191 baseEnd_1836191 := by
    simpa [prefixWord, tailWord_1836191, baseEnd_1836191] using wordTrace_append hprefix tailTrace_1836191
  have hstable : (prefixWord ++ tailWord_1836191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836191).length < 2 ^ (prefixWord ++ tailWord_1836191).sum := by decide
  have hdescent : baseEnd_1836191 < baseStart_1836191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836217 : List Nat := [1, 2, 1, 4, 1, 5, 8]
def baseStart_1836217 : Nat := 118140960795 + 1836217 * 2 ^ 59
def prefixEnd_1836217 : Nat := 4983230072969 + 3 ^ 40 * 1836217 * 2
def baseEnd_1836217 : Nat := 23280540912517222870195

theorem tailTrace_1836217 : CollatzResearch.WordTrace tailWord_1836217 prefixEnd_1836217 23280540912517222870195 := by
  unfold tailWord_1836217
  simp only [CollatzResearch.WordTrace]
  refine ⟨66972335988706884741666905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44648223992471256494444603 66972335988706884741666905)
  ·
    refine ⟨50229251991530163556250179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66972335988706884741666905 50229251991530163556250179)
    ·
      refine ⟨75343877987295245334375269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50229251991530163556250179 75343877987295245334375269)
      ·
        refine ⟨14126977122617858500195363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75343877987295245334375269 14126977122617858500195363)
        ·
          refine ⟨21190465683926787750293045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126977122617858500195363 21190465683926787750293045)
          ·
            refine ⟨1986606157868136351589973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21190465683926787750293045 1986606157868136351589973)
            ·
              refine ⟨23280540912517222870195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1986606157868136351589973 23280540912517222870195)
              ·
                rfl

theorem cell22_1836217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 8].length) (baseStart_1836217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836217 prefixEnd_1836217 := by exact prefixLift 1836217
  have htrace : WordTrace (prefixWord ++ tailWord_1836217) baseStart_1836217 baseEnd_1836217 := by
    simpa [prefixWord, tailWord_1836217, baseEnd_1836217] using wordTrace_append hprefix tailTrace_1836217
  have hstable : (prefixWord ++ tailWord_1836217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836217).length < 2 ^ (prefixWord ++ tailWord_1836217).sum := by decide
  have hdescent : baseEnd_1836217 < baseStart_1836217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836309 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1836309 : Nat := 118140960795 + 1836309 * 2 ^ 59
def prefixEnd_1836309 : Nat := 4983230072969 + 3 ^ 40 * 1836309 * 2
def baseEnd_1836309 : Nat := 628606098118107444194983

theorem tailTrace_1836309 : CollatzResearch.WordTrace tailWord_1836309 prefixEnd_1836309 628606098118107444194983 := by
  unfold tailWord_1836309
  simp only [CollatzResearch.WordTrace]
  refine ⟨66975691504373584454015981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44650461002915722969343987 66975691504373584454015981)
  ·
    refine ⟨25115884314140094170255993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66975691504373584454015981 25115884314140094170255993)
    ·
      refine ⟨18836913235605070627691995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25115884314140094170255993 18836913235605070627691995)
      ·
        refine ⟨28255369853407605941537993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18836913235605070627691995 28255369853407605941537993)
        ·
          refine ⟨21191527390055704456153495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28255369853407605941537993 21191527390055704456153495)
          ·
            refine ⟨31787291085083556684230243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191527390055704456153495 31787291085083556684230243)
            ·
              refine ⟨47680936627625335026345365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31787291085083556684230243 47680936627625335026345365)
              ·
                refine ⟨2235043904419937579359939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47680936627625335026345365 2235043904419937579359939)
                ·
                  refine ⟨3352565856629906369039909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235043904419937579359939 3352565856629906369039909)
                  ·
                    refine ⟨628606098118107444194983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352565856629906369039909 628606098118107444194983)
                    ·
                      rfl

theorem cell22_1836309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1836309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836309 prefixEnd_1836309 := by exact prefixLift 1836309
  have htrace : WordTrace (prefixWord ++ tailWord_1836309) baseStart_1836309 baseEnd_1836309 := by
    simpa [prefixWord, tailWord_1836309, baseEnd_1836309] using wordTrace_append hprefix tailTrace_1836309
  have hstable : (prefixWord ++ tailWord_1836309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836309).length < 2 ^ (prefixWord ++ tailWord_1836309).sum := by decide
  have hdescent : baseEnd_1836309 < baseStart_1836309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836341 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 4]
def baseStart_1836341 : Nat := 118140960795 + 1836341 * 2 ^ 59
def prefixEnd_1836341 : Nat := 4983230072969 + 3 ^ 40 * 1836341 * 2
def baseEnd_1836341 : Nat := 209539017457356675798295

theorem tailTrace_1836341 : CollatzResearch.WordTrace tailWord_1836341 prefixEnd_1836341 209539017457356675798295 := by
  unfold tailWord_1836341
  simp only [CollatzResearch.WordTrace]
  refine ⟨66976858640257653919180877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44651239093505102612787251 66976858640257653919180877)
  ·
    refine ⟨25116321990096620219692829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66976858640257653919180877 25116321990096620219692829)
    ·
      refine ⟨9418620746286232582384811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25116321990096620219692829 9418620746286232582384811)
      ·
        refine ⟨14127931119429348873577217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9418620746286232582384811 14127931119429348873577217)
        ·
          refine ⟨10595948339572011655182913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14127931119429348873577217 10595948339572011655182913)
          ·
            refine ⟨7946961254679008741387185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595948339572011655182913 7946961254679008741387185)
            ·
              refine ⟨5960220941009256556040389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946961254679008741387185 5960220941009256556040389)
              ·
                refine ⟨1117541426439235604257573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5960220941009256556040389 1117541426439235604257573)
                ·
                  refine ⟨209539017457356675798295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117541426439235604257573 209539017457356675798295)
                  ·
                    rfl

theorem cell22_1836341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_1836341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836341 prefixEnd_1836341 := by exact prefixLift 1836341
  have htrace : WordTrace (prefixWord ++ tailWord_1836341) baseStart_1836341 baseEnd_1836341 := by
    simpa [prefixWord, tailWord_1836341, baseEnd_1836341] using wordTrace_append hprefix tailTrace_1836341
  have hstable : (prefixWord ++ tailWord_1836341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836341).length < 2 ^ (prefixWord ++ tailWord_1836341).sum := by decide
  have hdescent : baseEnd_1836341 < baseStart_1836341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836352 : List Nat := [2, 1, 1, 2, 2, 1, 4, 9]
def baseStart_1836352 : Nat := 118140960795 + 1836352 * 2 ^ 59
def prefixEnd_1836352 : Nat := 4983230072969 + 3 ^ 40 * 1836352 * 2
def baseEnd_1836352 : Nat := 69846757544096629485539

theorem tailTrace_1836352 : CollatzResearch.WordTrace tailWord_1836352 prefixEnd_1836352 69846757544096629485539 := by
  unfold tailWord_1836352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33488629921608901398915655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44651506562145201865220873 33488629921608901398915655)
  ·
    refine ⟨50232944882413352098373483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33488629921608901398915655 50232944882413352098373483)
    ·
      refine ⟨75349417323620028147560225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50232944882413352098373483 75349417323620028147560225)
      ·
        refine ⟨56512062992715021110670169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75349417323620028147560225 56512062992715021110670169)
        ·
          refine ⟨42384047244536265833002627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56512062992715021110670169 42384047244536265833002627)
          ·
            refine ⟨63576070866804398749503941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42384047244536265833002627 63576070866804398749503941)
            ·
              refine ⟨11920513287525824765531989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63576070866804398749503941 11920513287525824765531989)
              ·
                refine ⟨69846757544096629485539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11920513287525824765531989 69846757544096629485539)
                ·
                  rfl

theorem cell22_1836352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_1836352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836352 prefixEnd_1836352 := by exact prefixLift 1836352
  have htrace : WordTrace (prefixWord ++ tailWord_1836352) baseStart_1836352 baseEnd_1836352 := by
    simpa [prefixWord, tailWord_1836352, baseEnd_1836352] using wordTrace_append hprefix tailTrace_1836352
  have hstable : (prefixWord ++ tailWord_1836352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836352).length < 2 ^ (prefixWord ++ tailWord_1836352).sum := by decide
  have hdescent : baseEnd_1836352 < baseStart_1836352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836401 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_1836401 : Nat := 118140960795 + 1836401 * 2 ^ 59
def prefixEnd_1836401 : Nat := 4983230072969 + 3 ^ 40 * 1836401 * 2
def baseEnd_1836401 : Nat := 628637591598249870894701

theorem tailTrace_1836401 : CollatzResearch.WordTrace tailWord_1836401 prefixEnd_1836401 628637591598249870894701 := by
  unfold tailWord_1836401
  simp only [CollatzResearch.WordTrace]
  refine ⟨66979047020040284166365057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44652698013360189444243371 66979047020040284166365057)
  ·
    refine ⟨50234285265030213124773793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66979047020040284166365057 50234285265030213124773793)
    ·
      refine ⟨37675713948772659843580345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50234285265030213124773793 37675713948772659843580345)
      ·
        refine ⟨28256785461579494882685259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37675713948772659843580345 28256785461579494882685259)
        ·
          refine ⟨42385178192369242324027889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28256785461579494882685259 42385178192369242324027889)
          ·
            refine ⟨31788883644276931743020917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42385178192369242324027889 31788883644276931743020917)
            ·
              refine ⟨2980207841650962350908211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31788883644276931743020917 2980207841650962350908211)
              ·
                refine ⟨4470311762476443526362317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980207841650962350908211 4470311762476443526362317)
                ·
                  refine ⟨1676366910928666322385869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4470311762476443526362317 1676366910928666322385869)
                  ·
                    refine ⟨628637591598249870894701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676366910928666322385869 628637591598249870894701)
                    ·
                      rfl

theorem cell22_1836401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_1836401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836401 prefixEnd_1836401 := by exact prefixLift 1836401
  have htrace : WordTrace (prefixWord ++ tailWord_1836401) baseStart_1836401 baseEnd_1836401 := by
    simpa [prefixWord, tailWord_1836401, baseEnd_1836401] using wordTrace_append hprefix tailTrace_1836401
  have hstable : (prefixWord ++ tailWord_1836401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836401).length < 2 ^ (prefixWord ++ tailWord_1836401).sum := by decide
  have hdescent : baseEnd_1836401 < baseStart_1836401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836525 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_1836525 : Nat := 118140960795 + 1836525 * 2 ^ 59
def prefixEnd_1836525 : Nat := 4983230072969 + 3 ^ 40 * 1836525 * 2
def baseEnd_1836525 : Nat := 628680039332354880794321

theorem tailTrace_1836525 : CollatzResearch.WordTrace tailWord_1836525 prefixEnd_1836525 628680039332354880794321 := by
  unfold tailWord_1836525
  simp only [CollatzResearch.WordTrace]
  refine ⟨66983569671591053343879029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44655713114394035562586019 66983569671591053343879029)
  ·
    refine ⟨6279709656711661250988659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66983569671591053343879029 6279709656711661250988659)
    ·
      refine ⟨9419564485067491876482989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6279709656711661250988659 9419564485067491876482989)
      ·
        refine ⟨3532336681900309453681121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9419564485067491876482989 3532336681900309453681121)
        ·
          refine ⟨2649252511425232090260841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532336681900309453681121 2649252511425232090260841)
          ·
            refine ⟨1986939383568924067695631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649252511425232090260841 1986939383568924067695631)
            ·
              refine ⟨2980409075353386101543447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986939383568924067695631 2980409075353386101543447)
              ·
                refine ⟨4470613613030079152315171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980409075353386101543447 4470613613030079152315171)
                ·
                  refine ⟨6705920419545118728472757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470613613030079152315171 6705920419545118728472757)
                  ·
                    refine ⟨628680039332354880794321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6705920419545118728472757 628680039332354880794321)
                    ·
                      rfl

theorem cell22_1836525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_1836525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836525 prefixEnd_1836525 := by exact prefixLift 1836525
  have htrace : WordTrace (prefixWord ++ tailWord_1836525) baseStart_1836525 baseEnd_1836525 := by
    simpa [prefixWord, tailWord_1836525, baseEnd_1836525] using wordTrace_append hprefix tailTrace_1836525
  have hstable : (prefixWord ++ tailWord_1836525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836525).length < 2 ^ (prefixWord ++ tailWord_1836525).sum := by decide
  have hdescent : baseEnd_1836525 < baseStart_1836525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836557 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1836557 : Nat := 118140960795 + 1836557 * 2 ^ 59
def prefixEnd_1836557 : Nat := 4983230072969 + 3 ^ 40 * 1836557 * 2
def baseEnd_1836557 : Nat := 628690993586317463994223

theorem tailTrace_1836557 : CollatzResearch.WordTrace tailWord_1836557 prefixEnd_1836557 628690993586317463994223 := by
  unfold tailWord_1836557
  simp only [CollatzResearch.WordTrace]
  refine ⟨66984736807475122809043925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44656491204983415206029283 66984736807475122809043925)
  ·
    refine ⟨1569954768925198190836967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66984736807475122809043925 1569954768925198190836967)
    ·
      refine ⟨2354932153387797286255451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1569954768925198190836967 2354932153387797286255451)
      ·
        refine ⟨3532398230081695929383177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354932153387797286255451 3532398230081695929383177)
        ·
          refine ⟨2649298672561271947037383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532398230081695929383177 2649298672561271947037383)
          ·
            refine ⟨3973948008841907920556075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649298672561271947037383 3973948008841907920556075)
            ·
              refine ⟨5960922013262861880834113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973948008841907920556075 5960922013262861880834113)
              ·
                refine ⟨4470691509947146410625585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5960922013262861880834113 4470691509947146410625585)
                ·
                  refine ⟨3353018632460359807969189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470691509947146410625585 3353018632460359807969189)
                  ·
                    refine ⟨628690993586317463994223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353018632460359807969189 628690993586317463994223)
                    ·
                      rfl

theorem cell22_1836557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1836557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836557 prefixEnd_1836557 := by exact prefixLift 1836557
  have htrace : WordTrace (prefixWord ++ tailWord_1836557) baseStart_1836557 baseEnd_1836557 := by
    simpa [prefixWord, tailWord_1836557, baseEnd_1836557] using wordTrace_append hprefix tailTrace_1836557
  have hstable : (prefixWord ++ tailWord_1836557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836557).length < 2 ^ (prefixWord ++ tailWord_1836557).sum := by decide
  have hdescent : baseEnd_1836557 < baseStart_1836557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836621 : List Nat := [1, 6, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1836621 : Nat := 118140960795 + 1836621 * 2 ^ 59
def prefixEnd_1836621 : Nat := 4983230072969 + 3 ^ 40 * 1836621 * 2
def baseEnd_1836621 : Nat := 628712902094242630394027

theorem tailTrace_1836621 : CollatzResearch.WordTrace tailWord_1836621 prefixEnd_1836621 628712902094242630394027 := by
  unfold tailWord_1836621
  simp only [CollatzResearch.WordTrace]
  refine ⟨66987071079243261739373717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44658047386162174492915811 66987071079243261739373717)
  ·
    refine ⟨3140018956839527894033143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66987071079243261739373717 3140018956839527894033143)
    ·
      refine ⟨4710028435259291841049715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3140018956839527894033143 4710028435259291841049715)
      ·
        refine ⟨7065042652888937761574573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710028435259291841049715 7065042652888937761574573)
        ·
          refine ⟨2649390994833351660590465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7065042652888937761574573 2649390994833351660590465)
          ·
            refine ⟨1987043246125013745442849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649390994833351660590465 1987043246125013745442849)
            ·
              refine ⟨1490282434593760309082137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987043246125013745442849 1490282434593760309082137)
              ·
                refine ⟨1117711825945320231811603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490282434593760309082137 1117711825945320231811603)
                ·
                  refine ⟨1676567738917980347717405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117711825945320231811603 1676567738917980347717405)
                  ·
                    refine ⟨628712902094242630394027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676567738917980347717405 628712902094242630394027)
                    ·
                      rfl

theorem cell22_1836621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1836621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836621 prefixEnd_1836621 := by exact prefixLift 1836621
  have htrace : WordTrace (prefixWord ++ tailWord_1836621) baseStart_1836621 baseEnd_1836621 := by
    simpa [prefixWord, tailWord_1836621, baseEnd_1836621] using wordTrace_append hprefix tailTrace_1836621
  have hstable : (prefixWord ++ tailWord_1836621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836621).length < 2 ^ (prefixWord ++ tailWord_1836621).sum := by decide
  have hdescent : baseEnd_1836621 < baseStart_1836621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836641 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1836641 : Nat := 118140960795 + 1836641 * 2 ^ 59
def prefixEnd_1836641 : Nat := 4983230072969 + 3 ^ 40 * 1836641 * 2
def baseEnd_1836641 : Nat := 628719748502969244893965

theorem tailTrace_1836641 : CollatzResearch.WordTrace tailWord_1836641 prefixEnd_1836641 628719748502969244893965 := by
  unfold tailWord_1836641
  simp only [CollatzResearch.WordTrace]
  refine ⟨66987800539170805155101777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44658533692780536770067851 66987800539170805155101777)
  ·
    refine ⟨50240850404378103866326333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66987800539170805155101777 50240850404378103866326333)
    ·
      refine ⟨18840318901641788949872375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50240850404378103866326333 18840318901641788949872375)
      ·
        refine ⟨28260478352462683424808563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18840318901641788949872375 28260478352462683424808563)
        ·
          refine ⟨42390717528694025137212845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28260478352462683424808563 42390717528694025137212845)
          ·
            refine ⟨15896519073260259426454817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42390717528694025137212845 15896519073260259426454817)
            ·
              refine ⟨11922389304945194569841113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15896519073260259426454817 11922389304945194569841113)
              ·
                refine ⟨8941791978708895927380835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11922389304945194569841113 8941791978708895927380835)
                ·
                  refine ⟨13412687968063343891071253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941791978708895927380835 13412687968063343891071253)
                  ·
                    refine ⟨628719748502969244893965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13412687968063343891071253 628719748502969244893965)
                    ·
                      rfl

theorem cell22_1836641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1836641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836641 prefixEnd_1836641 := by exact prefixLift 1836641
  have htrace : WordTrace (prefixWord ++ tailWord_1836641) baseStart_1836641 baseEnd_1836641 := by
    simpa [prefixWord, tailWord_1836641, baseEnd_1836641] using wordTrace_append hprefix tailTrace_1836641
  have hstable : (prefixWord ++ tailWord_1836641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836641).length < 2 ^ (prefixWord ++ tailWord_1836641).sum := by decide
  have hdescent : baseEnd_1836641 < baseStart_1836641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836643 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 1, 5]
def baseStart_1836643 : Nat := 118140960795 + 1836643 * 2 ^ 59
def prefixEnd_1836643 : Nat := 4983230072969 + 3 ^ 40 * 1836643 * 2
def baseEnd_1836643 : Nat := 628720433143841906343959

theorem tailTrace_1836643 : CollatzResearch.WordTrace tailWord_1836643 prefixEnd_1836643 628720433143841906343959 := by
  unfold tailWord_1836643
  simp only [CollatzResearch.WordTrace]
  refine ⟨66987873485163559496674583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44658582323442372997783055 66987873485163559496674583)
  ·
    refine ⟨100481810227745339245011875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66987873485163559496674583 100481810227745339245011875)
    ·
      refine ⟨150722715341618008867517813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100481810227745339245011875 150722715341618008867517813)
      ·
        refine ⟨14130254563276688331329795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150722715341618008867517813 14130254563276688331329795)
        ·
          refine ⟨21195381844915032496994693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130254563276688331329795 21195381844915032496994693)
          ·
            refine ⟨3974134095921568593186505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21195381844915032496994693 3974134095921568593186505)
            ·
              refine ⟨2980600571941176444889879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974134095921568593186505 2980600571941176444889879)
              ·
                refine ⟨4470900857911764667334819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980600571941176444889879 4470900857911764667334819)
                ·
                  refine ⟨6706351286867647001002229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470900857911764667334819 6706351286867647001002229)
                  ·
                    refine ⟨628720433143841906343959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6706351286867647001002229 628720433143841906343959)
                    ·
                      rfl

theorem cell22_1836643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 5].length) (baseStart_1836643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836643 prefixEnd_1836643 := by exact prefixLift 1836643
  have htrace : WordTrace (prefixWord ++ tailWord_1836643) baseStart_1836643 baseEnd_1836643 := by
    simpa [prefixWord, tailWord_1836643, baseEnd_1836643] using wordTrace_append hprefix tailTrace_1836643
  have hstable : (prefixWord ++ tailWord_1836643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836643).length < 2 ^ (prefixWord ++ tailWord_1836643).sum := by decide
  have hdescent : baseEnd_1836643 < baseStart_1836643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836658 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1836658 : Nat := 118140960795 + 1836658 * 2 ^ 59
def prefixEnd_1836658 : Nat := 4983230072969 + 3 ^ 40 * 1836658 * 2
def baseEnd_1836658 : Nat := 628725567950386867218913

theorem tailTrace_1836658 : CollatzResearch.WordTrace tailWord_1836658 prefixEnd_1836658 628725567950386867218913 := by
  unfold tailWord_1836658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747105145027304264617657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44658947053406144705647085 16747105145027304264617657)
  ·
    refine ⟨12560328858770478198463243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16747105145027304264617657 12560328858770478198463243)
    ·
      refine ⟨18840493288155717297694865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560328858770478198463243 18840493288155717297694865)
      ·
        refine ⟨14130369966116787973271149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18840493288155717297694865 14130369966116787973271149)
        ·
          refine ⟨5298888737293795489976681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14130369966116787973271149 5298888737293795489976681)
          ·
            refine ⟨3974166552970346617482511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298888737293795489976681 3974166552970346617482511)
            ·
              refine ⟨5961249829455519926223767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974166552970346617482511 5961249829455519926223767)
              ·
                refine ⟨8941874744183279889335651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961249829455519926223767 8941874744183279889335651)
                ·
                  refine ⟨13412812116274919834003477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941874744183279889335651 13412812116274919834003477)
                  ·
                    refine ⟨628725567950386867218913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13412812116274919834003477 628725567950386867218913)
                    ·
                      rfl

theorem cell22_1836658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1836658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836658 prefixEnd_1836658 := by exact prefixLift 1836658
  have htrace : WordTrace (prefixWord ++ tailWord_1836658) baseStart_1836658 baseEnd_1836658 := by
    simpa [prefixWord, tailWord_1836658, baseEnd_1836658] using wordTrace_append hprefix tailTrace_1836658
  have hstable : (prefixWord ++ tailWord_1836658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836658).length < 2 ^ (prefixWord ++ tailWord_1836658).sum := by decide
  have hdescent : baseEnd_1836658 < baseStart_1836658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836662 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1836662 : Nat := 118140960795 + 1836662 * 2 ^ 59
def prefixEnd_1836662 : Nat := 4983230072969 + 3 ^ 40 * 1836662 * 2
def baseEnd_1836662 : Nat := 209575645744044063372967

theorem tailTrace_1836662 : CollatzResearch.WordTrace tailWord_1836662 prefixEnd_1836662 209575645744044063372967 := by
  unfold tailWord_1836662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186785404505920358851015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44659044314729817161077493 4186785404505920358851015)
  ·
    refine ⟨6280178106758880538276523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4186785404505920358851015 6280178106758880538276523)
    ·
      refine ⟨9420267160138320807414785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280178106758880538276523 9420267160138320807414785)
      ·
        refine ⟨7065200370103740605561089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9420267160138320807414785 7065200370103740605561089)
        ·
          refine ⟨5298900277577805454170817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065200370103740605561089 5298900277577805454170817)
          ·
            refine ⟨3974175208183354090628113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298900277577805454170817 3974175208183354090628113)
            ·
              refine ⟨2980631406137515567971085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974175208183354090628113 2980631406137515567971085)
              ·
                refine ⟨1117736777301568337989157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980631406137515567971085 1117736777301568337989157)
                ·
                  refine ⟨209575645744044063372967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1117736777301568337989157 209575645744044063372967)
                  ·
                    rfl

theorem cell22_1836662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1836662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836662 prefixEnd_1836662 := by exact prefixLift 1836662
  have htrace : WordTrace (prefixWord ++ tailWord_1836662) baseStart_1836662 baseEnd_1836662 := by
    simpa [prefixWord, tailWord_1836662, baseEnd_1836662] using wordTrace_append hprefix tailTrace_1836662
  have hstable : (prefixWord ++ tailWord_1836662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836662).length < 2 ^ (prefixWord ++ tailWord_1836662).sum := by decide
  have hdescent : baseEnd_1836662 < baseStart_1836662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836705 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1836705 : Nat := 118140960795 + 1836705 * 2 ^ 59
def prefixEnd_1836705 : Nat := 4983230072969 + 3 ^ 40 * 1836705 * 2
def baseEnd_1836705 : Nat := 628741657010894411293769

theorem tailTrace_1836705 : CollatzResearch.WordTrace tailWord_1836705 prefixEnd_1836705 628741657010894411293769 := by
  unfold tailWord_1836705
  simp only [CollatzResearch.WordTrace]
  refine ⟨66990134810938944085431569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44660089873959296056954379 66990134810938944085431569)
  ·
    refine ⟨50242601108204208064073677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66990134810938944085431569 50242601108204208064073677)
    ·
      refine ⟨18840975415576578024027629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50242601108204208064073677 18840975415576578024027629)
      ·
        refine ⟨7065365780841216759010361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18840975415576578024027629 7065365780841216759010361)
        ·
          refine ⟨5299024335630912569257771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065365780841216759010361 5299024335630912569257771)
          ·
            refine ⟨7948536503446368853886657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299024335630912569257771 7948536503446368853886657)
            ·
              refine ⟨5961402377584776640414993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948536503446368853886657 5961402377584776640414993)
              ·
                refine ⟨4471051783188582480311245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961402377584776640414993 4471051783188582480311245)
                ·
                  refine ⟨1676644418695718430116717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4471051783188582480311245 1676644418695718430116717)
                  ·
                    refine ⟨628741657010894411293769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676644418695718430116717 628741657010894411293769)
                    ·
                      rfl

theorem cell22_1836705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1836705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836705 prefixEnd_1836705 := by exact prefixLift 1836705
  have htrace : WordTrace (prefixWord ++ tailWord_1836705) baseStart_1836705 baseEnd_1836705 := by
    simpa [prefixWord, tailWord_1836705, baseEnd_1836705] using wordTrace_append hprefix tailTrace_1836705
  have hstable : (prefixWord ++ tailWord_1836705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836705).length < 2 ^ (prefixWord ++ tailWord_1836705).sum := by decide
  have hdescent : baseEnd_1836705 < baseStart_1836705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836722 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1836722 : Nat := 118140960795 + 1836722 * 2 ^ 59
def prefixEnd_1836722 : Nat := 4983230072969 + 3 ^ 40 * 1836722 * 2
def baseEnd_1836722 : Nat := 628747476458312033618717

theorem tailTrace_1836722 : CollatzResearch.WordTrace tailWord_1836722 prefixEnd_1836722 628747476458312033618717 := by
  unfold tailWord_1836722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747688712969338997200105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44660503234584903992533613 16747688712969338997200105)
  ·
    refine ⟨12560766534727004247900079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16747688712969338997200105 12560766534727004247900079)
    ·
      refine ⟨18841149802090506371850119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560766534727004247900079 18841149802090506371850119)
      ·
        refine ⟨28261724703135759557775179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18841149802090506371850119 28261724703135759557775179)
        ·
          refine ⟨42392587054703639336662769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28261724703135759557775179 42392587054703639336662769)
          ·
            refine ⟨31794440291027729502497077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42392587054703639336662769 31794440291027729502497077)
            ·
              refine ⟨2980728777283849640859101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31794440291027729502497077 2980728777283849640859101)
              ·
                refine ⟨1117773291481443615322163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980728777283849640859101 1117773291481443615322163)
                ·
                  refine ⟨1676659937222165422983245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117773291481443615322163 1676659937222165422983245)
                  ·
                    refine ⟨628747476458312033618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676659937222165422983245 628747476458312033618717)
                    ·
                      rfl

theorem cell22_1836722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1836722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836722 prefixEnd_1836722 := by exact prefixLift 1836722
  have htrace : WordTrace (prefixWord ++ tailWord_1836722) baseStart_1836722 baseEnd_1836722 := by
    simpa [prefixWord, tailWord_1836722, baseEnd_1836722] using wordTrace_append hprefix tailTrace_1836722
  have hstable : (prefixWord ++ tailWord_1836722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836722).length < 2 ^ (prefixWord ++ tailWord_1836722).sum := by decide
  have hdescent : baseEnd_1836722 < baseStart_1836722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836778 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1836778 : Nat := 118140960795 + 1836778 * 2 ^ 59
def prefixEnd_1836778 : Nat := 4983230072969 + 3 ^ 40 * 1836778 * 2
def baseEnd_1836778 : Nat := 628766646402746554218545

theorem tailTrace_1836778 : CollatzResearch.WordTrace tailWord_1836778 prefixEnd_1836778 628766646402746554218545 := by
  unfold tailWord_1836778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16748199334918619388209747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44661864893116318368559325 16748199334918619388209747)
  ·
    refine ⟨25122299002377929082314621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16748199334918619388209747 25122299002377929082314621)
    ·
      refine ⟨9420862125891723405867983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25122299002377929082314621 9420862125891723405867983)
      ·
        refine ⟨14131293188837585108801975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420862125891723405867983 14131293188837585108801975)
        ·
          refine ⟨21196939783256377663202963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14131293188837585108801975 21196939783256377663202963)
          ·
            refine ⟨31795409674884566494804445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21196939783256377663202963 31795409674884566494804445)
            ·
              refine ⟨11923278628081712435551667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31795409674884566494804445 11923278628081712435551667)
              ·
                refine ⟨17884917942122568653327501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923278628081712435551667 17884917942122568653327501)
                ·
                  refine ⟨6706844228295963244997813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17884917942122568653327501 6706844228295963244997813)
                  ·
                    refine ⟨628766646402746554218545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6706844228295963244997813 628766646402746554218545)
                    ·
                      rfl

theorem cell22_1836778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1836778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836778 prefixEnd_1836778 := by exact prefixLift 1836778
  have htrace : WordTrace (prefixWord ++ tailWord_1836778) baseStart_1836778 baseEnd_1836778 := by
    simpa [prefixWord, tailWord_1836778, baseEnd_1836778] using wordTrace_append hprefix tailTrace_1836778
  have hstable : (prefixWord ++ tailWord_1836778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836778).length < 2 ^ (prefixWord ++ tailWord_1836778).sum := by decide
  have hdescent : baseEnd_1836778 < baseStart_1836778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836782 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_1836782 : Nat := 118140960795 + 1836782 * 2 ^ 59
def prefixEnd_1836782 : Nat := 4983230072969 + 3 ^ 40 * 1836782 * 2
def baseEnd_1836782 : Nat := 628768015684491877118533

theorem tailTrace_1836782 : CollatzResearch.WordTrace tailWord_1836782 prefixEnd_1836782 628768015684491877118533 := by
  unfold tailWord_1836782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374117903957498279498075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44661962154439990823989733 8374117903957498279498075)
  ·
    refine ⟨12561176855936247419247113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374117903957498279498075 12561176855936247419247113)
    ·
      refine ⟨9420882641952185564435335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12561176855936247419247113 9420882641952185564435335)
      ·
        refine ⟨14131323962928278346653003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420882641952185564435335 14131323962928278346653003)
        ·
          refine ⟨21196985944392417519979505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14131323962928278346653003 21196985944392417519979505)
          ·
            refine ⟨15897739458294313139984629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21196985944392417519979505 15897739458294313139984629)
            ·
              refine ⟨1490413074215091856873559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15897739458294313139984629 1490413074215091856873559)
              ·
                refine ⟨2235619611322637785310339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490413074215091856873559 2235619611322637785310339)
                ·
                  refine ⟨3353429416983956677965509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235619611322637785310339 3353429416983956677965509)
                  ·
                    refine ⟨628768015684491877118533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353429416983956677965509 628768015684491877118533)
                    ·
                      rfl

theorem cell22_1836782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_1836782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836782 prefixEnd_1836782 := by exact prefixLift 1836782
  have htrace : WordTrace (prefixWord ++ tailWord_1836782) baseStart_1836782 baseEnd_1836782 := by
    simpa [prefixWord, tailWord_1836782, baseEnd_1836782] using wordTrace_append hprefix tailTrace_1836782
  have hstable : (prefixWord ++ tailWord_1836782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836782).length < 2 ^ (prefixWord ++ tailWord_1836782).sum := by decide
  have hdescent : baseEnd_1836782 < baseStart_1836782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836846 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1836846 : Nat := 118140960795 + 1836846 * 2 ^ 59
def prefixEnd_1836846 : Nat := 4983230072969 + 3 ^ 40 * 1836846 * 2
def baseEnd_1836846 : Nat := 628789924192417043518337

theorem tailTrace_1836846 : CollatzResearch.WordTrace tailWord_1836846 prefixEnd_1836846 628789924192417043518337 := by
  unfold tailWord_1836846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374409687928515645789299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44663518335618750110876261 8374409687928515645789299)
  ·
    refine ⟨12561614531892773468683949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374409687928515645789299 12561614531892773468683949)
    ·
      refine ⟨4710605449459790050756481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12561614531892773468683949 4710605449459790050756481)
      ·
        refine ⟨3532954087094842538067361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4710605449459790050756481 3532954087094842538067361)
        ·
          refine ⟨2649715565321131903550521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532954087094842538067361 2649715565321131903550521)
          ·
            refine ⟨1987286673990848927662891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649715565321131903550521 1987286673990848927662891)
            ·
              refine ⟨2980930010986273391494337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987286673990848927662891 2980930010986273391494337)
              ·
                refine ⟨2235697508239705043620753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980930010986273391494337 2235697508239705043620753)
                ·
                  refine ⟨1676773131179778782715565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235697508239705043620753 1676773131179778782715565)
                  ·
                    refine ⟨628789924192417043518337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676773131179778782715565 628789924192417043518337)
                    ·
                      rfl

theorem cell22_1836846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1836846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836846 prefixEnd_1836846 := by exact prefixLift 1836846
  have htrace : WordTrace (prefixWord ++ tailWord_1836846) baseStart_1836846 baseEnd_1836846 := by
    simpa [prefixWord, tailWord_1836846, baseEnd_1836846] using wordTrace_append hprefix tailTrace_1836846
  have hstable : (prefixWord ++ tailWord_1836846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836846).length < 2 ^ (prefixWord ++ tailWord_1836846).sum := by decide
  have hdescent : baseEnd_1836846 < baseStart_1836846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836945 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1836945 : Nat := 118140960795 + 1836945 * 2 ^ 59
def prefixEnd_1836945 : Nat := 4983230072969 + 3 ^ 40 * 1836945 * 2
def baseEnd_1836945 : Nat := 628823813915613785293033

theorem tailTrace_1836945 : CollatzResearch.WordTrace tailWord_1836945 prefixEnd_1836945 628823813915613785293033 := by
  unfold tailWord_1836945
  simp only [CollatzResearch.WordTrace]
  refine ⟨66998888330069465074168289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44665925553379643382778859 66998888330069465074168289)
  ·
    refine ⟨50249166247552098805626217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66998888330069465074168289 50249166247552098805626217)
    ·
      refine ⟨37686874685664074104219663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50249166247552098805626217 37686874685664074104219663)
      ·
        refine ⟨56530312028496111156329495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37686874685664074104219663 56530312028496111156329495)
        ·
          refine ⟨84795468042744166734494243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56530312028496111156329495 84795468042744166734494243)
          ·
            refine ⟨127193202064116250101741365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84795468042744166734494243 127193202064116250101741365)
            ·
              refine ⟨11924362693510898447038253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127193202064116250101741365 11924362693510898447038253)
              ·
                refine ⟨4471636010066586917639345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11924362693510898447038253 4471636010066586917639345)
                ·
                  refine ⟨3353727007549940188229509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471636010066586917639345 3353727007549940188229509)
                  ·
                    refine ⟨628823813915613785293033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353727007549940188229509 628823813915613785293033)
                    ·
                      rfl

theorem cell22_1836945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1836945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836945 prefixEnd_1836945 := by exact prefixLift 1836945
  have htrace : WordTrace (prefixWord ++ tailWord_1836945) baseStart_1836945 baseEnd_1836945 := by
    simpa [prefixWord, tailWord_1836945, baseEnd_1836945] using wordTrace_append hprefix tailTrace_1836945
  have hstable : (prefixWord ++ tailWord_1836945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836945).length < 2 ^ (prefixWord ++ tailWord_1836945).sum := by decide
  have hdescent : baseEnd_1836945 < baseStart_1836945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836964 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_1836964 : Nat := 118140960795 + 1836964 * 2 ^ 59
def prefixEnd_1836964 : Nat := 4983230072969 + 3 ^ 40 * 1836964 * 2
def baseEnd_1836964 : Nat := 628830318003904069067975

theorem tailTrace_1836964 : CollatzResearch.WordTrace tailWord_1836964 prefixEnd_1836964 628830318003904069067975 := by
  unfold tailWord_1836964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33499790658500315659554973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44666387544667087546073297 33499790658500315659554973)
  ·
    refine ⟨12562421496937618372333115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33499790658500315659554973 12562421496937618372333115)
    ·
      refine ⟨18843632245406427558499673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12562421496937618372333115 18843632245406427558499673)
      ·
        refine ⟨14132724184054820668874755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18843632245406427558499673 14132724184054820668874755)
        ·
          refine ⟨21199086276082231003312133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14132724184054820668874755 21199086276082231003312133)
          ·
            refine ⟨3974828676765418313121025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21199086276082231003312133 3974828676765418313121025)
            ·
              refine ⟨2981121507574063734840769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974828676765418313121025 2981121507574063734840769)
              ·
                refine ⟨2235841130680547801130577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981121507574063734840769 2235841130680547801130577)
                ·
                  refine ⟨1676880848010410850847933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235841130680547801130577 1676880848010410850847933)
                  ·
                    refine ⟨628830318003904069067975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676880848010410850847933 628830318003904069067975)
                    ·
                      rfl

theorem cell22_1836964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_1836964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836964 prefixEnd_1836964 := by exact prefixLift 1836964
  have htrace : WordTrace (prefixWord ++ tailWord_1836964) baseStart_1836964 baseEnd_1836964 := by
    simpa [prefixWord, tailWord_1836964, baseEnd_1836964] using wordTrace_append hprefix tailTrace_1836964
  have hstable : (prefixWord ++ tailWord_1836964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836964).length < 2 ^ (prefixWord ++ tailWord_1836964).sum := by decide
  have hdescent : baseEnd_1836964 < baseStart_1836964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836977 : List Nat := [1, 2, 2, 4, 2, 3, 1, 7]
def baseStart_1836977 : Nat := 118140960795 + 1836977 * 2 ^ 59
def prefixEnd_1836977 : Nat := 4983230072969 + 3 ^ 40 * 1836977 * 2
def baseEnd_1836977 : Nat := 69870529796619596499215

theorem tailTrace_1836977 : CollatzResearch.WordTrace tailWord_1836977 prefixEnd_1836977 69870529796619596499215 := by
  unfold tailWord_1836977
  simp only [CollatzResearch.WordTrace]
  refine ⟨67000055465953534539333185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44666703643969023026222123 67000055465953534539333185)
  ·
    refine ⟨50250041599465150904499889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67000055465953534539333185 50250041599465150904499889)
    ·
      refine ⟨37687531199598863178374917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50250041599465150904499889 37687531199598863178374917)
      ·
        refine ⟨7066412099924786845945297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37687531199598863178374917 7066412099924786845945297)
        ·
          refine ⟨5299809074943590134458973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066412099924786845945297 5299809074943590134458973)
          ·
            refine ⟨1987428403103846300422115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5299809074943590134458973 1987428403103846300422115)
            ·
              refine ⟨2981142604655769450633173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987428403103846300422115 2981142604655769450633173)
              ·
                refine ⟨69870529796619596499215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2981142604655769450633173 69870529796619596499215)
                ·
                  rfl

theorem cell22_1836977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 7].length) (baseStart_1836977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836977 prefixEnd_1836977 := by exact prefixLift 1836977
  have htrace : WordTrace (prefixWord ++ tailWord_1836977) baseStart_1836977 baseEnd_1836977 := by
    simpa [prefixWord, tailWord_1836977, baseEnd_1836977] using wordTrace_append hprefix tailTrace_1836977
  have hstable : (prefixWord ++ tailWord_1836977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836977).length < 2 ^ (prefixWord ++ tailWord_1836977).sum := by decide
  have hdescent : baseEnd_1836977 < baseStart_1836977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836992 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_1836992 : Nat := 118140960795 + 1836992 * 2 ^ 59
def prefixEnd_1836992 : Nat := 4983230072969 + 3 ^ 40 * 1836992 * 2
def baseEnd_1836992 : Nat := 628839902976121329367889

theorem tailTrace_1836992 : CollatzResearch.WordTrace tailWord_1836992 prefixEnd_1836992 628839902976121329367889 := by
  unfold tailWord_1836992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500301280449596050564615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44667068373932794734086153 33500301280449596050564615)
  ·
    refine ⟨50250451920674394075846923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500301280449596050564615 50250451920674394075846923)
    ·
      refine ⟨75375677881011591113770385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50250451920674394075846923 75375677881011591113770385)
      ·
        refine ⟨56531758410758693335327789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75375677881011591113770385 56531758410758693335327789)
        ·
          refine ⟨21199409404034510000747921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56531758410758693335327789 21199409404034510000747921)
          ·
            refine ⟨15899557053025882500560941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21199409404034510000747921 15899557053025882500560941)
            ·
              refine ⟨5962333894884705937710353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15899557053025882500560941 5962333894884705937710353)
              ·
                refine ⟨4471750421163529453282765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962333894884705937710353 4471750421163529453282765)
                ·
                  refine ⟨1676906407936323544981037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4471750421163529453282765 1676906407936323544981037)
                  ·
                    refine ⟨628839902976121329367889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676906407936323544981037 628839902976121329367889)
                    ·
                      rfl

theorem cell22_1836992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_1836992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1836992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1836992 prefixEnd_1836992 := by exact prefixLift 1836992
  have htrace : WordTrace (prefixWord ++ tailWord_1836992) baseStart_1836992 baseEnd_1836992 := by
    simpa [prefixWord, tailWord_1836992, baseEnd_1836992] using wordTrace_append hprefix tailTrace_1836992
  have hstable : (prefixWord ++ tailWord_1836992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836992).length < 2 ^ (prefixWord ++ tailWord_1836992).sum := by decide
  have hdescent : baseEnd_1836992 < baseStart_1836992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837035 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_1837035 : Nat := 118140960795 + 1837035 * 2 ^ 59
def prefixEnd_1837035 : Nat := 4983230072969 + 3 ^ 40 * 1837035 * 2
def baseEnd_1837035 : Nat := 628854622754883550542757

theorem tailTrace_1837035 : CollatzResearch.WordTrace tailWord_1837035 prefixEnd_1837035 628854622754883550542757 := by
  unfold tailWord_1837035
  simp only [CollatzResearch.WordTrace]
  refine ⟨67002170899743410444944559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44668113933162273629963039 67002170899743410444944559)
  ·
    refine ⟨100503256349615115667416839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67002170899743410444944559 100503256349615115667416839)
    ·
      refine ⟨150754884524422673501125259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100503256349615115667416839 150754884524422673501125259)
      ·
        refine ⟨226132326786634010251687889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150754884524422673501125259 226132326786634010251687889)
        ·
          refine ⟨169599245089975507688765917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226132326786634010251687889 169599245089975507688765917)
          ·
            refine ⟨63599716908740815383287219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169599245089975507688765917 63599716908740815383287219)
            ·
              refine ⟨95399575363111223074930829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63599716908740815383287219 95399575363111223074930829)
              ·
                refine ⟨35774840761166708653099061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95399575363111223074930829 35774840761166708653099061)
                ·
                  refine ⟨3353891321359378936228037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35774840761166708653099061 3353891321359378936228037)
                  ·
                    refine ⟨628854622754883550542757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353891321359378936228037 628854622754883550542757)
                    ·
                      rfl

theorem cell22_1837035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_1837035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837035 prefixEnd_1837035 := by exact prefixLift 1837035
  have htrace : WordTrace (prefixWord ++ tailWord_1837035) baseStart_1837035 baseEnd_1837035 := by
    simpa [prefixWord, tailWord_1837035, baseEnd_1837035] using wordTrace_append hprefix tailTrace_1837035
  have hstable : (prefixWord ++ tailWord_1837035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837035).length < 2 ^ (prefixWord ++ tailWord_1837035).sum := by decide
  have hdescent : baseEnd_1837035 < baseStart_1837035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837060 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1837060 : Nat := 118140960795 + 1837060 * 2 ^ 59
def prefixEnd_1837060 : Nat := 4983230072969 + 3 ^ 40 * 1837060 * 2
def baseEnd_1837060 : Nat := 628863180765791818667681

theorem tailTrace_1837060 : CollatzResearch.WordTrace tailWord_1837060 prefixEnd_1837060 628863180765791818667681 := by
  unfold tailWord_1837060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501541362326419857302317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44668721816435226476403089 33501541362326419857302317)
  ·
    refine ⟨12563078010872407446488369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33501541362326419857302317 12563078010872407446488369)
    ·
      refine ⟨9422308508154305584866277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12563078010872407446488369 9422308508154305584866277)
      ·
        refine ⟨1766682845278932297162427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9422308508154305584866277 1766682845278932297162427)
        ·
          refine ⟨2650024267918398445743641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766682845278932297162427 2650024267918398445743641)
          ·
            refine ⟨1987518200938798834307731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2650024267918398445743641 1987518200938798834307731)
            ·
              refine ⟨2981277301408198251461597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987518200938798834307731 2981277301408198251461597)
              ·
                refine ⟨1117978988028074344298099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2981277301408198251461597 1117978988028074344298099)
                ·
                  refine ⟨1676968482042111516447149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117978988028074344298099 1676968482042111516447149)
                  ·
                    refine ⟨628863180765791818667681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676968482042111516447149 628863180765791818667681)
                    ·
                      rfl

theorem cell22_1837060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1837060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837060 prefixEnd_1837060 := by exact prefixLift 1837060
  have htrace : WordTrace (prefixWord ++ tailWord_1837060) baseStart_1837060 baseEnd_1837060 := by
    simpa [prefixWord, tailWord_1837060, baseEnd_1837060] using wordTrace_append hprefix tailTrace_1837060
  have hstable : (prefixWord ++ tailWord_1837060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837060).length < 2 ^ (prefixWord ++ tailWord_1837060).sum := by decide
  have hdescent : baseEnd_1837060 < baseStart_1837060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837084 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_1837084 : Nat := 118140960795 + 1837084 * 2 ^ 59
def prefixEnd_1837084 : Nat := 4983230072969 + 3 ^ 40 * 1837084 * 2
def baseEnd_1837084 : Nat := 209623798818754585355869

theorem tailTrace_1837084 : CollatzResearch.WordTrace tailWord_1837084 prefixEnd_1837084 209623798818754585355869 := by
  unfold tailWord_1837084
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501979038282945906739153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44669305384377261208985537 33501979038282945906739153)
  ·
    refine ⟨25126484278712209430054365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33501979038282945906739153 25126484278712209430054365)
    ·
      refine ⟨9422431604517078536270387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25126484278712209430054365 9422431604517078536270387)
      ·
        refine ⟨14133647406775617804405581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9422431604517078536270387 14133647406775617804405581)
        ·
          refine ⟨5300117777540856676652093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14133647406775617804405581 5300117777540856676652093)
          ·
            refine ⟨1987544166577821253744535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5300117777540856676652093 1987544166577821253744535)
            ·
              refine ⟨2981316249866731880616803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987544166577821253744535 2981316249866731880616803)
              ·
                refine ⟨4471974374800097820925205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981316249866731880616803 4471974374800097820925205)
                ·
                  refine ⟨209623798818754585355869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4471974374800097820925205 209623798818754585355869)
                  ·
                    rfl

theorem cell22_1837084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_1837084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837084 prefixEnd_1837084 := by exact prefixLift 1837084
  have htrace : WordTrace (prefixWord ++ tailWord_1837084) baseStart_1837084 baseEnd_1837084 := by
    simpa [prefixWord, tailWord_1837084, baseEnd_1837084] using wordTrace_append hprefix tailTrace_1837084
  have hstable : (prefixWord ++ tailWord_1837084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837084).length < 2 ^ (prefixWord ++ tailWord_1837084).sum := by decide
  have hdescent : baseEnd_1837084 < baseStart_1837084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837234 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_1837234 : Nat := 118140960795 + 1837234 * 2 ^ 59
def prefixEnd_1837234 : Nat := 4983230072969 + 3 ^ 40 * 1837234 * 2
def baseEnd_1837234 : Nat := 628922744521713364817147

theorem tailTrace_1837234 : CollatzResearch.WordTrace tailWord_1837234 prefixEnd_1837234 628922744521713364817147 := by
  unfold tailWord_1837234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752357256505616857859689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44672952684014978287625837 16752357256505616857859689)
  ·
    refine ⟨12564267942379212643394767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16752357256505616857859689 12564267942379212643394767)
    ·
      refine ⟨18846401913568818965092151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12564267942379212643394767 18846401913568818965092151)
      ·
        refine ⟨28269602870353228447638227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18846401913568818965092151 28269602870353228447638227)
        ·
          refine ⟨42404404305529842671457341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269602870353228447638227 42404404305529842671457341)
          ·
            refine ⟨15901651614573691001796503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42404404305529842671457341 15901651614573691001796503)
            ·
              refine ⟨23852477421860536502694755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901651614573691001796503 23852477421860536502694755)
              ·
                refine ⟨35778716132790804754042133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23852477421860536502694755 35778716132790804754042133)
                ·
                  refine ⟨1677127318724568972845725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35778716132790804754042133 1677127318724568972845725)
                  ·
                    refine ⟨628922744521713364817147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677127318724568972845725 628922744521713364817147)
                    ·
                      rfl

theorem cell22_1837234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_1837234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837234 prefixEnd_1837234 := by exact prefixLift 1837234
  have htrace : WordTrace (prefixWord ++ tailWord_1837234) baseStart_1837234 baseEnd_1837234 := by
    simpa [prefixWord, tailWord_1837234, baseEnd_1837234] using wordTrace_append hprefix tailTrace_1837234
  have hstable : (prefixWord ++ tailWord_1837234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837234).length < 2 ^ (prefixWord ++ tailWord_1837234).sum := by decide
  have hdescent : baseEnd_1837234 < baseStart_1837234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837279 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 5, 3]
def baseStart_1837279 : Nat := 118140960795 + 1837279 * 2 ^ 59
def prefixEnd_1837279 : Nat := 4983230072969 + 3 ^ 40 * 1837279 * 2
def baseEnd_1837279 : Nat := 628938148941348247442009

theorem tailTrace_1837279 : CollatzResearch.WordTrace tailWord_1837279 prefixEnd_1837279 628938148941348247442009 := by
  unfold tailWord_1837279
  simp only [CollatzResearch.WordTrace]
  refine ⟨67011070310859440116826891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44674046873906293411217927 67011070310859440116826891)
  ·
    refine ⟨100516605466289160175240337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67011070310859440116826891 100516605466289160175240337)
    ·
      refine ⟨75387454099716870131430253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100516605466289160175240337 75387454099716870131430253)
      ·
        refine ⟨28270295287393826299286345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75387454099716870131430253 28270295287393826299286345)
        ·
          refine ⟨21202721465545369724464759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28270295287393826299286345 21202721465545369724464759)
          ·
            refine ⟨31804082198318054586697139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21202721465545369724464759 31804082198318054586697139)
            ·
              refine ⟨47706123297477081880045709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31804082198318054586697139 47706123297477081880045709)
              ·
                refine ⟨17889796236553905705017141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47706123297477081880045709 17889796236553905705017141)
                ·
                  refine ⟨1677168397176928659845357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17889796236553905705017141 1677168397176928659845357)
                  ·
                    refine ⟨628938148941348247442009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677168397176928659845357 628938148941348247442009)
                    ·
                      rfl

theorem cell22_1837279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_1837279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837279 prefixEnd_1837279 := by exact prefixLift 1837279
  have htrace : WordTrace (prefixWord ++ tailWord_1837279) baseStart_1837279 baseEnd_1837279 := by
    simpa [prefixWord, tailWord_1837279, baseEnd_1837279] using wordTrace_append hprefix tailTrace_1837279
  have hstable : (prefixWord ++ tailWord_1837279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837279).length < 2 ^ (prefixWord ++ tailWord_1837279).sum := by decide
  have hdescent : baseEnd_1837279 < baseStart_1837279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837283 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 2, 4]
def baseStart_1837283 : Nat := 118140960795 + 1837283 * 2 ^ 59
def prefixEnd_1837283 : Nat := 4983230072969 + 3 ^ 40 * 1837283 * 2
def baseEnd_1837283 : Nat := 628939518223093570341997

theorem tailTrace_1837283 : CollatzResearch.WordTrace tailWord_1837283 prefixEnd_1837283 628939518223093570341997 := by
  unfold tailWord_1837283
  simp only [CollatzResearch.WordTrace]
  refine ⟨67011216202844948799972503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44674144135229965866648335 67011216202844948799972503)
  ·
    refine ⟨100516824304267423199958755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67011216202844948799972503 100516824304267423199958755)
    ·
      refine ⟨150775236456401134799938133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100516824304267423199958755 150775236456401134799938133)
      ·
        refine ⟨1766897302223450798436775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 150775236456401134799938133 1766897302223450798436775)
        ·
          refine ⟨2650345953335176197655163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766897302223450798436775 2650345953335176197655163)
          ·
            refine ⟨3975518930002764296482745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650345953335176197655163 3975518930002764296482745)
            ·
              refine ⟨2981639197502073222362059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975518930002764296482745 2981639197502073222362059)
              ·
                refine ⟨4472458796253109833543089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981639197502073222362059 4472458796253109833543089)
                ·
                  refine ⟨3354344097189832375157317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472458796253109833543089 3354344097189832375157317)
                  ·
                    refine ⟨628939518223093570341997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354344097189832375157317 628939518223093570341997)
                    ·
                      rfl

theorem cell22_1837283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 4].length) (baseStart_1837283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837283 prefixEnd_1837283 := by exact prefixLift 1837283
  have htrace : WordTrace (prefixWord ++ tailWord_1837283) baseStart_1837283 baseEnd_1837283 := by
    simpa [prefixWord, tailWord_1837283, baseEnd_1837283] using wordTrace_append hprefix tailTrace_1837283
  have hstable : (prefixWord ++ tailWord_1837283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837283).length < 2 ^ (prefixWord ++ tailWord_1837283).sum := by decide
  have hdescent : baseEnd_1837283 < baseStart_1837283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837307 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_1837307 : Nat := 118140960795 + 1837307 * 2 ^ 59
def prefixEnd_1837307 : Nat := 4983230072969 + 3 ^ 40 * 1837307 * 2
def baseEnd_1837307 : Nat := 628947733913565507741923

theorem tailTrace_1837307 : CollatzResearch.WordTrace tailWord_1837307 prefixEnd_1837307 628947733913565507741923 := by
  unfold tailWord_1837307
  simp only [CollatzResearch.WordTrace]
  refine ⟨67012091554758000898846175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44674727703172000599230783 67012091554758000898846175)
  ·
    refine ⟨100518137332137001348269263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67012091554758000898846175 100518137332137001348269263)
    ·
      refine ⟨150777205998205502022403895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100518137332137001348269263 150777205998205502022403895)
      ·
        refine ⟨226165808997308253033605843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150777205998205502022403895 226165808997308253033605843)
        ·
          refine ⟨339248713495962379550408765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226165808997308253033605843 339248713495962379550408765)
          ·
            refine ⟨127218267560985892331403287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339248713495962379550408765 127218267560985892331403287)
            ·
              refine ⟨190827401341478838497104931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127218267560985892331403287 190827401341478838497104931)
              ·
                refine ⟨286241102012218257745657397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190827401341478838497104931 286241102012218257745657397)
                ·
                  refine ⟨26835103313645461663655381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286241102012218257745657397 26835103313645461663655381)
                  ·
                    refine ⟨628947733913565507741923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26835103313645461663655381 628947733913565507741923)
                    ·
                      rfl

theorem cell22_1837307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_1837307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837307 prefixEnd_1837307 := by exact prefixLift 1837307
  have htrace : WordTrace (prefixWord ++ tailWord_1837307) baseStart_1837307 baseEnd_1837307 := by
    simpa [prefixWord, tailWord_1837307, baseEnd_1837307] using wordTrace_append hprefix tailTrace_1837307
  have hstable : (prefixWord ++ tailWord_1837307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837307).length < 2 ^ (prefixWord ++ tailWord_1837307).sum := by decide
  have hdescent : baseEnd_1837307 < baseStart_1837307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837313 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1837313 : Nat := 118140960795 + 1837313 * 2 ^ 59
def prefixEnd_1837313 : Nat := 4983230072969 + 3 ^ 40 * 1837313 * 2
def baseEnd_1837313 : Nat := 628949787836183492091905

theorem tailTrace_1837313 : CollatzResearch.WordTrace tailWord_1837313 prefixEnd_1837313 628949787836183492091905 := by
  unfold tailWord_1837313
  simp only [CollatzResearch.WordTrace]
  refine ⟨67012310392736263923564593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44674873595157509282376395 67012310392736263923564593)
  ·
    refine ⟨50259232794552197942673445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67012310392736263923564593 50259232794552197942673445)
    ·
      refine ⟨9423606148978537114251271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50259232794552197942673445 9423606148978537114251271)
      ·
        refine ⟨14135409223467805671376907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9423606148978537114251271 14135409223467805671376907)
        ·
          refine ⟨21203113835201708507065361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135409223467805671376907 21203113835201708507065361)
          ·
            refine ⟨15902335376401281380299021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21203113835201708507065361 15902335376401281380299021)
            ·
              refine ⟨5963375766150480517612133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15902335376401281380299021 5963375766150480517612133)
              ·
                refine ⟨1118132956153215097052275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5963375766150480517612133 1118132956153215097052275)
                ·
                  refine ⟨1677199434229822645578413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118132956153215097052275 1677199434229822645578413)
                  ·
                    refine ⟨628949787836183492091905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677199434229822645578413 628949787836183492091905)
                    ·
                      rfl

theorem cell22_1837313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1837313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837313 prefixEnd_1837313 := by exact prefixLift 1837313
  have htrace : WordTrace (prefixWord ++ tailWord_1837313) baseStart_1837313 baseEnd_1837313 := by
    simpa [prefixWord, tailWord_1837313, baseEnd_1837313] using wordTrace_append hprefix tailTrace_1837313
  have hstable : (prefixWord ++ tailWord_1837313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837313).length < 2 ^ (prefixWord ++ tailWord_1837313).sum := by decide
  have hdescent : baseEnd_1837313 < baseStart_1837313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837324 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1837324 : Nat := 118140960795 + 1837324 * 2 ^ 59
def prefixEnd_1837324 : Nat := 4983230072969 + 3 ^ 40 * 1837324 * 2
def baseEnd_1837324 : Nat := 628953553360983130066871

theorem tailTrace_1837324 : CollatzResearch.WordTrace tailWord_1837324 prefixEnd_1837324 628953553360983130066871 := by
  unfold tailWord_1837324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33506355797848206401107513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44675141063797608534810017 33506355797848206401107513)
  ·
    refine ⟨25129766848386154800830635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33506355797848206401107513 25129766848386154800830635)
    ·
      refine ⟨37694650272579232201245953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25129766848386154800830635 37694650272579232201245953)
      ·
        refine ⟨28270987704434424150934465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37694650272579232201245953 28270987704434424150934465)
        ·
          refine ⟨21203240778325818113200849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28270987704434424150934465 21203240778325818113200849)
          ·
            refine ⟨15902430583744363584900637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21203240778325818113200849 15902430583744363584900637)
            ·
              refine ⟨5963411468904136344337739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15902430583744363584900637 5963411468904136344337739)
              ·
                refine ⟨8945117203356204516506609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963411468904136344337739 8945117203356204516506609)
                ·
                  refine ⟨6708837902517153387379957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8945117203356204516506609 6708837902517153387379957)
                  ·
                    refine ⟨628953553360983130066871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6708837902517153387379957 628953553360983130066871)
                    ·
                      rfl

theorem cell22_1837324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1837324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837324 prefixEnd_1837324 := by exact prefixLift 1837324
  have htrace : WordTrace (prefixWord ++ tailWord_1837324) baseStart_1837324 baseEnd_1837324 := by
    simpa [prefixWord, tailWord_1837324, baseEnd_1837324] using wordTrace_append hprefix tailTrace_1837324
  have hstable : (prefixWord ++ tailWord_1837324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837324).length < 2 ^ (prefixWord ++ tailWord_1837324).sum := by decide
  have hdescent : baseEnd_1837324 < baseStart_1837324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837339 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_1837339 : Nat := 118140960795 + 1837339 * 2 ^ 59
def prefixEnd_1837339 : Nat := 4983230072969 + 3 ^ 40 * 1837339 * 2
def baseEnd_1837339 : Nat := 628958688167528090941825

theorem tailTrace_1837339 : CollatzResearch.WordTrace tailWord_1837339 prefixEnd_1837339 628958688167528090941825 := by
  unfold tailWord_1837339
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013258690642070364011071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44675505793761380242674047 67013258690642070364011071)
  ·
    refine ⟨100519888035963105546016607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67013258690642070364011071 100519888035963105546016607)
    ·
      refine ⟨150779832053944658319024911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100519888035963105546016607 150779832053944658319024911)
      ·
        refine ⟨226169748080916987478537367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150779832053944658319024911 226169748080916987478537367)
        ·
          refine ⟨339254622121375481217806051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226169748080916987478537367 339254622121375481217806051)
          ·
            refine ⟨508881933182063221826709077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339254622121375481217806051 508881933182063221826709077)
            ·
              refine ⟨5963460154477303380781747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 508881933182063221826709077 5963460154477303380781747)
              ·
                refine ⟨8945190231715955071172621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963460154477303380781747 8945190231715955071172621)
                ·
                  refine ⟨3354446336893483151689733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8945190231715955071172621 3354446336893483151689733)
                  ·
                    refine ⟨628958688167528090941825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354446336893483151689733 628958688167528090941825)
                    ·
                      rfl

theorem cell22_1837339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_1837339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837339 prefixEnd_1837339 := by exact prefixLift 1837339
  have htrace : WordTrace (prefixWord ++ tailWord_1837339) baseStart_1837339 baseEnd_1837339 := by
    simpa [prefixWord, tailWord_1837339, baseEnd_1837339] using wordTrace_append hprefix tailTrace_1837339
  have hstable : (prefixWord ++ tailWord_1837339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837339).length < 2 ^ (prefixWord ++ tailWord_1837339).sum := by decide
  have hdescent : baseEnd_1837339 < baseStart_1837339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837384 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_1837384 : Nat := 118140960795 + 1837384 * 2 ^ 59
def prefixEnd_1837384 : Nat := 4983230072969 + 3 ^ 40 * 1837384 * 2
def baseEnd_1837384 : Nat := 628974092587162973566687

theorem tailTrace_1837384 : CollatzResearch.WordTrace tailWord_1837384 prefixEnd_1837384 628974092587162973566687 := by
  unfold tailWord_1837384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507449987739521524699603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44676599983652695366266137 33507449987739521524699603)
  ·
    refine ⟨50261174981609282287049405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33507449987739521524699603 50261174981609282287049405)
    ·
      refine ⟨18847940618103480857643527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50261174981609282287049405 18847940618103480857643527)
      ·
        refine ⟨28271910927155221286465291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18847940618103480857643527 28271910927155221286465291)
        ·
          refine ⟨42407866390732831929697937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28271910927155221286465291 42407866390732831929697937)
          ·
            refine ⟨31805899793049623947273453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42407866390732831929697937 31805899793049623947273453)
            ·
              refine ⟨11927212422393608980227545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31805899793049623947273453 11927212422393608980227545)
              ·
                refine ⟨8945409316795206735170659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11927212422393608980227545 8945409316795206735170659)
                ·
                  refine ⟨13418113975192810102755989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945409316795206735170659 13418113975192810102755989)
                  ·
                    refine ⟨628974092587162973566687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13418113975192810102755989 628974092587162973566687)
                    ·
                      rfl

theorem cell22_1837384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_1837384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837384 prefixEnd_1837384 := by exact prefixLift 1837384
  have htrace : WordTrace (prefixWord ++ tailWord_1837384) baseStart_1837384 baseEnd_1837384 := by
    simpa [prefixWord, tailWord_1837384, baseEnd_1837384] using wordTrace_append hprefix tailTrace_1837384
  have hstable : (prefixWord ++ tailWord_1837384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837384).length < 2 ^ (prefixWord ++ tailWord_1837384).sum := by decide
  have hdescent : baseEnd_1837384 < baseStart_1837384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837399 : List Nat := [1, 1, 3, 2, 3, 1, 3, 8]
def baseStart_1837399 : Nat := 118140960795 + 1837399 * 2 ^ 59
def prefixEnd_1837399 : Nat := 4983230072969 + 3 ^ 40 * 1837399 * 2
def baseEnd_1837399 : Nat := 69886580821523103826849

theorem tailTrace_1837399 : CollatzResearch.WordTrace tailWord_1837399 prefixEnd_1837399 69886580821523103826849 := by
  unfold tailWord_1837399
  simp only [CollatzResearch.WordTrace]
  refine ⟨67015447070424700611195251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44676964713616467074130167 67015447070424700611195251)
  ·
    refine ⟨100523170605637050916792877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67015447070424700611195251 100523170605637050916792877)
    ·
      refine ⟨37696188977113894093797329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100523170605637050916792877 37696188977113894093797329)
      ·
        refine ⟨28272141732835420570347997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37696188977113894093797329 28272141732835420570347997)
        ·
          refine ⟨10602053149813282713880499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28272141732835420570347997 10602053149813282713880499)
          ·
            refine ⟨15903079724719924070820749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602053149813282713880499 15903079724719924070820749)
            ·
              refine ⟨5963654896769971526557781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15903079724719924070820749 5963654896769971526557781)
              ·
                refine ⟨69886580821523103826849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5963654896769971526557781 69886580821523103826849)
                ·
                  rfl

theorem cell22_1837399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 8].length) (baseStart_1837399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837399 prefixEnd_1837399 := by exact prefixLift 1837399
  have htrace : WordTrace (prefixWord ++ tailWord_1837399) baseStart_1837399 baseEnd_1837399 := by
    simpa [prefixWord, tailWord_1837399, baseEnd_1837399] using wordTrace_append hprefix tailTrace_1837399
  have hstable : (prefixWord ++ tailWord_1837399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837399).length < 2 ^ (prefixWord ++ tailWord_1837399).sum := by decide
  have hdescent : baseEnd_1837399 < baseStart_1837399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837416 : List Nat := [2, 1, 4, 2, 2, 3, 8]
def baseStart_1837416 : Nat := 118140960795 + 1837416 * 2 ^ 59
def prefixEnd_1837416 : Nat := 4983230072969 + 3 ^ 40 * 1837416 * 2
def baseEnd_1837416 : Nat := 23295742475597242843207

theorem tailTrace_1837416 : CollatzResearch.WordTrace tailWord_1837416 prefixEnd_1837416 23295742475597242843207 := by
  unfold tailWord_1837416
  simp only [CollatzResearch.WordTrace]
  refine ⟨33508033555681556257282051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44677378074242075009709401 33508033555681556257282051)
  ·
    refine ⟨50262050333522334385923077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33508033555681556257282051 50262050333522334385923077)
    ·
      refine ⟨9424134437535437697360577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50262050333522334385923077 9424134437535437697360577)
      ·
        refine ⟨7068100828151578273020433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424134437535437697360577 7068100828151578273020433)
        ·
          refine ⟨5301075621113683704765325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7068100828151578273020433 5301075621113683704765325)
          ·
            refine ⟨1987903357917631389286997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5301075621113683704765325 1987903357917631389286997)
            ·
              refine ⟨23295742475597242843207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1987903357917631389286997 23295742475597242843207)
              ·
                rfl

theorem cell22_1837416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 8].length) (baseStart_1837416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837416 prefixEnd_1837416 := by exact prefixLift 1837416
  have htrace : WordTrace (prefixWord ++ tailWord_1837416) baseStart_1837416 baseEnd_1837416 := by
    simpa [prefixWord, tailWord_1837416, baseEnd_1837416] using wordTrace_append hprefix tailTrace_1837416
  have hstable : (prefixWord ++ tailWord_1837416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837416).length < 2 ^ (prefixWord ++ tailWord_1837416).sum := by decide
  have hdescent : baseEnd_1837416 < baseStart_1837416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837418 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1837418 : Nat := 118140960795 + 1837418 * 2 ^ 59
def prefixEnd_1837418 : Nat := 4983230072969 + 3 ^ 40 * 1837418 * 2
def baseEnd_1837418 : Nat := 628985731481998218216583

theorem tailTrace_1837418 : CollatzResearch.WordTrace tailWord_1837418 prefixEnd_1837418 628985731481998218216583 := by
  unfold tailWord_1837418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754035014338966714034227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44677426704903911237424605 16754035014338966714034227)
  ·
    refine ⟨25131052521508450071051341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754035014338966714034227 25131052521508450071051341)
    ·
      refine ⟨9424144695565668776644253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25131052521508450071051341 9424144695565668776644253)
      ·
        refine ⟨3534054260837125791241595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9424144695565668776644253 3534054260837125791241595)
        ·
          refine ⟨5301081391255688686862393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3534054260837125791241595 5301081391255688686862393)
          ·
            refine ⟨3975811043441766515146795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5301081391255688686862393 3975811043441766515146795)
            ·
              refine ⟨5963716565162649772720193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975811043441766515146795 5963716565162649772720193)
              ·
                refine ⟨4472787423871987329540145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963716565162649772720193 4472787423871987329540145)
                ·
                  refine ⟨3354590567903990497155109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472787423871987329540145 3354590567903990497155109)
                  ·
                    refine ⟨628985731481998218216583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354590567903990497155109 628985731481998218216583)
                    ·
                      rfl

theorem cell22_1837418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1837418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837418 prefixEnd_1837418 := by exact prefixLift 1837418
  have htrace : WordTrace (prefixWord ++ tailWord_1837418) baseStart_1837418 baseEnd_1837418 := by
    simpa [prefixWord, tailWord_1837418, baseEnd_1837418] using wordTrace_append hprefix tailTrace_1837418
  have hstable : (prefixWord ++ tailWord_1837418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837418).length < 2 ^ (prefixWord ++ tailWord_1837418).sum := by decide
  have hdescent : baseEnd_1837418 < baseStart_1837418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837431 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1837431 : Nat := 118140960795 + 1837431 * 2 ^ 59
def prefixEnd_1837431 : Nat := 4983230072969 + 3 ^ 40 * 1837431 * 2
def baseEnd_1837431 : Nat := 628990181647670517641543

theorem tailTrace_1837431 : CollatzResearch.WordTrace tailWord_1837431 prefixEnd_1837431 628990181647670517641543 := by
  unfold tailWord_1837431
  simp only [CollatzResearch.WordTrace]
  refine ⟨67016614206308770076360147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44677742804205846717573431 67016614206308770076360147)
  ·
    refine ⟨100524921309463155114540221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67016614206308770076360147 100524921309463155114540221)
    ·
      refine ⟨37696845491048683167952583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100524921309463155114540221 37696845491048683167952583)
      ·
        refine ⟨56545268236573024751928875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37696845491048683167952583 56545268236573024751928875)
        ·
          refine ⟨84817902354859537127893313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56545268236573024751928875 84817902354859537127893313)
          ·
            refine ⟨63613426766144652845919985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84817902354859537127893313 63613426766144652845919985)
            ·
              refine ⟨47710070074608489634439989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63613426766144652845919985 47710070074608489634439989)
              ·
                refine ⟨4472819069494545903228749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47710070074608489634439989 4472819069494545903228749)
                ·
                  refine ⟨1677307151060454713710781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4472819069494545903228749 1677307151060454713710781)
                  ·
                    refine ⟨628990181647670517641543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677307151060454713710781 628990181647670517641543)
                    ·
                      rfl

theorem cell22_1837431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1837431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837431 prefixEnd_1837431 := by exact prefixLift 1837431
  have htrace : WordTrace (prefixWord ++ tailWord_1837431) baseStart_1837431 baseEnd_1837431 := by
    simpa [prefixWord, tailWord_1837431, baseEnd_1837431] using wordTrace_append hprefix tailTrace_1837431
  have hstable : (prefixWord ++ tailWord_1837431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837431).length < 2 ^ (prefixWord ++ tailWord_1837431).sum := by decide
  have hdescent : baseEnd_1837431 < baseStart_1837431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837493 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1837493 : Nat := 118140960795 + 1837493 * 2 ^ 59
def prefixEnd_1837493 : Nat := 4983230072969 + 3 ^ 40 * 1837493 * 2
def baseEnd_1837493 : Nat := 629011405514723022591353

theorem tailTrace_1837493 : CollatzResearch.WordTrace tailWord_1837493 prefixEnd_1837493 629011405514723022591353 := by
  unfold tailWord_1837493
  simp only [CollatzResearch.WordTrace]
  refine ⟨67018875532084154665117133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44679250354722769776744755 67018875532084154665117133)
  ·
    refine ⟨25132078324531557999418925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67018875532084154665117133 25132078324531557999418925)
    ·
      refine ⟨9424529371699334249782097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25132078324531557999418925 9424529371699334249782097)
      ·
        refine ⟨7068397028774500687336573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424529371699334249782097 7068397028774500687336573)
        ·
          refine ⟨2650648885790437757751215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7068397028774500687336573 2650648885790437757751215)
          ·
            refine ⟨3975973328685656636626823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650648885790437757751215 3975973328685656636626823)
            ·
              refine ⟨5963959993028484954940235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975973328685656636626823 5963959993028484954940235)
              ·
                refine ⟨8945939989542727432410353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963959993028484954940235 8945939989542727432410353)
                ·
                  refine ⟨6709454992157045574307765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8945939989542727432410353 6709454992157045574307765)
                  ·
                    refine ⟨629011405514723022591353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6709454992157045574307765 629011405514723022591353)
                    ·
                      rfl

theorem cell22_1837493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1837493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837493 prefixEnd_1837493 := by exact prefixLift 1837493
  have htrace : WordTrace (prefixWord ++ tailWord_1837493) baseStart_1837493 baseEnd_1837493 := by
    simpa [prefixWord, tailWord_1837493, baseEnd_1837493] using wordTrace_append hprefix tailTrace_1837493
  have hstable : (prefixWord ++ tailWord_1837493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837493).length < 2 ^ (prefixWord ++ tailWord_1837493).sum := by decide
  have hdescent : baseEnd_1837493 < baseStart_1837493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837525 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1837525 : Nat := 118140960795 + 1837525 * 2 ^ 59
def prefixEnd_1837525 : Nat := 4983230072969 + 3 ^ 40 * 1837525 * 2
def baseEnd_1837525 : Nat := 629022359768685605791255

theorem tailTrace_1837525 : CollatzResearch.WordTrace tailWord_1837525 prefixEnd_1837525 629022359768685605791255 := by
  unfold tailWord_1837525
  simp only [CollatzResearch.WordTrace]
  refine ⟨67020042667968224130282029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44680028445312149420188019 67020042667968224130282029)
  ·
    refine ⟨25132516000488084048855761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67020042667968224130282029 25132516000488084048855761)
    ·
      refine ⟨18849387000366063036641821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25132516000488084048855761 18849387000366063036641821)
      ·
        refine ⟨7068520125137273638740683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18849387000366063036641821 7068520125137273638740683)
        ·
          refine ⟨10602780187705910458111025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068520125137273638740683 10602780187705910458111025)
          ·
            refine ⟨7952085140779432843583269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10602780187705910458111025 7952085140779432843583269)
            ·
              refine ⟨1491015963896143658171863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7952085140779432843583269 1491015963896143658171863)
              ·
                refine ⟨2236523945844215487257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491015963896143658171863 2236523945844215487257795)
                ·
                  refine ⟨3354785918766323230886693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236523945844215487257795 3354785918766323230886693)
                  ·
                    refine ⟨629022359768685605791255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354785918766323230886693 629022359768685605791255)
                    ·
                      rfl

theorem cell22_1837525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1837525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837525 prefixEnd_1837525 := by exact prefixLift 1837525
  have htrace : WordTrace (prefixWord ++ tailWord_1837525) baseStart_1837525 baseEnd_1837525 := by
    simpa [prefixWord, tailWord_1837525, baseEnd_1837525] using wordTrace_append hprefix tailTrace_1837525
  have hstable : (prefixWord ++ tailWord_1837525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837525).length < 2 ^ (prefixWord ++ tailWord_1837525).sum := by decide
  have hdescent : baseEnd_1837525 < baseStart_1837525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837536 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_1837536 : Nat := 118140960795 + 1837536 * 2 ^ 59
def prefixEnd_1837536 : Nat := 4983230072969 + 3 ^ 40 * 1837536 * 2
def baseEnd_1837536 : Nat := 629026125293485243766221

theorem tailTrace_1837536 : CollatzResearch.WordTrace tailWord_1837536 prefixEnd_1837536 629026125293485243766221 := by
  unfold tailWord_1837536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33510221935464186504466231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44680295913952248672621641 33510221935464186504466231)
  ·
    refine ⟨50265332903196279756699347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33510221935464186504466231 50265332903196279756699347)
    ·
      refine ⟨75397999354794419635049021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50265332903196279756699347 75397999354794419635049021)
      ·
        refine ⟨28274249758047907363143383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75397999354794419635049021 28274249758047907363143383)
        ·
          refine ⟨42411374637071861044715075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28274249758047907363143383 42411374637071861044715075)
          ·
            refine ⟨63617061955607791567072613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42411374637071861044715075 63617061955607791567072613)
            ·
              refine ⟨11928199116676460918826115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63617061955607791567072613 11928199116676460918826115)
              ·
                refine ⟨17892298675014691378239173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928199116676460918826115 17892298675014691378239173)
                ·
                  refine ⟨3354806001565254633419845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17892298675014691378239173 3354806001565254633419845)
                  ·
                    refine ⟨629026125293485243766221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354806001565254633419845 629026125293485243766221)
                    ·
                      rfl

theorem cell22_1837536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_1837536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837536 prefixEnd_1837536 := by exact prefixLift 1837536
  have htrace : WordTrace (prefixWord ++ tailWord_1837536) baseStart_1837536 baseEnd_1837536 := by
    simpa [prefixWord, tailWord_1837536, baseEnd_1837536] using wordTrace_append hprefix tailTrace_1837536
  have hstable : (prefixWord ++ tailWord_1837536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837536).length < 2 ^ (prefixWord ++ tailWord_1837536).sum := by decide
  have hdescent : baseEnd_1837536 < baseStart_1837536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837555 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 2, 3]
def baseStart_1837555 : Nat := 118140960795 + 1837555 * 2 ^ 59
def prefixEnd_1837555 : Nat := 4983230072969 + 3 ^ 40 * 1837555 * 2
def baseEnd_1837555 : Nat := 629032629381775527541163

theorem tailTrace_1837555 : CollatzResearch.WordTrace tailWord_1837555 prefixEnd_1837555 629032629381775527541163 := by
  unfold tailWord_1837555
  simp only [CollatzResearch.WordTrace]
  refine ⟨67021136857859539253874119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44680757905239692835916079 67021136857859539253874119)
  ·
    refine ⟨100531705286789308880811179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67021136857859539253874119 100531705286789308880811179)
    ·
      refine ⟨150797557930183963321216769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100531705286789308880811179 150797557930183963321216769)
      ·
        refine ⟨113098168447637972490912577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150797557930183963321216769 113098168447637972490912577)
        ·
          refine ⟨84823626335728479368184433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113098168447637972490912577 84823626335728479368184433)
          ·
            refine ⟨63617719751796359526138325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84823626335728479368184433 63617719751796359526138325)
            ·
              refine ⟨1491040306682727176393867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63617719751796359526138325 1491040306682727176393867)
              ·
                refine ⟨2236560460024090764590801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491040306682727176393867 2236560460024090764590801)
                ·
                  refine ⟨1677420345018068073443101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236560460024090764590801 1677420345018068073443101)
                  ·
                    refine ⟨629032629381775527541163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677420345018068073443101 629032629381775527541163)
                    ·
                      rfl

theorem cell22_1837555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 3].length) (baseStart_1837555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837555 prefixEnd_1837555 := by exact prefixLift 1837555
  have htrace : WordTrace (prefixWord ++ tailWord_1837555) baseStart_1837555 baseEnd_1837555 := by
    simpa [prefixWord, tailWord_1837555, baseEnd_1837555] using wordTrace_append hprefix tailTrace_1837555
  have hstable : (prefixWord ++ tailWord_1837555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837555).length < 2 ^ (prefixWord ++ tailWord_1837555).sum := by decide
  have hdescent : baseEnd_1837555 < baseStart_1837555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837611 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_1837611 : Nat := 118140960795 + 1837611 * 2 ^ 59
def prefixEnd_1837611 : Nat := 4983230072969 + 3 ^ 40 * 1837611 * 2
def baseEnd_1837611 : Nat := 629051799326210048140991

theorem tailTrace_1837611 : CollatzResearch.WordTrace tailWord_1837611 prefixEnd_1837611 629051799326210048140991 := by
  unfold tailWord_1837611
  simp only [CollatzResearch.WordTrace]
  refine ⟨67023179345656660817912687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44682119563771107211941791 67023179345656660817912687)
  ·
    refine ⟨100534769018484991226869031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67023179345656660817912687 100534769018484991226869031)
    ·
      refine ⟨150802153527727486840303547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100534769018484991226869031 150802153527727486840303547)
      ·
        refine ⟨226203230291591230260455321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150802153527727486840303547 226203230291591230260455321)
        ·
          refine ⟨169652422718693422695341491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226203230291591230260455321 169652422718693422695341491)
          ·
            refine ⟨254478634078040134043012237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169652422718693422695341491 254478634078040134043012237)
            ·
              refine ⟨95429487779265050266129589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254478634078040134043012237 95429487779265050266129589)
              ·
                refine ⟨8946514479306098462449649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95429487779265050266129589 8946514479306098462449649)
                ·
                  refine ⟨6709885859479573846837237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946514479306098462449649 6709885859479573846837237)
                  ·
                    refine ⟨629051799326210048140991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6709885859479573846837237 629051799326210048140991)
                    ·
                      rfl

theorem cell22_1837611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_1837611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837611 prefixEnd_1837611 := by exact prefixLift 1837611
  have htrace : WordTrace (prefixWord ++ tailWord_1837611) baseStart_1837611 baseEnd_1837611 := by
    simpa [prefixWord, tailWord_1837611, baseEnd_1837611] using wordTrace_append hprefix tailTrace_1837611
  have hstable : (prefixWord ++ tailWord_1837611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837611).length < 2 ^ (prefixWord ++ tailWord_1837611).sum := by decide
  have hdescent : baseEnd_1837611 < baseStart_1837611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837643 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 1, 4]
def baseStart_1837643 : Nat := 118140960795 + 1837643 * 2 ^ 59
def prefixEnd_1837643 : Nat := 4983230072969 + 3 ^ 40 * 1837643 * 2
def baseEnd_1837643 : Nat := 629062753580172631340893

theorem tailTrace_1837643 : CollatzResearch.WordTrace tailWord_1837643 prefixEnd_1837643 629062753580172631340893 := by
  unfold tailWord_1837643
  simp only [CollatzResearch.WordTrace]
  refine ⟨67024346481540730283077583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44682897654360486855385055 67024346481540730283077583)
  ·
    refine ⟨100536519722311095424616375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67024346481540730283077583 100536519722311095424616375)
    ·
      refine ⟨150804779583466643136924563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100536519722311095424616375 150804779583466643136924563)
      ·
        refine ⟨226207169375199964705386845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150804779583466643136924563 226207169375199964705386845)
        ·
          refine ⟨84827688515699986764520067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226207169375199964705386845 84827688515699986764520067)
          ·
            refine ⟨127241532773549980146780101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84827688515699986764520067 127241532773549980146780101)
            ·
              refine ⟨23857787395040621277521269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127241532773549980146780101 23857787395040621277521269)
              ·
                refine ⟨2236667568285058244767619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23857787395040621277521269 2236667568285058244767619)
                ·
                  refine ⟨3355001352427587367151429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236667568285058244767619 3355001352427587367151429)
                  ·
                    refine ⟨629062753580172631340893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355001352427587367151429 629062753580172631340893)
                    ·
                      rfl

theorem cell22_1837643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 4].length) (baseStart_1837643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837643 prefixEnd_1837643 := by exact prefixLift 1837643
  have htrace : WordTrace (prefixWord ++ tailWord_1837643) baseStart_1837643 baseEnd_1837643 := by
    simpa [prefixWord, tailWord_1837643, baseEnd_1837643] using wordTrace_append hprefix tailTrace_1837643
  have hstable : (prefixWord ++ tailWord_1837643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837643).length < 2 ^ (prefixWord ++ tailWord_1837643).sum := by decide
  have hdescent : baseEnd_1837643 < baseStart_1837643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837673 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_1837673 : Nat := 118140960795 + 1837673 * 2 ^ 59
def prefixEnd_1837673 : Nat := 4983230072969 + 3 ^ 40 * 1837673 * 2
def baseEnd_1837673 : Nat := 629073023193262553090801

theorem tailTrace_1837673 : CollatzResearch.WordTrace tailWord_1837673 prefixEnd_1837673 629073023193262553090801 := by
  unfold tailWord_1837673
  simp only [CollatzResearch.WordTrace]
  refine ⟨67025440671432045406669673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44683627114288030271113115 67025440671432045406669673)
  ·
    refine ⟨50269080503574034055002255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67025440671432045406669673 50269080503574034055002255)
    ·
      refine ⟨75403620755361051082503383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50269080503574034055002255 75403620755361051082503383)
      ·
        refine ⟨113105431133041576623755075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75403620755361051082503383 113105431133041576623755075)
        ·
          refine ⟨169658146699562364935632613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113105431133041576623755075 169658146699562364935632613)
          ·
            refine ⟨31810902506167943425431115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169658146699562364935632613 31810902506167943425431115)
            ·
              refine ⟨47716353759251915138146673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31810902506167943425431115 47716353759251915138146673)
              ·
                refine ⟨35787265319438936353610005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47716353759251915138146673 35787265319438936353610005)
                ·
                  refine ⟨1677528061848700141575469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35787265319438936353610005 1677528061848700141575469)
                  ·
                    refine ⟨629073023193262553090801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677528061848700141575469 629073023193262553090801)
                    ·
                      rfl

theorem cell22_1837673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_1837673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837673 prefixEnd_1837673 := by exact prefixLift 1837673
  have htrace : WordTrace (prefixWord ++ tailWord_1837673) baseStart_1837673 baseEnd_1837673 := by
    simpa [prefixWord, tailWord_1837673, baseEnd_1837673] using wordTrace_append hprefix tailTrace_1837673
  have hstable : (prefixWord ++ tailWord_1837673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837673).length < 2 ^ (prefixWord ++ tailWord_1837673).sum := by decide
  have hdescent : baseEnd_1837673 < baseStart_1837673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837698 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1837698 : Nat := 118140960795 + 1837698 * 2 ^ 59
def prefixEnd_1837698 : Nat := 4983230072969 + 3 ^ 40 * 1837698 * 2
def baseEnd_1837698 : Nat := 209693860401390273738575

theorem tailTrace_1837698 : CollatzResearch.WordTrace tailWord_1837698 prefixEnd_1837698 209693860401390273738575 := by
  unfold tailWord_1837698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756588124085368669082437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44684234997560983117553165 16756588124085368669082437)
  ·
    refine ⟨3141860273266006625452957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16756588124085368669082437 3141860273266006625452957)
    ·
      refine ⟨1178197602474752484544859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3141860273266006625452957 1178197602474752484544859)
      ·
        refine ⟨1767296403712128726817289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178197602474752484544859 1767296403712128726817289)
        ·
          refine ⟨1325472302784096545112967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767296403712128726817289 1325472302784096545112967)
          ·
            refine ⟨1988208454176144817669451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325472302784096545112967 1988208454176144817669451)
            ·
              refine ⟨2982312681264217226504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988208454176144817669451 2982312681264217226504177)
              ·
                refine ⟨2236734510948162919878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982312681264217226504177 2236734510948162919878133)
                ·
                  refine ⟨209693860401390273738575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236734510948162919878133 209693860401390273738575)
                  ·
                    rfl

theorem cell22_1837698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1837698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837698 prefixEnd_1837698 := by exact prefixLift 1837698
  have htrace : WordTrace (prefixWord ++ tailWord_1837698) baseStart_1837698 baseEnd_1837698 := by
    simpa [prefixWord, tailWord_1837698, baseEnd_1837698] using wordTrace_append hprefix tailTrace_1837698
  have hstable : (prefixWord ++ tailWord_1837698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837698).length < 2 ^ (prefixWord ++ tailWord_1837698).sum := by decide
  have hdescent : baseEnd_1837698 < baseStart_1837698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837724 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1837724 : Nat := 118140960795 + 1837724 * 2 ^ 59
def prefixEnd_1837724 : Nat := 4983230072969 + 3 ^ 40 * 1837724 * 2
def baseEnd_1837724 : Nat := 629090481535515420065645

theorem tailTrace_1837724 : CollatzResearch.WordTrace tailWord_1837724 prefixEnd_1837724 629090481535515420065645 := by
  unfold tailWord_1837724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513650397123640558388113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44684867196164854077850817 33513650397123640558388113)
  ·
    refine ⟨25135237797842730418791085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33513650397123640558388113 25135237797842730418791085)
    ·
      refine ⟨9425714174191023907046657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25135237797842730418791085 9425714174191023907046657)
      ·
        refine ⟨7069285630643267930284993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425714174191023907046657 7069285630643267930284993)
        ·
          refine ⟨5301964222982450947713745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069285630643267930284993 5301964222982450947713745)
          ·
            refine ⟨3976473167236838210785309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5301964222982450947713745 3976473167236838210785309)
            ·
              refine ⟨1491177437713814329044491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976473167236838210785309 1491177437713814329044491)
              ·
                refine ⟨2236766156570721493566737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491177437713814329044491 2236766156570721493566737)
                ·
                  refine ⟨1677574617428041120175053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236766156570721493566737 1677574617428041120175053)
                  ·
                    refine ⟨629090481535515420065645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677574617428041120175053 629090481535515420065645)
                    ·
                      rfl

theorem cell22_1837724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1837724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837724 prefixEnd_1837724 := by exact prefixLift 1837724
  have htrace : WordTrace (prefixWord ++ tailWord_1837724) baseStart_1837724 baseEnd_1837724 := by
    simpa [prefixWord, tailWord_1837724, baseEnd_1837724] using wordTrace_append hprefix tailTrace_1837724
  have hstable : (prefixWord ++ tailWord_1837724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837724).length < 2 ^ (prefixWord ++ tailWord_1837724).sum := by decide
  have hdescent : baseEnd_1837724 < baseStart_1837724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837823 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_1837823 : Nat := 118140960795 + 1837823 * 2 ^ 59
def prefixEnd_1837823 : Nat := 4983230072969 + 3 ^ 40 * 1837823 * 2
def baseEnd_1837823 : Nat := 629124371258712161840341

theorem tailTrace_1837823 : CollatzResearch.WordTrace tailWord_1837823 prefixEnd_1837823 629124371258712161840341 := by
  unfold tailWord_1837823
  simp only [CollatzResearch.WordTrace]
  refine ⟨67030911620888621024630123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44687274413925747349753415 67030911620888621024630123)
  ·
    refine ⟨100546367431332931536945185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67030911620888621024630123 100546367431332931536945185)
    ·
      refine ⟨75409775573499698652708889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100546367431332931536945185 75409775573499698652708889)
      ·
        refine ⟨56557331680124773989531667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75409775573499698652708889 56557331680124773989531667)
        ·
          refine ⟨84835997520187160984297501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56557331680124773989531667 84835997520187160984297501)
          ·
            refine ⟨31813499070070185369111563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84835997520187160984297501 31813499070070185369111563)
            ·
              refine ⟨47720248605105278053667345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31813499070070185369111563 47720248605105278053667345)
              ·
                refine ⟨35790186453828958540250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47720248605105278053667345 35790186453828958540250509)
                ·
                  refine ⟨13421319920185859452593941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35790186453828958540250509 13421319920185859452593941)
                  ·
                    refine ⟨629124371258712161840341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13421319920185859452593941 629124371258712161840341)
                    ·
                      rfl

theorem cell22_1837823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_1837823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837823 prefixEnd_1837823 := by exact prefixLift 1837823
  have htrace : WordTrace (prefixWord ++ tailWord_1837823) baseStart_1837823 baseEnd_1837823 := by
    simpa [prefixWord, tailWord_1837823, baseEnd_1837823] using wordTrace_append hprefix tailTrace_1837823
  have hstable : (prefixWord ++ tailWord_1837823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837823).length < 2 ^ (prefixWord ++ tailWord_1837823).sum := by decide
  have hdescent : baseEnd_1837823 < baseStart_1837823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837887 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 3, 3]
def baseStart_1837887 : Nat := 118140960795 + 1837887 * 2 ^ 59
def prefixEnd_1837887 : Nat := 4983230072969 + 3 ^ 40 * 1837887 * 2
def baseEnd_1837887 : Nat := 629146279766637328240145

theorem tailTrace_1837887 : CollatzResearch.WordTrace tailWord_1837887 prefixEnd_1837887 629146279766637328240145 := by
  unfold tailWord_1837887
  simp only [CollatzResearch.WordTrace]
  refine ⟨67033245892656759954959915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44688830595104506636639943 67033245892656759954959915)
  ·
    refine ⟨100549868838985139932439873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67033245892656759954959915 100549868838985139932439873)
    ·
      refine ⟨75412401629238854949329905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100549868838985139932439873 75412401629238854949329905)
      ·
        refine ⟨56559301221929141211997429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75412401629238854949329905 56559301221929141211997429)
        ·
          refine ⟨5302434489555856988624759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56559301221929141211997429 5302434489555856988624759)
          ·
            refine ⟨7953651734333785482937139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302434489555856988624759 7953651734333785482937139)
            ·
              refine ⟨11930477601500678224405709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953651734333785482937139 11930477601500678224405709)
              ·
                refine ⟨4473929100562754334152141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11930477601500678224405709 4473929100562754334152141)
                ·
                  refine ⟨1677723412711032875307053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4473929100562754334152141 1677723412711032875307053)
                  ·
                    refine ⟨629146279766637328240145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677723412711032875307053 629146279766637328240145)
                    ·
                      rfl

theorem cell22_1837887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_1837887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1837887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1837887 prefixEnd_1837887 := by exact prefixLift 1837887
  have htrace : WordTrace (prefixWord ++ tailWord_1837887) baseStart_1837887 baseEnd_1837887 := by
    simpa [prefixWord, tailWord_1837887, baseEnd_1837887] using wordTrace_append hprefix tailTrace_1837887
  have hstable : (prefixWord ++ tailWord_1837887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837887).length < 2 ^ (prefixWord ++ tailWord_1837887).sum := by decide
  have hdescent : baseEnd_1837887 < baseStart_1837887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838024 : List Nat := [2, 1, 3, 1, 5, 1, 3, 6]
def baseStart_1838024 : Nat := 118140960795 + 1838024 * 2 ^ 59
def prefixEnd_1838024 : Nat := 4983230072969 + 3 ^ 40 * 1838024 * 2
def baseEnd_1838024 : Nat := 69910353074046070840525

theorem tailTrace_1838024 : CollatzResearch.WordTrace tailWord_1838024 prefixEnd_1838024 69910353074046070840525 := by
  unfold tailWord_1838024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519121346580216176348563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44692161795440288235131417 33519121346580216176348563)
  ·
    refine ⟨50278682019870324264522845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33519121346580216176348563 50278682019870324264522845)
    ·
      refine ⟨18854505757451371599196067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50278682019870324264522845 18854505757451371599196067)
      ·
        refine ⟨28281758636177057398794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18854505757451371599196067 28281758636177057398794101)
        ·
          refine ⟨2651414872141599131136947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28281758636177057398794101 2651414872141599131136947)
          ·
            refine ⟨3977122308212398696705421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651414872141599131136947 3977122308212398696705421)
            ·
              refine ⟨1491420865579649511264533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3977122308212398696705421 1491420865579649511264533)
              ·
                refine ⟨69910353074046070840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1491420865579649511264533 69910353074046070840525)
                ·
                  rfl

theorem cell22_1838024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_1838024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838024 prefixEnd_1838024 := by exact prefixLift 1838024
  have htrace : WordTrace (prefixWord ++ tailWord_1838024) baseStart_1838024 baseEnd_1838024 := by
    simpa [prefixWord, tailWord_1838024, baseEnd_1838024] using wordTrace_append hprefix tailTrace_1838024
  have hstable : (prefixWord ++ tailWord_1838024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838024).length < 2 ^ (prefixWord ++ tailWord_1838024).sum := by decide
  have hdescent : baseEnd_1838024 < baseStart_1838024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838052 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1838052 : Nat := 118140960795 + 1838052 * 2 ^ 59
def prefixEnd_1838052 : Nat := 4983230072969 + 3 ^ 40 * 1838052 * 2
def baseEnd_1838052 : Nat := 209734254212877299288213

theorem tailTrace_1838052 : CollatzResearch.WordTrace tailWord_1838052 prefixEnd_1838052 209734254212877299288213 := by
  unfold tailWord_1838052
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519631968529496567358205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44692842624705995423144273 33519631968529496567358205)
  ·
    refine ⟨12569861988198561212759327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33519631968529496567358205 12569861988198561212759327)
    ·
      refine ⟨18854792982297841819138991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569861988198561212759327 18854792982297841819138991)
      ·
        refine ⟨28282189473446762728708487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18854792982297841819138991 28282189473446762728708487)
        ·
          refine ⟨42423284210170144093062731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282189473446762728708487 42423284210170144093062731)
          ·
            refine ⟨63634926315255216139594097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42423284210170144093062731 63634926315255216139594097)
            ·
              refine ⟨47726194736441412104695573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63634926315255216139594097 47726194736441412104695573)
              ·
                refine ⟨2237165378270691192407605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47726194736441412104695573 2237165378270691192407605)
                ·
                  refine ⟨209734254212877299288213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237165378270691192407605 209734254212877299288213)
                  ·
                    rfl

theorem cell22_1838052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1838052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838052 prefixEnd_1838052 := by exact prefixLift 1838052
  have htrace : WordTrace (prefixWord ++ tailWord_1838052) baseStart_1838052 baseEnd_1838052 := by
    simpa [prefixWord, tailWord_1838052, baseEnd_1838052] using wordTrace_append hprefix tailTrace_1838052
  have hstable : (prefixWord ++ tailWord_1838052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838052).length < 2 ^ (prefixWord ++ tailWord_1838052).sum := by decide
  have hdescent : baseEnd_1838052 < baseStart_1838052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838056 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_1838056 : Nat := 118140960795 + 1838056 * 2 ^ 59
def prefixEnd_1838056 : Nat := 4983230072969 + 3 ^ 40 * 1838056 * 2
def baseEnd_1838056 : Nat := 629204131920377220764627

theorem tailTrace_1838056 : CollatzResearch.WordTrace tailWord_1838056 prefixEnd_1838056 629204131920377220764627 := by
  unfold tailWord_1838056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519704914522250908931011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44692939886029667878574681 33519704914522250908931011)
  ·
    refine ⟨50279557371783376363396517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33519704914522250908931011 50279557371783376363396517)
    ·
      refine ⟨9427417007209383068136847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50279557371783376363396517 9427417007209383068136847)
      ·
        refine ⟨14141125510814074602205271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427417007209383068136847 14141125510814074602205271)
        ·
          refine ⟨21211688266221111903307907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141125510814074602205271 21211688266221111903307907)
          ·
            refine ⟨31817532399331667854961861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21211688266221111903307907 31817532399331667854961861)
            ·
              refine ⟨5965787324874687722805349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31817532399331667854961861 5965787324874687722805349)
              ·
                refine ⟨1118585123414003948026003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5965787324874687722805349 1118585123414003948026003)
                ·
                  refine ⟨1677877685121005922039005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118585123414003948026003 1677877685121005922039005)
                  ·
                    refine ⟨629204131920377220764627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677877685121005922039005 629204131920377220764627)
                    ·
                      rfl

theorem cell22_1838056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_1838056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838056 prefixEnd_1838056 := by exact prefixLift 1838056
  have htrace : WordTrace (prefixWord ++ tailWord_1838056) baseStart_1838056 baseEnd_1838056 := by
    simpa [prefixWord, tailWord_1838056, baseEnd_1838056] using wordTrace_append hprefix tailTrace_1838056
  have hstable : (prefixWord ++ tailWord_1838056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838056).length < 2 ^ (prefixWord ++ tailWord_1838056).sum := by decide
  have hdescent : baseEnd_1838056 < baseStart_1838056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838114 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1838114 : Nat := 118140960795 + 1838114 * 2 ^ 59
def prefixEnd_1838114 : Nat := 4983230072969 + 3 ^ 40 * 1838114 * 2
def baseEnd_1838114 : Nat := 209741328835228134271483

theorem tailTrace_1838114 : CollatzResearch.WordTrace tailWord_1838114 prefixEnd_1838114 209741328835228134271483 := by
  unfold tailWord_1838114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760381315708594430868349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44694350175222918482315597 16760381315708594430868349)
  ·
    refine ⟨6285142993390722911575631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16760381315708594430868349 6285142993390722911575631)
    ·
      refine ⟨9427714490086084367363447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285142993390722911575631 9427714490086084367363447)
      ·
        refine ⟨14141571735129126551045171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427714490086084367363447 14141571735129126551045171)
        ·
          refine ⟨21212357602693689826567757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141571735129126551045171 21212357602693689826567757)
          ·
            refine ⟨7954634101010133684962909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21212357602693689826567757 7954634101010133684962909)
            ·
              refine ⟨2982987787878800131861091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7954634101010133684962909 2982987787878800131861091)
              ·
                refine ⟨4474481681818200197791637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982987787878800131861091 4474481681818200197791637)
                ·
                  refine ⟨209741328835228134271483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4474481681818200197791637 209741328835228134271483)
                  ·
                    rfl

theorem cell22_1838114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1838114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838114 prefixEnd_1838114 := by exact prefixLift 1838114
  have htrace : WordTrace (prefixWord ++ tailWord_1838114) baseStart_1838114 baseEnd_1838114 := by
    simpa [prefixWord, tailWord_1838114, baseEnd_1838114] using wordTrace_append hprefix tailTrace_1838114
  have hstable : (prefixWord ++ tailWord_1838114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838114).length < 2 ^ (prefixWord ++ tailWord_1838114).sum := by decide
  have hdescent : baseEnd_1838114 < baseStart_1838114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838144 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_1838144 : Nat := 118140960795 + 1838144 * 2 ^ 59
def prefixEnd_1838144 : Nat := 4983230072969 + 3 ^ 40 * 1838144 * 2
def baseEnd_1838144 : Nat := 629234256118774324564357

theorem tailTrace_1838144 : CollatzResearch.WordTrace tailWord_1838144 prefixEnd_1838144 629234256118774324564357 := by
  unfold tailWord_1838144
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521309726362846423532743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44695079635150461898043657 33521309726362846423532743)
  ·
    refine ⟨50281964589544269635299115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33521309726362846423532743 50281964589544269635299115)
    ·
      refine ⟨75422946884316404452948673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281964589544269635299115 75422946884316404452948673)
      ·
        refine ⟨56567210163237303339711505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75422946884316404452948673 56567210163237303339711505)
        ·
          refine ⟨42425407622427977504783629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56567210163237303339711505 42425407622427977504783629)
          ·
            refine ⟨15909527858410491564293861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42425407622427977504783629 15909527858410491564293861)
            ·
              refine ⟨2983036473451967168305099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15909527858410491564293861 2983036473451967168305099)
              ·
                refine ⟨4474554710177950752457649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983036473451967168305099 4474554710177950752457649)
                ·
                  refine ⟨3355916032633463064343237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474554710177950752457649 3355916032633463064343237)
                  ·
                    refine ⟨629234256118774324564357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355916032633463064343237 629234256118774324564357)
                    ·
                      rfl

theorem cell22_1838144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_1838144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838144 prefixEnd_1838144 := by exact prefixLift 1838144
  have htrace : WordTrace (prefixWord ++ tailWord_1838144) baseStart_1838144 baseEnd_1838144 := by
    simpa [prefixWord, tailWord_1838144, baseEnd_1838144] using wordTrace_append hprefix tailTrace_1838144
  have hstable : (prefixWord ++ tailWord_1838144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838144).length < 2 ^ (prefixWord ++ tailWord_1838144).sum := by decide
  have hdescent : baseEnd_1838144 < baseStart_1838144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838150 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1838150 : Nat := 118140960795 + 1838150 * 2 ^ 59
def prefixEnd_1838150 : Nat := 4983230072969 + 3 ^ 40 * 1838150 * 2
def baseEnd_1838150 : Nat := 629236310041392308914339

theorem tailTrace_1838150 : CollatzResearch.WordTrace tailWord_1838150 prefixEnd_1838150 629236310041392308914339 := by
  unfold tailWord_1838150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095088696584498620993247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44695225527135970581189269 2095088696584498620993247)
  ·
    refine ⟨3142633044876747931489871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095088696584498620993247 3142633044876747931489871)
    ·
      refine ⟨4713949567315121897234807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142633044876747931489871 4713949567315121897234807)
      ·
        refine ⟨7070924350972682845852211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713949567315121897234807 7070924350972682845852211)
        ·
          refine ⟨10606386526459024268778317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070924350972682845852211 10606386526459024268778317)
          ·
            refine ⟨3977394947422134100791869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10606386526459024268778317 3977394947422134100791869)
            ·
              refine ⟨1491523105283300287796951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3977394947422134100791869 1491523105283300287796951)
              ·
                refine ⟨2237284657924950431695427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491523105283300287796951 2237284657924950431695427)
                ·
                  refine ⟨3355926986887425647543141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237284657924950431695427 3355926986887425647543141)
                  ·
                    refine ⟨629236310041392308914339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355926986887425647543141 629236310041392308914339)
                    ·
                      rfl

theorem cell22_1838150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1838150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838150 prefixEnd_1838150 := by exact prefixLift 1838150
  have htrace : WordTrace (prefixWord ++ tailWord_1838150) baseStart_1838150 baseEnd_1838150 := by
    simpa [prefixWord, tailWord_1838150, baseEnd_1838150] using wordTrace_append hprefix tailTrace_1838150
  have hstable : (prefixWord ++ tailWord_1838150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838150).length < 2 ^ (prefixWord ++ tailWord_1838150).sum := by decide
  have hdescent : baseEnd_1838150 < baseStart_1838150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838384 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 8]
def baseStart_1838384 : Nat := 118140960795 + 1838384 * 2 ^ 59
def prefixEnd_1838384 : Nat := 4983230072969 + 3 ^ 40 * 1838384 * 2
def baseEnd_1838384 : Nat := 209772137674497899521207

theorem tailTrace_1838384 : CollatzResearch.WordTrace tailWord_1838384 prefixEnd_1838384 209772137674497899521207 := by
  unfold tailWord_1838384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33525686485928106917901103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44700915314570809223868137 33525686485928106917901103)
  ·
    refine ⟨50288529728892160376851655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33525686485928106917901103 50288529728892160376851655)
    ·
      refine ⟨75432794593338240565277483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50288529728892160376851655 75432794593338240565277483)
      ·
        refine ⟨113149191890007360847916225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75432794593338240565277483 113149191890007360847916225)
        ·
          refine ⟨84861893917505520635937169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113149191890007360847916225 84861893917505520635937169)
          ·
            refine ⟨63646420438129140476952877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84861893917505520635937169 63646420438129140476952877)
            ·
              refine ⟨23867407664298427678857329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63646420438129140476952877 23867407664298427678857329)
              ·
                refine ⟨17900555748223820759142997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23867407664298427678857329 17900555748223820759142997)
                ·
                  refine ⟨209772137674497899521207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17900555748223820759142997 209772137674497899521207)
                  ·
                    rfl

theorem cell22_1838384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_1838384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838384 prefixEnd_1838384 := by exact prefixLift 1838384
  have htrace : WordTrace (prefixWord ++ tailWord_1838384) baseStart_1838384 baseEnd_1838384 := by
    simpa [prefixWord, tailWord_1838384, baseEnd_1838384] using wordTrace_append hprefix tailTrace_1838384
  have hstable : (prefixWord ++ tailWord_1838384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838384).length < 2 ^ (prefixWord ++ tailWord_1838384).sum := by decide
  have hdescent : baseEnd_1838384 < baseStart_1838384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838390 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1838390 : Nat := 118140960795 + 1838390 * 2 ^ 59
def prefixEnd_1838390 : Nat := 4983230072969 + 3 ^ 40 * 1838390 * 2
def baseEnd_1838390 : Nat := 209772822315370560971201

theorem tailTrace_1838390 : CollatzResearch.WordTrace tailWord_1838390 prefixEnd_1838390 209772822315370560971201 := by
  unfold tailWord_1838390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190724488114654803782539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44701061206556317907013749 4190724488114654803782539)
  ·
    refine ⟨6286086732171982205673809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190724488114654803782539 6286086732171982205673809)
    ·
      refine ⟨4714565049128986654255357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6286086732171982205673809 4714565049128986654255357)
      ·
        refine ⟨1767961893423369995345759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4714565049128986654255357 1767961893423369995345759)
        ·
          refine ⟨2651942840135054993018639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767961893423369995345759 2651942840135054993018639)
          ·
            refine ⟨3977914260202582489527959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651942840135054993018639 3977914260202582489527959)
            ·
              refine ⟨5966871390303873734291939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977914260202582489527959 5966871390303873734291939)
              ·
                refine ⟨8950307085455810601437909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966871390303873734291939 8950307085455810601437909)
                ·
                  refine ⟨209772822315370560971201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8950307085455810601437909 209772822315370560971201)
                  ·
                    rfl

theorem cell22_1838390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1838390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838390 prefixEnd_1838390 := by exact prefixLift 1838390
  have htrace : WordTrace (prefixWord ++ tailWord_1838390) baseStart_1838390 baseEnd_1838390 := by
    simpa [prefixWord, tailWord_1838390, baseEnd_1838390] using wordTrace_append hprefix tailTrace_1838390
  have hstable : (prefixWord ++ tailWord_1838390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838390).length < 2 ^ (prefixWord ++ tailWord_1838390).sum := by decide
  have hdescent : baseEnd_1838390 < baseStart_1838390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838431 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_1838431 : Nat := 118140960795 + 1838431 * 2 ^ 59
def prefixEnd_1838431 : Nat := 4983230072969 + 3 ^ 40 * 1838431 * 2
def baseEnd_1838431 : Nat := 629332502084001242638477

theorem tailTrace_1838431 : CollatzResearch.WordTrace tailWord_1838431 prefixEnd_1838431 629332502084001242638477 := by
  unfold tailWord_1838431
  simp only [CollatzResearch.WordTrace]
  refine ⟨67053087202685940862763147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44702058135123960575175431 67053087202685940862763147)
  ·
    refine ⟨100579630804028911294144721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67053087202685940862763147 100579630804028911294144721)
    ·
      refine ⟨75434723103021683470608541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100579630804028911294144721 75434723103021683470608541)
      ·
        refine ⟨28288021163633131301478203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75434723103021683470608541 28288021163633131301478203)
        ·
          refine ⟨42432031745449696952217305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28288021163633131301478203 42432031745449696952217305)
          ·
            refine ⟨31824023809087272714162979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42432031745449696952217305 31824023809087272714162979)
            ·
              refine ⟨47736035713630909071244469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31824023809087272714162979 47736035713630909071244469)
              ·
                refine ⟨4475253348152897725429169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47736035713630909071244469 4475253348152897725429169)
                ·
                  refine ⟨3356440011114673294071877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475253348152897725429169 3356440011114673294071877)
                  ·
                    refine ⟨629332502084001242638477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356440011114673294071877 629332502084001242638477)
                    ·
                      rfl

theorem cell22_1838431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_1838431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838431 prefixEnd_1838431 := by exact prefixLift 1838431
  have htrace : WordTrace (prefixWord ++ tailWord_1838431) baseStart_1838431 baseEnd_1838431 := by
    simpa [prefixWord, tailWord_1838431, baseEnd_1838431] using wordTrace_append hprefix tailTrace_1838431
  have hstable : (prefixWord ++ tailWord_1838431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838431).length < 2 ^ (prefixWord ++ tailWord_1838431).sum := by decide
  have hdescent : baseEnd_1838431 < baseStart_1838431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838435 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 4]
def baseStart_1838435 : Nat := 118140960795 + 1838435 * 2 ^ 59
def prefixEnd_1838435 : Nat := 4983230072969 + 3 ^ 40 * 1838435 * 2
def baseEnd_1838435 : Nat := 209777957121915521846155

theorem tailTrace_1838435 : CollatzResearch.WordTrace tailWord_1838435 prefixEnd_1838435 209777957121915521846155 := by
  unfold tailWord_1838435
  simp only [CollatzResearch.WordTrace]
  refine ⟨67053233094671449545908759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44702155396447633030605839 67053233094671449545908759)
  ·
    refine ⟨100579849642007174318863139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67053233094671449545908759 100579849642007174318863139)
    ·
      refine ⟨150869774463010761478294709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100579849642007174318863139 150869774463010761478294709)
      ·
        refine ⟨14144041355907258888590129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150869774463010761478294709 14144041355907258888590129)
        ·
          refine ⟨10608031016930444166442597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144041355907258888590129 10608031016930444166442597)
          ·
            refine ⟨1989005815674458281207987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10608031016930444166442597 1989005815674458281207987)
            ·
              refine ⟨2983508723511687421811981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989005815674458281207987 2983508723511687421811981)
              ·
                refine ⟨1118815771316882783179493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2983508723511687421811981 1118815771316882783179493)
                ·
                  refine ⟨209777957121915521846155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118815771316882783179493 209777957121915521846155)
                  ·
                    rfl

theorem cell22_1838435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 4].length) (baseStart_1838435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838435 prefixEnd_1838435 := by exact prefixLift 1838435
  have htrace : WordTrace (prefixWord ++ tailWord_1838435) baseStart_1838435 baseEnd_1838435 := by
    simpa [prefixWord, tailWord_1838435, baseEnd_1838435] using wordTrace_append hprefix tailTrace_1838435
  have hstable : (prefixWord ++ tailWord_1838435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838435).length < 2 ^ (prefixWord ++ tailWord_1838435).sum := by decide
  have hdescent : baseEnd_1838435 < baseStart_1838435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838467 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 2, 3]
def baseStart_1838467 : Nat := 118140960795 + 1838467 * 2 ^ 59
def prefixEnd_1838467 : Nat := 4983230072969 + 3 ^ 40 * 1838467 * 2
def baseEnd_1838467 : Nat := 629344825619709148738367

theorem tailTrace_1838467 : CollatzResearch.WordTrace tailWord_1838467 prefixEnd_1838467 629344825619709148738367 := by
  unfold tailWord_1838467
  simp only [CollatzResearch.WordTrace]
  refine ⟨67054400230555519011073655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44702933487037012674049103 67054400230555519011073655)
  ·
    refine ⟨100581600345833278516610483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67054400230555519011073655 100581600345833278516610483)
    ·
      refine ⟨150872400518749917774915725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100581600345833278516610483 150872400518749917774915725)
      ·
        refine ⟨56577150194531219165593397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150872400518749917774915725 56577150194531219165593397)
        ·
          refine ⟨5304107830737301796774381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56577150194531219165593397 5304107830737301796774381)
          ·
            refine ⟨1989040436526488173790393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5304107830737301796774381 1989040436526488173790393)
            ·
              refine ⟨1491780327394866130342795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989040436526488173790393 1491780327394866130342795)
              ·
                refine ⟨2237670491092299195514193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491780327394866130342795 2237670491092299195514193)
                ·
                  refine ⟨1678252868319224396635645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2237670491092299195514193 1678252868319224396635645)
                  ·
                    refine ⟨629344825619709148738367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1678252868319224396635645 629344825619709148738367)
                    ·
                      rfl

theorem cell22_1838467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 3].length) (baseStart_1838467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838467 prefixEnd_1838467 := by exact prefixLift 1838467
  have htrace : WordTrace (prefixWord ++ tailWord_1838467) baseStart_1838467 baseEnd_1838467 := by
    simpa [prefixWord, tailWord_1838467, baseEnd_1838467] using wordTrace_append hprefix tailTrace_1838467
  have hstable : (prefixWord ++ tailWord_1838467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838467).length < 2 ^ (prefixWord ++ tailWord_1838467).sum := by decide
  have hdescent : baseEnd_1838467 < baseStart_1838467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838482 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1838482 : Nat := 118140960795 + 1838482 * 2 ^ 59
def prefixEnd_1838482 : Nat := 4983230072969 + 3 ^ 40 * 1838482 * 2
def baseEnd_1838482 : Nat := 629349960426254109613321

theorem tailTrace_1838482 : CollatzResearch.WordTrace tailWord_1838482 prefixEnd_1838482 629349960426254109613321 := by
  unfold tailWord_1838482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763736831375294143217425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44703298217000784381913133 16763736831375294143217425)
  ·
    refine ⟨12572802623531470607413069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16763736831375294143217425 12572802623531470607413069)
    ·
      refine ⟨4714800983824301477779901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12572802623531470607413069 4714800983824301477779901)
      ·
        refine ⟨1768050368934113054167463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4714800983824301477779901 1768050368934113054167463)
        ·
          refine ⟨2652075553401169581251195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768050368934113054167463 2652075553401169581251195)
          ·
            refine ⟨3978113330101754371876793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652075553401169581251195 3978113330101754371876793)
            ·
              refine ⟨2983584997576315778907595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978113330101754371876793 2983584997576315778907595)
              ·
                refine ⟨4475377496364473668361393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983584997576315778907595 4475377496364473668361393)
                ·
                  refine ⟨3356533122273355251271045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475377496364473668361393 3356533122273355251271045)
                  ·
                    refine ⟨629349960426254109613321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356533122273355251271045 629349960426254109613321)
                    ·
                      rfl

theorem cell22_1838482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1838482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838482 prefixEnd_1838482 := by exact prefixLift 1838482
  have htrace : WordTrace (prefixWord ++ tailWord_1838482) baseStart_1838482 baseEnd_1838482 := by
    simpa [prefixWord, tailWord_1838482, baseEnd_1838482] using wordTrace_append hprefix tailTrace_1838482
  have hstable : (prefixWord ++ tailWord_1838482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838482).length < 2 ^ (prefixWord ++ tailWord_1838482).sum := by decide
  have hdescent : baseEnd_1838482 < baseStart_1838482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838538 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1838538 : Nat := 118140960795 + 1838538 * 2 ^ 59
def prefixEnd_1838538 : Nat := 4983230072969 + 3 ^ 40 * 1838538 * 2
def baseEnd_1838538 : Nat := 629369130370688630213149

theorem tailTrace_1838538 : CollatzResearch.WordTrace tailWord_1838538 prefixEnd_1838538 629369130370688630213149 := by
  unfold tailWord_1838538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764247453324574534227067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44704659875532198757938845 16764247453324574534227067)
  ·
    refine ⟨25146371179986861801340601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764247453324574534227067 25146371179986861801340601)
    ·
      refine ⟨18859778384990146351005451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25146371179986861801340601 18859778384990146351005451)
      ·
        refine ⟨28289667577485219526508177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859778384990146351005451 28289667577485219526508177)
        ·
          refine ⟨21217250683113914644881133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28289667577485219526508177 21217250683113914644881133)
          ·
            refine ⟨7956469006167717991830425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21217250683113914644881133 7956469006167717991830425)
            ·
              refine ⟨5967351754625788493872819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956469006167717991830425 5967351754625788493872819)
              ·
                refine ⟨8951027631938682740809229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967351754625788493872819 8951027631938682740809229)
                ·
                  refine ⟨3356635361977006027803461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8951027631938682740809229 3356635361977006027803461)
                  ·
                    refine ⟨629369130370688630213149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356635361977006027803461 629369130370688630213149)
                    ·
                      rfl

theorem cell22_1838538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1838538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838538 prefixEnd_1838538 := by exact prefixLift 1838538
  have htrace : WordTrace (prefixWord ++ tailWord_1838538) baseStart_1838538 baseEnd_1838538 := by
    simpa [prefixWord, tailWord_1838538, baseEnd_1838538] using wordTrace_append hprefix tailTrace_1838538
  have hstable : (prefixWord ++ tailWord_1838538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838538).length < 2 ^ (prefixWord ++ tailWord_1838538).sum := by decide
  have hdescent : baseEnd_1838538 < baseStart_1838538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838570 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1838570 : Nat := 118140960795 + 1838570 * 2 ^ 59
def prefixEnd_1838570 : Nat := 4983230072969 + 3 ^ 40 * 1838570 * 2
def baseEnd_1838570 : Nat := 209793361541550404471017

theorem tailTrace_1838570 : CollatzResearch.WordTrace tailWord_1838570 prefixEnd_1838570 209793361541550404471017 := by
  unfold tailWord_1838570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764539237295591900518291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44705437966121578401382109 16764539237295591900518291)
  ·
    refine ⟨25146808855943387850777437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764539237295591900518291 25146808855943387850777437)
    ·
      refine ⟨9430053320978770444041539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25146808855943387850777437 9430053320978770444041539)
      ·
        refine ⟨14145079981468155666062309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9430053320978770444041539 14145079981468155666062309)
        ·
          refine ⟨2652202496525279187386683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14145079981468155666062309 2652202496525279187386683)
          ·
            refine ⟨3978303744787918781080025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652202496525279187386683 3978303744787918781080025)
            ·
              refine ⟨2983727808590939085810019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978303744787918781080025 2983727808590939085810019)
              ·
                refine ⟨4475591712886408628715029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983727808590939085810019 4475591712886408628715029)
                ·
                  refine ⟨209793361541550404471017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4475591712886408628715029 209793361541550404471017)
                  ·
                    rfl

theorem cell22_1838570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1838570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838570 prefixEnd_1838570 := by exact prefixLift 1838570
  have htrace : WordTrace (prefixWord ++ tailWord_1838570) baseStart_1838570 baseEnd_1838570 := by
    simpa [prefixWord, tailWord_1838570, baseEnd_1838570] using wordTrace_append hprefix tailTrace_1838570
  have hstable : (prefixWord ++ tailWord_1838570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838570).length < 2 ^ (prefixWord ++ tailWord_1838570).sum := by decide
  have hdescent : baseEnd_1838570 < baseStart_1838570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838604 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_1838604 : Nat := 118140960795 + 1838604 * 2 ^ 59
def prefixEnd_1838604 : Nat := 4983230072969 + 3 ^ 40 * 1838604 * 2
def baseEnd_1838604 : Nat := 209797241173162152687649

theorem tailTrace_1838604 : CollatzResearch.WordTrace tailWord_1838604 prefixEnd_1838604 209797241173162152687649 := by
  unfold tailWord_1838604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529698515529595704405433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44706264687372794272540577 33529698515529595704405433)
  ·
    refine ⟨25147273886647196778304075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33529698515529595704405433 25147273886647196778304075)
    ·
      refine ⟨37720910829970795167456113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25147273886647196778304075 37720910829970795167456113)
      ·
        refine ⟨28290683122478096375592085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37720910829970795167456113 28290683122478096375592085)
        ·
          refine ⟨1326125771366160767605879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28290683122478096375592085 1326125771366160767605879)
          ·
            refine ⟨1989188657049241151408819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326125771366160767605879 1989188657049241151408819)
            ·
              refine ⟨2983782985573861727113229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989188657049241151408819 2983782985573861727113229)
              ·
                refine ⟨1118918619590198147667461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2983782985573861727113229 1118918619590198147667461)
                ·
                  refine ⟨209797241173162152687649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1118918619590198147667461 209797241173162152687649)
                  ·
                    rfl

theorem cell22_1838604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_1838604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838604 prefixEnd_1838604 := by exact prefixLift 1838604
  have htrace : WordTrace (prefixWord ++ tailWord_1838604) baseStart_1838604 baseEnd_1838604 := by
    simpa [prefixWord, tailWord_1838604, baseEnd_1838604] using wordTrace_append hprefix tailTrace_1838604
  have hstable : (prefixWord ++ tailWord_1838604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838604).length < 2 ^ (prefixWord ++ tailWord_1838604).sum := by decide
  have hdescent : baseEnd_1838604 < baseStart_1838604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838688 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 6]
def baseStart_1838688 : Nat := 118140960795 + 1838688 * 2 ^ 59
def prefixEnd_1838688 : Nat := 4983230072969 + 3 ^ 40 * 1838688 * 2
def baseEnd_1838688 : Nat := 209806826145379412987563

theorem tailTrace_1838688 : CollatzResearch.WordTrace tailWord_1838688 prefixEnd_1838688 209806826145379412987563 := by
  unfold tailWord_1838688
  simp only [CollatzResearch.WordTrace]
  refine ⟨33531230381377436877434359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44708307175169915836579145 33531230381377436877434359)
  ·
    refine ⟨50296845572066155316151539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33531230381377436877434359 50296845572066155316151539)
    ·
      refine ⟨75445268358099232974227309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50296845572066155316151539 75445268358099232974227309)
      ·
        refine ⟨28291975634287212365335241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75445268358099232974227309 28291975634287212365335241)
        ·
          refine ⟨21218981725715409274001431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28291975634287212365335241 21218981725715409274001431)
          ·
            refine ⟨31828472588573113911002147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21218981725715409274001431 31828472588573113911002147)
            ·
              refine ⟨47742708882859670866503221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31828472588573113911002147 47742708882859670866503221)
              ·
                refine ⟨4475878957768094143734677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47742708882859670866503221 4475878957768094143734677)
                ·
                  refine ⟨209806826145379412987563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4475878957768094143734677 209806826145379412987563)
                  ·
                    rfl

theorem cell22_1838688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_1838688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838688 prefixEnd_1838688 := by exact prefixLift 1838688
  have htrace : WordTrace (prefixWord ++ tailWord_1838688) baseStart_1838688 baseEnd_1838688 := by
    simpa [prefixWord, tailWord_1838688, baseEnd_1838688] using wordTrace_append hprefix tailTrace_1838688
  have hstable : (prefixWord ++ tailWord_1838688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838688).length < 2 ^ (prefixWord ++ tailWord_1838688).sum := by decide
  have hdescent : baseEnd_1838688 < baseStart_1838688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838720 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 4, 3]
def baseStart_1838720 : Nat := 118140960795 + 1838720 * 2 ^ 59
def prefixEnd_1838720 : Nat := 4983230072969 + 3 ^ 40 * 1838720 * 2
def baseEnd_1838720 : Nat := 629431432690100822162591

theorem tailTrace_1838720 : CollatzResearch.WordTrace tailWord_1838720 prefixEnd_1838720 629431432690100822162591 := by
  unfold tailWord_1838720
  simp only [CollatzResearch.WordTrace]
  refine ⟨33531813949319471610016807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44709085265759295480022409 33531813949319471610016807)
  ·
    refine ⟨50297720923979207415025211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33531813949319471610016807 50297720923979207415025211)
    ·
      refine ⟨75446581385968811122537817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50297720923979207415025211 75446581385968811122537817)
      ·
        refine ⟨56584936039476608341903363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75446581385968811122537817 56584936039476608341903363)
        ·
          refine ⟨84877404059214912512855045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56584936039476608341903363 84877404059214912512855045)
          ·
            refine ⟨15914513261102796096160321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84877404059214912512855045 15914513261102796096160321)
            ·
              refine ⟨11935884945827097072120241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15914513261102796096160321 11935884945827097072120241)
              ·
                refine ⟨8951913709370322804090181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11935884945827097072120241 8951913709370322804090181)
                ·
                  refine ⟨1678483820506935525766909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8951913709370322804090181 1678483820506935525766909)
                  ·
                    refine ⟨629431432690100822162591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1678483820506935525766909 629431432690100822162591)
                    ·
                      rfl

theorem cell22_1838720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_1838720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838720 prefixEnd_1838720 := by exact prefixLift 1838720
  have htrace : WordTrace (prefixWord ++ tailWord_1838720) baseStart_1838720 baseEnd_1838720 := by
    simpa [prefixWord, tailWord_1838720, baseEnd_1838720] using wordTrace_append hprefix tailTrace_1838720
  have hstable : (prefixWord ++ tailWord_1838720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838720).length < 2 ^ (prefixWord ++ tailWord_1838720).sum := by decide
  have hdescent : baseEnd_1838720 < baseStart_1838720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838765 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1838765 : Nat := 118140960795 + 1838765 * 2 ^ 59
def prefixEnd_1838765 : Nat := 4983230072969 + 3 ^ 40 * 1838765 * 2
def baseEnd_1838765 : Nat := 629446837109735704787453

theorem tailTrace_1838765 : CollatzResearch.WordTrace tailWord_1838765 prefixEnd_1838765 629446837109735704787453 := by
  unfold tailWord_1838765
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065269183475915905421749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44710179455650610603614499 67065269183475915905421749)
  ·
    refine ⟨6287368985950867116133289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67065269183475915905421749 6287368985950867116133289)
    ·
      refine ⟨4715526739463150337099967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6287368985950867116133289 4715526739463150337099967)
      ·
        refine ⟨7073290109194725505649951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715526739463150337099967 7073290109194725505649951)
        ·
          refine ⟨10609935163792088258474927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073290109194725505649951 10609935163792088258474927)
          ·
            refine ⟨15914902745688132387712391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609935163792088258474927 15914902745688132387712391)
            ·
              refine ⟨23872354118532198581568587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914902745688132387712391 23872354118532198581568587)
              ·
                refine ⟨35808531177798297872352881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23872354118532198581568587 35808531177798297872352881)
                ·
                  refine ⟨26856398383348723404264661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35808531177798297872352881 26856398383348723404264661)
                  ·
                    refine ⟨629446837109735704787453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26856398383348723404264661 629446837109735704787453)
                    ·
                      rfl

theorem cell22_1838765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1838765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838765 prefixEnd_1838765 := by exact prefixLift 1838765
  have htrace : WordTrace (prefixWord ++ tailWord_1838765) baseStart_1838765 baseEnd_1838765 := by
    simpa [prefixWord, tailWord_1838765, baseEnd_1838765] using wordTrace_append hprefix tailTrace_1838765
  have hstable : (prefixWord ++ tailWord_1838765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838765).length < 2 ^ (prefixWord ++ tailWord_1838765).sum := by decide
  have hdescent : baseEnd_1838765 < baseStart_1838765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838906 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1838906 : Nat := 118140960795 + 1838906 * 2 ^ 59
def prefixEnd_1838906 : Nat := 4983230072969 + 3 ^ 40 * 1838906 * 2
def baseEnd_1838906 : Nat := 629495104291258337012021

theorem tailTrace_1838906 : CollatzResearch.WordTrace tailWord_1838906 prefixEnd_1838906 629495104291258337012021 := by
  unfold tailWord_1838906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767602968991274246576143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44713607917310064657536381 16767602968991274246576143)
  ·
    refine ⟨25151404453486911369864215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16767602968991274246576143 25151404453486911369864215)
    ·
      refine ⟨37727106680230367054796323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25151404453486911369864215 37727106680230367054796323)
      ·
        refine ⟨56590660020345550582194485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37727106680230367054796323 56590660020345550582194485)
        ·
          refine ⟨5305374376907395367080733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56590660020345550582194485 5305374376907395367080733)
          ·
            refine ⟨1989515391340273262655275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5305374376907395367080733 1989515391340273262655275)
            ·
              refine ⟨2984273087010409893982913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989515391340273262655275 2984273087010409893982913)
              ·
                refine ⟨2238204815257807420487185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984273087010409893982913 2238204815257807420487185)
                ·
                  refine ⟨1678653611443355565365389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238204815257807420487185 1678653611443355565365389)
                  ·
                    refine ⟨629495104291258337012021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1678653611443355565365389 629495104291258337012021)
                    ·
                      rfl

theorem cell22_1838906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1838906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1838906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1838906 prefixEnd_1838906 := by exact prefixLift 1838906
  have htrace : WordTrace (prefixWord ++ tailWord_1838906) baseStart_1838906 baseEnd_1838906 := by
    simpa [prefixWord, tailWord_1838906, baseEnd_1838906] using wordTrace_append hprefix tailTrace_1838906
  have hstable : (prefixWord ++ tailWord_1838906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838906).length < 2 ^ (prefixWord ++ tailWord_1838906).sum := by decide
  have hdescent : baseEnd_1838906 < baseStart_1838906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839054 : List Nat := [4, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1839054 : Nat := 118140960795 + 1839054 * 2 ^ 59
def prefixEnd_1839054 : Nat := 4983230072969 + 3 ^ 40 * 1839054 * 2
def baseEnd_1839054 : Nat := 69949529746203920479063

theorem tailTrace_1839054 : CollatzResearch.WordTrace tailWord_1839054 prefixEnd_1839054 69949529746203920479063 := by
  unfold tailWord_1839054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384476234928614782836527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44717206586285945508461477 8384476234928614782836527)
  ·
    refine ⟨12576714352392922174254791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384476234928614782836527 12576714352392922174254791)
    ·
      refine ⟨18865071528589383261382187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12576714352392922174254791 18865071528589383261382187)
      ·
        refine ⟨28297607292884074892073281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865071528589383261382187 28297607292884074892073281)
        ·
          refine ⟨21223205469663056169054961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28297607292884074892073281 21223205469663056169054961)
          ·
            refine ⟨15917404102247292126791221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21223205469663056169054961 15917404102247292126791221)
            ·
              refine ⟨1492256634585683636886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15917404102247292126791221 1492256634585683636886677)
              ·
                refine ⟨69949529746203920479063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1492256634585683636886677 69949529746203920479063)
                ·
                  rfl

theorem cell22_1839054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1839054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839054 prefixEnd_1839054 := by exact prefixLift 1839054
  have htrace : WordTrace (prefixWord ++ tailWord_1839054) baseStart_1839054 baseEnd_1839054 := by
    simpa [prefixWord, tailWord_1839054, baseEnd_1839054] using wordTrace_append hprefix tailTrace_1839054
  have hstable : (prefixWord ++ tailWord_1839054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839054).length < 2 ^ (prefixWord ++ tailWord_1839054).sum := by decide
  have hdescent : baseEnd_1839054 < baseStart_1839054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839062 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1839062 : Nat := 118140960795 + 1839062 * 2 ^ 59
def prefixEnd_1839062 : Nat := 4983230072969 + 3 ^ 40 * 1839062 * 2
def baseEnd_1839062 : Nat := 629548506279325930111543

theorem tailTrace_1839062 : CollatzResearch.WordTrace tailWord_1839062 prefixEnd_1839062 629548506279325930111543 := by
  unfold tailWord_1839062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192256353962495976811465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44717401108933290419322293 4192256353962495976811465)
  ·
    refine ⟨3144192265471871982608599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4192256353962495976811465 3144192265471871982608599)
    ·
      refine ⟨4716288398207807973912899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144192265471871982608599 4716288398207807973912899)
      ·
        refine ⟨7074432597311711960869349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716288398207807973912899 7074432597311711960869349)
        ·
          refine ⟨1326456111995945992663003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7074432597311711960869349 1326456111995945992663003)
          ·
            refine ⟨1989684167993918988994505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326456111995945992663003 1989684167993918988994505)
            ·
              refine ⟨1492263125995439241745879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989684167993918988994505 1492263125995439241745879)
              ·
                refine ⟨2238394688993158862618819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492263125995439241745879 2238394688993158862618819)
                ·
                  refine ⟨3357592033489738293928229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238394688993158862618819 3357592033489738293928229)
                  ·
                    refine ⟨629548506279325930111543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3357592033489738293928229 629548506279325930111543)
                    ·
                      rfl

theorem cell22_1839062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1839062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839062 prefixEnd_1839062 := by exact prefixLift 1839062
  have htrace : WordTrace (prefixWord ++ tailWord_1839062) baseStart_1839062 baseEnd_1839062 := by
    simpa [prefixWord, tailWord_1839062, baseEnd_1839062] using wordTrace_append hprefix tailTrace_1839062
  have hstable : (prefixWord ++ tailWord_1839062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839062).length < 2 ^ (prefixWord ++ tailWord_1839062).sum := by decide
  have hdescent : baseEnd_1839062 < baseStart_1839062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839086 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1839086 : Nat := 118140960795 + 1839086 * 2 ^ 59
def prefixEnd_1839086 : Nat := 4983230072969 + 3 ^ 40 * 1839086 * 2
def baseEnd_1839086 : Nat := 629556721969797867511469

theorem tailTrace_1839086 : CollatzResearch.WordTrace tailWord_1839086 prefixEnd_1839086 629556721969797867511469 := by
  unfold tailWord_1839086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384622126914123465982139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44717984676875325151904741 8384622126914123465982139)
  ·
    refine ⟨12576933190371185198973209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384622126914123465982139 12576933190371185198973209)
    ·
      refine ⟨9432699892778388899229907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12576933190371185198973209 9432699892778388899229907)
      ·
        refine ⟨14149049839167583348844861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432699892778388899229907 14149049839167583348844861)
        ·
          refine ⟨5305893689687843755816823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14149049839167583348844861 5305893689687843755816823)
          ·
            refine ⟨7958840534531765633725235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305893689687843755816823 7958840534531765633725235)
            ·
              refine ⟨11938260801797648450587853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958840534531765633725235 11938260801797648450587853)
              ·
                refine ⟨4476847800674118168970445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11938260801797648450587853 4476847800674118168970445)
                ·
                  refine ⟨1678817925252794313363917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476847800674118168970445 1678817925252794313363917)
                  ·
                    refine ⟨629556721969797867511469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1678817925252794313363917 629556721969797867511469)
                    ·
                      rfl

theorem cell22_1839086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1839086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839086 prefixEnd_1839086 := by exact prefixLift 1839086
  have htrace : WordTrace (prefixWord ++ tailWord_1839086) baseStart_1839086 baseEnd_1839086 := by
    simpa [prefixWord, tailWord_1839086, baseEnd_1839086] using wordTrace_append hprefix tailTrace_1839086
  have hstable : (prefixWord ++ tailWord_1839086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839086).length < 2 ^ (prefixWord ++ tailWord_1839086).sum := by decide
  have hdescent : baseEnd_1839086 < baseStart_1839086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839311 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 4, 3]
def baseStart_1839311 : Nat := 118140960795 + 1839311 * 2 ^ 59
def prefixEnd_1839311 : Nat := 4983230072969 + 3 ^ 40 * 1839311 * 2
def baseEnd_1839311 : Nat := 629633744067972280635779

theorem tailTrace_1839311 : CollatzResearch.WordTrace tailWord_1839311 prefixEnd_1839311 629633744067972280635779 := by
  unfold tailWord_1839311
  simp only [CollatzResearch.WordTrace]
  refine ⟨67085183439497851154797787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44723455626331900769865191 67085183439497851154797787)
  ·
    refine ⟨100627775159246776732196681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67085183439497851154797787 100627775159246776732196681)
    ·
      refine ⟨75470831369435082549147511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100627775159246776732196681 75470831369435082549147511)
      ·
        refine ⟨113206247054152623823721267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75470831369435082549147511 113206247054152623823721267)
        ·
          refine ⟨169809370581228935735581901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113206247054152623823721267 169809370581228935735581901)
          ·
            refine ⟨63678513967960850900843213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169809370581228935735581901 63678513967960850900843213)
            ·
              refine ⟨23879442737985319087816205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63678513967960850900843213 23879442737985319087816205)
              ·
                refine ⟨8954791026744494657931077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23879442737985319087816205 8954791026744494657931077)
                ·
                  refine ⟨1679023317514592748362077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8954791026744494657931077 1679023317514592748362077)
                  ·
                    refine ⟨629633744067972280635779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679023317514592748362077 629633744067972280635779)
                    ·
                      rfl

theorem cell22_1839311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_1839311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839311 prefixEnd_1839311 := by exact prefixLift 1839311
  have htrace : WordTrace (prefixWord ++ tailWord_1839311) baseStart_1839311 baseEnd_1839311 := by
    simpa [prefixWord, tailWord_1839311, baseEnd_1839311] using wordTrace_append hprefix tailTrace_1839311
  have hstable : (prefixWord ++ tailWord_1839311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839311).length < 2 ^ (prefixWord ++ tailWord_1839311).sum := by decide
  have hdescent : baseEnd_1839311 < baseStart_1839311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839328 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_1839328 : Nat := 118140960795 + 1839328 * 2 ^ 59
def prefixEnd_1839328 : Nat := 4983230072969 + 3 ^ 40 * 1839328 * 2
def baseEnd_1839328 : Nat := 629639563515389902960727

theorem tailTrace_1839328 : CollatzResearch.WordTrace tailWord_1839328 prefixEnd_1839328 629639563515389902960727 := by
  unfold tailWord_1839328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542901740218131529083319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44723868986957508705444425 33542901740218131529083319)
  ·
    refine ⟨50314352610327197293624979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33542901740218131529083319 50314352610327197293624979)
    ·
      refine ⟨75471528915490795940437469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50314352610327197293624979 75471528915490795940437469)
      ·
        refine ⟨28301823343309048477664051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75471528915490795940437469 28301823343309048477664051)
        ·
          refine ⟨42452735014963572716496077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28301823343309048477664051 42452735014963572716496077)
          ·
            refine ⟨15919775630611339768686029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42452735014963572716496077 15919775630611339768686029)
            ·
              refine ⟨5969915861479252413257261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15919775630611339768686029 5969915861479252413257261)
              ·
                refine ⟨2238718448054719654971473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5969915861479252413257261 2238718448054719654971473)
                ·
                  refine ⟨1679038836041039741228605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238718448054719654971473 1679038836041039741228605)
                  ·
                    refine ⟨629639563515389902960727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679038836041039741228605 629639563515389902960727)
                    ·
                      rfl

theorem cell22_1839328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_1839328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839328 prefixEnd_1839328 := by exact prefixLift 1839328
  have htrace : WordTrace (prefixWord ++ tailWord_1839328) baseStart_1839328 baseEnd_1839328 := by
    simpa [prefixWord, tailWord_1839328, baseEnd_1839328] using wordTrace_append hprefix tailTrace_1839328
  have hstable : (prefixWord ++ tailWord_1839328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839328).length < 2 ^ (prefixWord ++ tailWord_1839328).sum := by decide
  have hdescent : baseEnd_1839328 < baseStart_1839328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839343 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_1839343 : Nat := 118140960795 + 1839343 * 2 ^ 59
def prefixEnd_1839343 : Nat := 4983230072969 + 3 ^ 40 * 1839343 * 2
def baseEnd_1839343 : Nat := 629644698321934863835681

theorem tailTrace_1839343 : CollatzResearch.WordTrace tailWord_1839343 prefixEnd_1839343 629644698321934863835681 := by
  unfold tailWord_1839343
  simp only [CollatzResearch.WordTrace]
  refine ⟨67086350575381920619962683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44724233716921280413308455 67086350575381920619962683)
  ·
    refine ⟨100629525863072880929944025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67086350575381920619962683 100629525863072880929944025)
    ·
      refine ⟨75472144397304660697458019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100629525863072880929944025 75472144397304660697458019)
      ·
        refine ⟨113208216595956991046187029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75472144397304660697458019 113208216595956991046187029)
        ·
          refine ⟨5306635152935483955290017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113208216595956991046187029 5306635152935483955290017)
          ·
            refine ⟨3979976364701612966467513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5306635152935483955290017 3979976364701612966467513)
            ·
              refine ⟨2984982273526209724850635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3979976364701612966467513 2984982273526209724850635)
              ·
                refine ⟨4477473410289314587275953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984982273526209724850635 4477473410289314587275953)
                ·
                  refine ⟨3358105057716985940456965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477473410289314587275953 3358105057716985940456965)
                  ·
                    refine ⟨629644698321934863835681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358105057716985940456965 629644698321934863835681)
                    ·
                      rfl

theorem cell22_1839343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_1839343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839343 prefixEnd_1839343 := by exact prefixLift 1839343
  have htrace : WordTrace (prefixWord ++ tailWord_1839343) baseStart_1839343 baseEnd_1839343 := by
    simpa [prefixWord, tailWord_1839343, baseEnd_1839343] using wordTrace_append hprefix tailTrace_1839343
  have hstable : (prefixWord ++ tailWord_1839343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839343).length < 2 ^ (prefixWord ++ tailWord_1839343).sum := by decide
  have hdescent : baseEnd_1839343 < baseStart_1839343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839362 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1839362 : Nat := 118140960795 + 1839362 * 2 ^ 59
def prefixEnd_1839362 : Nat := 4983230072969 + 3 ^ 40 * 1839362 * 2
def baseEnd_1839362 : Nat := 629651202410225147610623

theorem tailTrace_1839362 : CollatzResearch.WordTrace tailWord_1839362 prefixEnd_1839362 629651202410225147610623 := by
  unfold tailWord_1839362
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771760890578271716226085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44724695708208724576602893 16771760890578271716226085)
  ·
    refine ⟨3144705166983425946792391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16771760890578271716226085 3144705166983425946792391)
    ·
      refine ⟨4717057750475138920188587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144705166983425946792391 4717057750475138920188587)
      ·
        refine ⟨7075586625712708380282881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717057750475138920188587 7075586625712708380282881)
        ·
          refine ⟨5306689969284531285212161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7075586625712708380282881 5306689969284531285212161)
          ·
            refine ⟨3980017476963398463909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5306689969284531285212161 3980017476963398463909121)
            ·
              refine ⟨2985013107722548847931841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980017476963398463909121 2985013107722548847931841)
              ·
                refine ⟨2238759830791911635948881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985013107722548847931841 2238759830791911635948881)
                ·
                  refine ⟨1679069873093933726961661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238759830791911635948881 1679069873093933726961661)
                  ·
                    refine ⟨629651202410225147610623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679069873093933726961661 629651202410225147610623)
                    ·
                      rfl

theorem cell22_1839362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1839362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839362 prefixEnd_1839362 := by exact prefixLift 1839362
  have htrace : WordTrace (prefixWord ++ tailWord_1839362) baseStart_1839362 baseEnd_1839362 := by
    simpa [prefixWord, tailWord_1839362, baseEnd_1839362] using wordTrace_append hprefix tailTrace_1839362
  have hstable : (prefixWord ++ tailWord_1839362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839362).length < 2 ^ (prefixWord ++ tailWord_1839362).sum := by decide
  have hdescent : baseEnd_1839362 < baseStart_1839362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839364 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1839364 : Nat := 118140960795 + 1839364 * 2 ^ 59
def prefixEnd_1839364 : Nat := 4983230072969 + 3 ^ 40 * 1839364 * 2
def baseEnd_1839364 : Nat := 209883962350365936353539

theorem tailTrace_1839364 : CollatzResearch.WordTrace tailWord_1839364 prefixEnd_1839364 209883962350365936353539 := by
  unfold tailWord_1839364
  simp only [CollatzResearch.WordTrace]
  refine ⟨33543558254152920603238573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44724744338870560804318097 33543558254152920603238573)
  ·
    refine ⟨12578834345307345226214465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33543558254152920603238573 12578834345307345226214465)
    ·
      refine ⟨9434125758980508919660849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12578834345307345226214465 9434125758980508919660849)
      ·
        refine ⟨7075594319235381689745637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9434125758980508919660849 7075594319235381689745637)
        ·
          refine ⟨1326673934856634066827307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7075594319235381689745637 1326673934856634066827307)
          ·
            refine ⟨1990010902284951100240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326673934856634066827307 1990010902284951100240961)
            ·
              refine ⟨1492508176713713325180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990010902284951100240961 1492508176713713325180721)
              ·
                refine ⟨1119381132535284993885541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492508176713713325180721 1119381132535284993885541)
                ·
                  refine ⟨209883962350365936353539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119381132535284993885541 209883962350365936353539)
                  ·
                    rfl

theorem cell22_1839364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1839364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839364 prefixEnd_1839364 := by exact prefixLift 1839364
  have htrace : WordTrace (prefixWord ++ tailWord_1839364) baseStart_1839364 baseEnd_1839364 := by
    simpa [prefixWord, tailWord_1839364, baseEnd_1839364] using wordTrace_append hprefix tailTrace_1839364
  have hstable : (prefixWord ++ tailWord_1839364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839364).length < 2 ^ (prefixWord ++ tailWord_1839364).sum := by decide
  have hdescent : baseEnd_1839364 < baseStart_1839364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839497 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_1839497 : Nat := 118140960795 + 1839497 * 2 ^ 59
def prefixEnd_1839497 : Nat := 4983230072969 + 3 ^ 40 * 1839497 * 2
def baseEnd_1839497 : Nat := 629697415669129795485209

theorem tailTrace_1839497 : CollatzResearch.WordTrace tailWord_1839497 prefixEnd_1839497 629697415669129795485209 := by
  unfold tailWord_1839497
  simp only [CollatzResearch.WordTrace]
  refine ⟨67091967416824004921068745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44727978277882669947379163 67091967416824004921068745)
  ·
    refine ⟨50318975562618003690801559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67091967416824004921068745 50318975562618003690801559)
    ·
      refine ⟨75478463343927005536202339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50318975562618003690801559 75478463343927005536202339)
      ·
        refine ⟨113217695015890508304303509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75478463343927005536202339 113217695015890508304303509)
        ·
          refine ⟨5307079453869867576764227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113217695015890508304303509 5307079453869867576764227)
          ·
            refine ⟨7960619180804801365146341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307079453869867576764227 7960619180804801365146341)
            ·
              refine ⟨1492616096400900255964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7960619180804801365146341 1492616096400900255964939)
              ·
                refine ⟨2238924144601350383947409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492616096400900255964939 2238924144601350383947409)
                ·
                  refine ⟨1679193108451012787960557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238924144601350383947409 1679193108451012787960557)
                  ·
                    refine ⟨629697415669129795485209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679193108451012787960557 629697415669129795485209)
                    ·
                      rfl

theorem cell22_1839497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_1839497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839497 prefixEnd_1839497 := by exact prefixLift 1839497
  have htrace : WordTrace (prefixWord ++ tailWord_1839497) baseStart_1839497 baseEnd_1839497 := by
    simpa [prefixWord, tailWord_1839497, baseEnd_1839497] using wordTrace_append hprefix tailTrace_1839497
  have hstable : (prefixWord ++ tailWord_1839497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839497).length < 2 ^ (prefixWord ++ tailWord_1839497).sum := by decide
  have hdescent : baseEnd_1839497 < baseStart_1839497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839585 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1839585 : Nat := 118140960795 + 1839585 * 2 ^ 59
def prefixEnd_1839585 : Nat := 4983230072969 + 3 ^ 40 * 1839585 * 2
def baseEnd_1839585 : Nat := 629727539867526899284939

theorem tailTrace_1839585 : CollatzResearch.WordTrace tailWord_1839585 prefixEnd_1839585 629727539867526899284939 := by
  unfold tailWord_1839585
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095177040505195950272209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730118027003463966848139 67095177040505195950272209)
  ·
    refine ⟨50321382780378896962704157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67095177040505195950272209 50321382780378896962704157)
    ·
      refine ⟨18870518542642086361014059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50321382780378896962704157 18870518542642086361014059)
      ·
        refine ⟨28305777813963129541521089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18870518542642086361014059 28305777813963129541521089)
        ·
          refine ⟨21229333360472347156140817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28305777813963129541521089 21229333360472347156140817)
          ·
            refine ⟨15922000020354260367105613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21229333360472347156140817 15922000020354260367105613)
            ·
              refine ⟨5970750007632847637664605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15922000020354260367105613 5970750007632847637664605)
              ·
                refine ⟨2239031252862317864124227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5970750007632847637664605 2239031252862317864124227)
                ·
                  refine ⟨3358546879293476796186341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239031252862317864124227 3358546879293476796186341)
                  ·
                    refine ⟨629727539867526899284939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358546879293476796186341 629727539867526899284939)
                    ·
                      rfl

theorem cell22_1839585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1839585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839585 prefixEnd_1839585 := by exact prefixLift 1839585
  have htrace : WordTrace (prefixWord ++ tailWord_1839585) baseStart_1839585 baseEnd_1839585 := by
    simpa [prefixWord, tailWord_1839585, baseEnd_1839585] using wordTrace_append hprefix tailTrace_1839585
  have hstable : (prefixWord ++ tailWord_1839585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839585).length < 2 ^ (prefixWord ++ tailWord_1839585).sum := by decide
  have hdescent : baseEnd_1839585 < baseStart_1839585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839589 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 5]
def baseStart_1839589 : Nat := 118140960795 + 1839589 * 2 ^ 59
def prefixEnd_1839589 : Nat := 4983230072969 + 3 ^ 40 * 1839589 * 2
def baseEnd_1839589 : Nat := 209909636383090740728309

theorem tailTrace_1839589 : CollatzResearch.WordTrace tailWord_1839589 prefixEnd_1839589 209909636383090740728309 := by
  unfold tailWord_1839589
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095322932490704633417821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730215288327136422278547 67095322932490704633417821)
  ·
    refine ⟨25160746099684014237531683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67095322932490704633417821 25160746099684014237531683)
    ·
      refine ⟨37741119149526021356297525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25160746099684014237531683 37741119149526021356297525)
      ·
        refine ⟨3538229920268064502152893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37741119149526021356297525 3538229920268064502152893)
        ·
          refine ⟨1326836220100524188307335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3538229920268064502152893 1326836220100524188307335)
          ·
            refine ⟨1990254330150786282461003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326836220100524188307335 1990254330150786282461003)
            ·
              refine ⟨2985381495226179423691505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990254330150786282461003 2985381495226179423691505)
              ·
                refine ⟨2239036121419634567768629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985381495226179423691505 2239036121419634567768629)
                ·
                  refine ⟨209909636383090740728309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239036121419634567768629 209909636383090740728309)
                  ·
                    rfl

theorem cell22_1839589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_1839589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839589 prefixEnd_1839589 := by exact prefixLift 1839589
  have htrace : WordTrace (prefixWord ++ tailWord_1839589) baseStart_1839589 baseEnd_1839589 := by
    simpa [prefixWord, tailWord_1839589, baseEnd_1839589] using wordTrace_append hprefix tailTrace_1839589
  have hstable : (prefixWord ++ tailWord_1839589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839589).length < 2 ^ (prefixWord ++ tailWord_1839589).sum := by decide
  have hdescent : baseEnd_1839589 < baseStart_1839589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839600 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 4]
def baseStart_1839600 : Nat := 118140960795 + 1839600 * 2 ^ 59
def prefixEnd_1839600 : Nat := 4983230072969 + 3 ^ 40 * 1839600 * 2
def baseEnd_1839600 : Nat := 209910891558023953386631

theorem tailTrace_1839600 : CollatzResearch.WordTrace tailWord_1839600 prefixEnd_1839600 209910891558023953386631 := by
  unfold tailWord_1839600
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547862067725426756034127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44730482756967235674712169 33547862067725426756034127)
  ·
    refine ⟨50321793101588140134051191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33547862067725426756034127 50321793101588140134051191)
    ·
      refine ⟨75482689652382210201076787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50321793101588140134051191 75482689652382210201076787)
      ·
        refine ⟨113224034478573315301615181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75482689652382210201076787 113224034478573315301615181)
        ·
          refine ⟨42459012929464993238105693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113224034478573315301615181 42459012929464993238105693)
          ·
            refine ⟨15922129848549372464289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42459012929464993238105693 15922129848549372464289635)
            ·
              refine ⟨23883194772824058696434453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922129848549372464289635 23883194772824058696434453)
              ·
                refine ⟨1119524754976127751395365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23883194772824058696434453 1119524754976127751395365)
                ·
                  refine ⟨209910891558023953386631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119524754976127751395365 209910891558023953386631)
                  ·
                    rfl

theorem cell22_1839600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 4].length) (baseStart_1839600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839600 prefixEnd_1839600 := by exact prefixLift 1839600
  have htrace : WordTrace (prefixWord ++ tailWord_1839600) baseStart_1839600 baseEnd_1839600 := by
    simpa [prefixWord, tailWord_1839600, baseEnd_1839600] using wordTrace_append hprefix tailTrace_1839600
  have hstable : (prefixWord ++ tailWord_1839600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839600).length < 2 ^ (prefixWord ++ tailWord_1839600).sum := by decide
  have hdescent : baseEnd_1839600 < baseStart_1839600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839613 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1839613 : Nat := 118140960795 + 1839613 * 2 ^ 59
def prefixEnd_1839613 : Nat := 4983230072969 + 3 ^ 40 * 1839613 * 2
def baseEnd_1839613 : Nat := 629737124839744159584853

theorem tailTrace_1839613 : CollatzResearch.WordTrace tailWord_1839613 prefixEnd_1839613 629737124839744159584853 := by
  unfold tailWord_1839613
  simp only [CollatzResearch.WordTrace]
  refine ⟨67096198284403756732291493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730798856269171154860995 67096198284403756732291493)
  ·
    refine ⟨12580537178325704387304655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67096198284403756732291493 12580537178325704387304655)
    ·
      refine ⟨18870805767488556580956983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580537178325704387304655 18870805767488556580956983)
      ·
        refine ⟨28306208651232834871435475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18870805767488556580956983 28306208651232834871435475)
        ·
          refine ⟨42459312976849252307153213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28306208651232834871435475 42459312976849252307153213)
          ·
            refine ⟨15922242366318469615182455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42459312976849252307153213 15922242366318469615182455)
            ·
              refine ⟨23883363549477704422773683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922242366318469615182455 23883363549477704422773683)
              ·
                refine ⟨35825045324216556634160525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883363549477704422773683 35825045324216556634160525)
                ·
                  refine ⟨13434391996581208737810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35825045324216556634160525 13434391996581208737810197)
                  ·
                    refine ⟨629737124839744159584853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13434391996581208737810197 629737124839744159584853)
                    ·
                      rfl

theorem cell22_1839613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1839613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839613 prefixEnd_1839613 := by exact prefixLift 1839613
  have htrace : WordTrace (prefixWord ++ tailWord_1839613) baseStart_1839613 baseEnd_1839613 := by
    simpa [prefixWord, tailWord_1839613, baseEnd_1839613] using wordTrace_append hprefix tailTrace_1839613
  have hstable : (prefixWord ++ tailWord_1839613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839613).length < 2 ^ (prefixWord ++ tailWord_1839613).sum := by decide
  have hdescent : baseEnd_1839613 < baseStart_1839613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839630 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1839630 : Nat := 118140960795 + 1839630 * 2 ^ 59
def prefixEnd_1839630 : Nat := 4983230072969 + 3 ^ 40 * 1839630 * 2
def baseEnd_1839630 : Nat := 629742944287161781909801

theorem tailTrace_1839630 : CollatzResearch.WordTrace tailWord_1839630 prefixEnd_1839630 629742944287161781909801 := by
  unfold tailWord_1839630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387102290667771079457543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44731212216894779090440229 8387102290667771079457543)
  ·
    refine ⟨12580653436001656619186315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387102290667771079457543 12580653436001656619186315)
    ·
      refine ⟨18870980154002484928779473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580653436001656619186315 18870980154002484928779473)
      ·
        refine ⟨14153235115501863696584605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18870980154002484928779473 14153235115501863696584605)
        ·
          refine ⟨5307463168313198886219227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14153235115501863696584605 5307463168313198886219227)
          ·
            refine ⟨7961194752469798329328841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307463168313198886219227 7961194752469798329328841)
            ·
              refine ⟨5970896064352348746996631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961194752469798329328841 5970896064352348746996631)
              ·
                refine ⟨8956344096528523120494947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970896064352348746996631 8956344096528523120494947)
                ·
                  refine ⟨13434516144792784680742421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956344096528523120494947 13434516144792784680742421)
                  ·
                    refine ⟨629742944287161781909801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13434516144792784680742421 629742944287161781909801)
                    ·
                      rfl

theorem cell22_1839630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1839630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839630 prefixEnd_1839630 := by exact prefixLift 1839630
  have htrace : WordTrace (prefixWord ++ tailWord_1839630) baseStart_1839630 baseEnd_1839630 := by
    simpa [prefixWord, tailWord_1839630, baseEnd_1839630] using wordTrace_append hprefix tailTrace_1839630
  have hstable : (prefixWord ++ tailWord_1839630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839630).length < 2 ^ (prefixWord ++ tailWord_1839630).sum := by decide
  have hdescent : baseEnd_1839630 < baseStart_1839630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839645 : List Nat := [1, 4, 2, 2, 1, 4, 8]
def baseStart_1839645 : Nat := 118140960795 + 1839645 * 2 ^ 59
def prefixEnd_1839645 : Nat := 4983230072969 + 3 ^ 40 * 1839645 * 2
def baseEnd_1839645 : Nat := 23324002929396546029065

theorem tailTrace_1839645 : CollatzResearch.WordTrace tailWord_1839645 prefixEnd_1839645 23324002929396546029065 := by
  unfold tailWord_1839645
  simp only [CollatzResearch.WordTrace]
  refine ⟨67097365420287826197456389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44731576946858550798304259 67097365420287826197456389)
  ·
    refine ⟨12580756016303967412023073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67097365420287826197456389 12580756016303967412023073)
    ·
      refine ⟨9435567012227975559017305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12580756016303967412023073 9435567012227975559017305)
      ·
        refine ⟨7076675259170981669262979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9435567012227975559017305 7076675259170981669262979)
        ·
          refine ⟨10615012888756472503894469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076675259170981669262979 10615012888756472503894469)
          ·
            refine ⟨1990314916641838594480213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10615012888756472503894469 1990314916641838594480213)
            ·
              refine ⟨23324002929396546029065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1990314916641838594480213 23324002929396546029065)
              ·
                rfl

theorem cell22_1839645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 8].length) (baseStart_1839645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839645 prefixEnd_1839645 := by exact prefixLift 1839645
  have htrace : WordTrace (prefixWord ++ tailWord_1839645) baseStart_1839645 baseEnd_1839645 := by
    simpa [prefixWord, tailWord_1839645, baseEnd_1839645] using wordTrace_append hprefix tailTrace_1839645
  have hstable : (prefixWord ++ tailWord_1839645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839645).length < 2 ^ (prefixWord ++ tailWord_1839645).sum := by decide
  have hdescent : baseEnd_1839645 < baseStart_1839645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839662 : List Nat := [4, 1, 3, 1, 3, 1, 2, 7]
def baseStart_1839662 : Nat := 118140960795 + 1839662 * 2 ^ 59
def prefixEnd_1839662 : Nat := 4983230072969 + 3 ^ 40 * 1839662 * 2
def baseEnd_1839662 : Nat := 69972655393458262789967

theorem tailTrace_1839662 : CollatzResearch.WordTrace tailWord_1839662 prefixEnd_1839662 69972655393458262789967 := by
  unfold tailWord_1839662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387248182653279762603155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44731990307484158733883493 8387248182653279762603155)
  ·
    refine ⟨12580872273979919643904733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387248182653279762603155 12580872273979919643904733)
    ·
      refine ⟨4717827102742469866464275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12580872273979919643904733 4717827102742469866464275)
      ·
        refine ⟨7076740654113704799696413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717827102742469866464275 7076740654113704799696413)
        ·
          refine ⟨2653777745292639299886155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7076740654113704799696413 2653777745292639299886155)
          ·
            refine ⟨3980666617938958949829233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653777745292639299886155 3980666617938958949829233)
            ·
              refine ⟨2985499963454219212371925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980666617938958949829233 2985499963454219212371925)
              ·
                refine ⟨69972655393458262789967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2985499963454219212371925 69972655393458262789967)
                ·
                  rfl

theorem cell22_1839662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_1839662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839662 prefixEnd_1839662 := by exact prefixLift 1839662
  have htrace : WordTrace (prefixWord ++ tailWord_1839662) baseStart_1839662 baseEnd_1839662 := by
    simpa [prefixWord, tailWord_1839662, baseEnd_1839662] using wordTrace_append hprefix tailTrace_1839662
  have hstable : (prefixWord ++ tailWord_1839662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839662).length < 2 ^ (prefixWord ++ tailWord_1839662).sum := by decide
  have hdescent : baseEnd_1839662 < baseStart_1839662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839754 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1839754 : Nat := 118140960795 + 1839754 * 2 ^ 59
def prefixEnd_1839754 : Nat := 4983230072969 + 3 ^ 40 * 1839754 * 2
def baseEnd_1839754 : Nat := 629785392021266791809421

theorem tailTrace_1839754 : CollatzResearch.WordTrace tailWord_1839754 prefixEnd_1839754 629785392021266791809421 := by
  unfold tailWord_1839754
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775335244223234453293579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44734227317928625208782877 16775335244223234453293579)
  ·
    refine ⟨25163002866334851679940369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16775335244223234453293579 25163002866334851679940369)
    ·
      refine ⟨18872252149751138759955277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25163002866334851679940369 18872252149751138759955277)
      ·
        refine ⟨7077094556156677034983229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18872252149751138759955277 7077094556156677034983229)
        ·
          refine ⟨2653910458558753888118711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7077094556156677034983229 2653910458558753888118711)
          ·
            refine ⟨3980865687838130832178067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653910458558753888118711 3980865687838130832178067)
            ·
              refine ⟨5971298531757196248267101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980865687838130832178067 5971298531757196248267101)
              ·
                refine ⟨2239236949408948593100163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5971298531757196248267101 2239236949408948593100163)
                ·
                  refine ⟨3358855424113422889650245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239236949408948593100163 3358855424113422889650245)
                  ·
                    refine ⟨629785392021266791809421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358855424113422889650245 629785392021266791809421)
                    ·
                      rfl

theorem cell22_1839754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1839754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839754 prefixEnd_1839754 := by exact prefixLift 1839754
  have htrace : WordTrace (prefixWord ++ tailWord_1839754) baseStart_1839754 baseEnd_1839754 := by
    simpa [prefixWord, tailWord_1839754, baseEnd_1839754] using wordTrace_append hprefix tailTrace_1839754
  have hstable : (prefixWord ++ tailWord_1839754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839754).length < 2 ^ (prefixWord ++ tailWord_1839754).sum := by decide
  have hdescent : baseEnd_1839754 < baseStart_1839754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839767 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1839767 : Nat := 118140960795 + 1839767 * 2 ^ 59
def prefixEnd_1839767 : Nat := 4983230072969 + 3 ^ 40 * 1839767 * 2
def baseEnd_1839767 : Nat := 629789842186939091234381

theorem tailTrace_1839767 : CollatzResearch.WordTrace tailWord_1839767 prefixEnd_1839767 629789842186939091234381 := by
  unfold tailWord_1839767
  simp only [CollatzResearch.WordTrace]
  refine ⟨67101815125845841033397555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44734543417230560688931703 67101815125845841033397555)
  ·
    refine ⟨100652722688768761550096333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67101815125845841033397555 100652722688768761550096333)
    ·
      refine ⟨37744771008288285581286125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100652722688768761550096333 37744771008288285581286125)
      ·
        refine ⟨14154289128108107092982297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37744771008288285581286125 14154289128108107092982297)
        ·
          refine ⟨10615716846081080319736723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14154289128108107092982297 10615716846081080319736723)
          ·
            refine ⟨15923575269121620479605085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10615716846081080319736723 15923575269121620479605085)
            ·
              refine ⟨5971340725920607679851907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15923575269121620479605085 5971340725920607679851907)
              ·
                refine ⟨8957011088880911519777861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971340725920607679851907 8957011088880911519777861)
                ·
                  refine ⟨1679439579165170909958349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8957011088880911519777861 1679439579165170909958349)
                  ·
                    refine ⟨629789842186939091234381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679439579165170909958349 629789842186939091234381)
                    ·
                      rfl

theorem cell22_1839767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1839767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839767 prefixEnd_1839767 := by exact prefixLift 1839767
  have htrace : WordTrace (prefixWord ++ tailWord_1839767) baseStart_1839767 baseEnd_1839767 := by
    simpa [prefixWord, tailWord_1839767, baseEnd_1839767] using wordTrace_append hprefix tailTrace_1839767
  have hstable : (prefixWord ++ tailWord_1839767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839767).length < 2 ^ (prefixWord ++ tailWord_1839767).sum := by decide
  have hdescent : baseEnd_1839767 < baseStart_1839767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839780 : List Nat := [2, 3, 1, 2, 2, 1, 2, 9]
def baseStart_1839780 : Nat := 118140960795 + 1839780 * 2 ^ 59
def prefixEnd_1839780 : Nat := 4983230072969 + 3 ^ 40 * 1839780 * 2
def baseEnd_1839780 : Nat := 69977143594734598962149

theorem tailTrace_1839780 : CollatzResearch.WordTrace tailWord_1839780 prefixEnd_1839780 69977143594734598962149 := by
  unfold tailWord_1839780
  simp only [CollatzResearch.WordTrace]
  refine ⟨33551144637399372126810397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44734859516532496169080529 33551144637399372126810397)
  ·
    refine ⟨12581679239024764547553899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33551144637399372126810397 12581679239024764547553899)
    ·
      refine ⟨18872518858537146821330849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12581679239024764547553899 18872518858537146821330849)
      ·
        refine ⟨14154389143902860115998137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18872518858537146821330849 14154389143902860115998137)
        ·
          refine ⟨10615791857927145086998603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14154389143902860115998137 10615791857927145086998603)
          ·
            refine ⟨15923687786890717630497905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10615791857927145086998603 15923687786890717630497905)
            ·
              refine ⟨11942765840168038222873429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15923687786890717630497905 11942765840168038222873429)
              ·
                refine ⟨69977143594734598962149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11942765840168038222873429 69977143594734598962149)
                ·
                  rfl

theorem cell22_1839780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 9].length) (baseStart_1839780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839780 prefixEnd_1839780 := by exact prefixLift 1839780
  have htrace : WordTrace (prefixWord ++ tailWord_1839780) baseStart_1839780 baseEnd_1839780 := by
    simpa [prefixWord, tailWord_1839780, baseEnd_1839780] using wordTrace_append hprefix tailTrace_1839780
  have hstable : (prefixWord ++ tailWord_1839780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839780).length < 2 ^ (prefixWord ++ tailWord_1839780).sum := by decide
  have hdescent : baseEnd_1839780 < baseStart_1839780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839797 : List Nat := [1, 3, 3, 3, 1, 2, 1, 8]
def baseStart_1839797 : Nat := 118140960795 + 1839797 * 2 ^ 59
def prefixEnd_1839797 : Nat := 4983230072969 + 3 ^ 40 * 1839797 * 2
def baseEnd_1839797 : Nat := 69977790200003223664921

theorem tailTrace_1839797 : CollatzResearch.WordTrace tailWord_1839797 prefixEnd_1839797 69977790200003223664921 := by
  unfold tailWord_1839797
  simp only [CollatzResearch.WordTrace]
  refine ⟨67102909315737156156989645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44735272877158104104659763 67102909315737156156989645)
  ·
    refine ⟨25163590993401433558871117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67102909315737156156989645 25163590993401433558871117)
    ·
      refine ⟨9436346622525537584576669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25163590993401433558871117 9436346622525537584576669)
      ·
        refine ⟨3538629983447076594216251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9436346622525537584576669 3538629983447076594216251)
        ·
          refine ⟨5307944975170614891324377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538629983447076594216251 5307944975170614891324377)
          ·
            refine ⟨3980958731377961168493283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307944975170614891324377 3980958731377961168493283)
            ·
              refine ⟨5971438097066941752739925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980958731377961168493283 5971438097066941752739925)
              ·
                refine ⟨69977790200003223664921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5971438097066941752739925 69977790200003223664921)
                ·
                  rfl

theorem cell22_1839797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 8].length) (baseStart_1839797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839797 prefixEnd_1839797 := by exact prefixLift 1839797
  have htrace : WordTrace (prefixWord ++ tailWord_1839797) baseStart_1839797 baseEnd_1839797 := by
    simpa [prefixWord, tailWord_1839797, baseEnd_1839797] using wordTrace_append hprefix tailTrace_1839797
  have hstable : (prefixWord ++ tailWord_1839797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839797).length < 2 ^ (prefixWord ++ tailWord_1839797).sum := by decide
  have hdescent : baseEnd_1839797 < baseStart_1839797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839825 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 7]
def baseStart_1839825 : Nat := 118140960795 + 1839825 * 2 ^ 59
def prefixEnd_1839825 : Nat := 4983230072969 + 3 ^ 40 * 1839825 * 2
def baseEnd_1839825 : Nat := 209936565590748757761401

theorem tailTrace_1839825 : CollatzResearch.WordTrace tailWord_1839825 prefixEnd_1839825 209936565590748757761401 := by
  unfold tailWord_1839825
  simp only [CollatzResearch.WordTrace]
  refine ⟨67103930559635716939008929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44735953706423811292672619 67103930559635716939008929)
  ·
    refine ⟨50327947919726787704256697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67103930559635716939008929 50327947919726787704256697)
    ·
      refine ⟨37745960939795090778192523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50327947919726787704256697 37745960939795090778192523)
      ·
        refine ⟨56618941409692636167288785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37745960939795090778192523 56618941409692636167288785)
        ·
          refine ⟨42464206057269477125466589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56618941409692636167288785 42464206057269477125466589)
          ·
            refine ⟨15924077271476053922049971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42464206057269477125466589 15924077271476053922049971)
            ·
              refine ⟨23886115907214080883074957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15924077271476053922049971 23886115907214080883074957)
              ·
                refine ⟨8957293465205280331153109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23886115907214080883074957 8957293465205280331153109)
                ·
                  refine ⟨209936565590748757761401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8957293465205280331153109 209936565590748757761401)
                  ·
                    rfl

theorem cell22_1839825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_1839825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839825 prefixEnd_1839825 := by exact prefixLift 1839825
  have htrace : WordTrace (prefixWord ++ tailWord_1839825) baseStart_1839825 baseEnd_1839825 := by
    simpa [prefixWord, tailWord_1839825, baseEnd_1839825] using wordTrace_append hprefix tailTrace_1839825
  have hstable : (prefixWord ++ tailWord_1839825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839825).length < 2 ^ (prefixWord ++ tailWord_1839825).sum := by decide
  have hdescent : baseEnd_1839825 < baseStart_1839825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839840 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_1839840 : Nat := 118140960795 + 1839840 * 2 ^ 59
def prefixEnd_1839840 : Nat := 4983230072969 + 3 ^ 40 * 1839840 * 2
def baseEnd_1839840 : Nat := 629814831578791234159157

theorem tailTrace_1839840 : CollatzResearch.WordTrace tailWord_1839840 prefixEnd_1839840 629814831578791234159157 := by
  unfold tailWord_1839840
  simp only [CollatzResearch.WordTrace]
  refine ⟨33552238827290687250402487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44736318436387583000536649 33552238827290687250402487)
  ·
    refine ⟨50328358240936030875603731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33552238827290687250402487 50328358240936030875603731)
    ·
      refine ⟨75492537361404046313405597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50328358240936030875603731 75492537361404046313405597)
      ·
        refine ⟨28309701510526517367527099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75492537361404046313405597 28309701510526517367527099)
        ·
          refine ⟨42464552265789776051290649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28309701510526517367527099 42464552265789776051290649)
          ·
            refine ⟨31848414199342332038467987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42464552265789776051290649 31848414199342332038467987)
            ·
              refine ⟨47772621299013498057701981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31848414199342332038467987 47772621299013498057701981)
              ·
                refine ⟨17914732987130061771638243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47772621299013498057701981 17914732987130061771638243)
                ·
                  refine ⟨26872099480695092657457365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17914732987130061771638243 26872099480695092657457365)
                  ·
                    refine ⟨629814831578791234159157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26872099480695092657457365 629814831578791234159157)
                    ·
                      rfl

theorem cell22_1839840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_1839840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839840 prefixEnd_1839840 := by exact prefixLift 1839840
  have htrace : WordTrace (prefixWord ++ tailWord_1839840) baseStart_1839840 baseEnd_1839840 := by
    simpa [prefixWord, tailWord_1839840, baseEnd_1839840] using wordTrace_append hprefix tailTrace_1839840
  have hstable : (prefixWord ++ tailWord_1839840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839840).length < 2 ^ (prefixWord ++ tailWord_1839840).sum := by decide
  have hdescent : baseEnd_1839840 < baseStart_1839840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839953 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_1839953 : Nat := 118140960795 + 1839953 * 2 ^ 59
def prefixEnd_1839953 : Nat := 4983230072969 + 3 ^ 40 * 1839953 * 2
def baseEnd_1839953 : Nat := 629853513788096606083811

theorem tailTrace_1839953 : CollatzResearch.WordTrace tailWord_1839953 prefixEnd_1839953 629853513788096606083811 := by
  unfold tailWord_1839953
  simp only [CollatzResearch.WordTrace]
  refine ⟨67108599103171994799668513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44739066068781329866445675 67108599103171994799668513)
  ·
    refine ⟨50331449327378996099751385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67108599103171994799668513 50331449327378996099751385)
    ·
      refine ⟨37748586995534247074813539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50331449327378996099751385 37748586995534247074813539)
      ·
        refine ⟨56622880493301370612220309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748586995534247074813539 56622880493301370612220309)
        ·
          refine ⟨2654197523123501747447827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56622880493301370612220309 2654197523123501747447827)
          ·
            refine ⟨3981296284685252621171741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654197523123501747447827 3981296284685252621171741)
            ·
              refine ⟨1492986106756969732939403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3981296284685252621171741 1492986106756969732939403)
              ·
                refine ⟨2239479160135454599409105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492986106756969732939403 2239479160135454599409105)
                ·
                  refine ⟨1679609370101590949556829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239479160135454599409105 1679609370101590949556829)
                  ·
                    refine ⟨629853513788096606083811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679609370101590949556829 629853513788096606083811)
                    ·
                      rfl

theorem cell22_1839953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_1839953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839953 prefixEnd_1839953 := by exact prefixLift 1839953
  have htrace : WordTrace (prefixWord ++ tailWord_1839953) baseStart_1839953 baseEnd_1839953 := by
    simpa [prefixWord, tailWord_1839953, baseEnd_1839953] using wordTrace_append hprefix tailTrace_1839953
  have hstable : (prefixWord ++ tailWord_1839953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839953).length < 2 ^ (prefixWord ++ tailWord_1839953).sum := by decide
  have hdescent : baseEnd_1839953 < baseStart_1839953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839992 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_1839992 : Nat := 118140960795 + 1839992 * 2 ^ 59
def prefixEnd_1839992 : Nat := 4983230072969 + 3 ^ 40 * 1839992 * 2
def baseEnd_1839992 : Nat := 629866864285113504358691

theorem tailTrace_1839992 : CollatzResearch.WordTrace tailWord_1839992 prefixEnd_1839992 629866864285113504358691 := by
  unfold tailWord_1839992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555010775015352230169115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44740014366687136306892153 33555010775015352230169115)
  ·
    refine ⟨50332516162523028345253673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33555010775015352230169115 50332516162523028345253673)
    ·
      refine ⟨37749387121892271258940255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50332516162523028345253673 37749387121892271258940255)
      ·
        refine ⟨56624080682838406888410383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37749387121892271258940255 56624080682838406888410383)
        ·
          refine ⟨84936121024257610332615575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56624080682838406888410383 84936121024257610332615575)
          ·
            refine ⟨127404181536386415498923363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84936121024257610332615575 127404181536386415498923363)
            ·
              refine ⟨191106272304579623248385045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127404181536386415498923363 191106272304579623248385045)
              ·
                refine ⟨8958106514277169839768049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191106272304579623248385045 8958106514277169839768049)
                ·
                  refine ⟨6718579885707877379826037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958106514277169839768049 6718579885707877379826037)
                  ·
                    refine ⟨629866864285113504358691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6718579885707877379826037 629866864285113504358691)
                    ·
                      rfl

theorem cell22_1839992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_1839992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1839992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1839992 prefixEnd_1839992 := by exact prefixLift 1839992
  have htrace : WordTrace (prefixWord ++ tailWord_1839992) baseStart_1839992 baseEnd_1839992 := by
    simpa [prefixWord, tailWord_1839992, baseEnd_1839992] using wordTrace_append hprefix tailTrace_1839992
  have hstable : (prefixWord ++ tailWord_1839992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839992).length < 2 ^ (prefixWord ++ tailWord_1839992).sum := by decide
  have hdescent : baseEnd_1839992 < baseStart_1839992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840041 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_1840041 : Nat := 118140960795 + 1840041 * 2 ^ 59
def prefixEnd_1840041 : Nat := 4983230072969 + 3 ^ 40 * 1840041 * 2
def baseEnd_1840041 : Nat := 629883637986493709883541

theorem tailTrace_1840041 : CollatzResearch.WordTrace tailWord_1840041 prefixEnd_1840041 629883637986493709883541 := by
  unfold tailWord_1840041
  simp only [CollatzResearch.WordTrace]
  refine ⟨67111808726853185828871977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44741205817902123885914651 67111808726853185828871977)
  ·
    refine ⟨50333856545139889371653983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67111808726853185828871977 50333856545139889371653983)
    ·
      refine ⟨75500784817709834057480975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50333856545139889371653983 75500784817709834057480975)
      ·
        refine ⟨113251177226564751086221463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75500784817709834057480975 113251177226564751086221463)
        ·
          refine ⟨169876765839847126629332195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113251177226564751086221463 169876765839847126629332195)
          ·
            refine ⟨254815148759770689943998293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169876765839847126629332195 254815148759770689943998293)
            ·
              refine ⟨1493057512264281386390615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 254815148759770689943998293 1493057512264281386390615)
              ·
                refine ⟨2239586268396422079585923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493057512264281386390615 2239586268396422079585923)
                ·
                  refine ⟨3359379402594633119378885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239586268396422079585923 3359379402594633119378885)
                  ·
                    refine ⟨629883637986493709883541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359379402594633119378885 629883637986493709883541)
                    ·
                      rfl

theorem cell22_1840041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_1840041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840041 prefixEnd_1840041 := by exact prefixLift 1840041
  have htrace : WordTrace (prefixWord ++ tailWord_1840041) baseStart_1840041 baseEnd_1840041 := by
    simpa [prefixWord, tailWord_1840041, baseEnd_1840041] using wordTrace_append hprefix tailTrace_1840041
  have hstable : (prefixWord ++ tailWord_1840041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840041).length < 2 ^ (prefixWord ++ tailWord_1840041).sum := by decide
  have hdescent : baseEnd_1840041 < baseStart_1840041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840056 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 4]
def baseStart_1840056 : Nat := 118140960795 + 1840056 * 2 ^ 59
def prefixEnd_1840056 : Nat := 4983230072969 + 3 ^ 40 * 1840056 * 2
def baseEnd_1840056 : Nat := 209962924264346223586165

theorem tailTrace_1840056 : CollatzResearch.WordTrace tailWord_1840056 prefixEnd_1840056 209962924264346223586165 := by
  unfold tailWord_1840056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33556177910899421695334011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44741570547865895593778681 33556177910899421695334011)
  ·
    refine ⟨50334266866349132543001017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33556177910899421695334011 50334266866349132543001017)
    ·
      refine ⟨37750700149761849407250763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50334266866349132543001017 37750700149761849407250763)
      ·
        refine ⟨56626050224642774110876145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750700149761849407250763 56626050224642774110876145)
        ·
          refine ⟨42469537668482080583157109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56626050224642774110876145 42469537668482080583157109)
          ·
            refine ⟨3981519156420195054670979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42469537668482080583157109 3981519156420195054670979)
            ·
              refine ⟨5972278734630292582006469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981519156420195054670979 5972278734630292582006469)
              ·
                refine ⟨1119802262743179859126213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5972278734630292582006469 1119802262743179859126213)
                ·
                  refine ⟨209962924264346223586165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119802262743179859126213 209962924264346223586165)
                  ·
                    rfl

theorem cell22_1840056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 4].length) (baseStart_1840056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840056 prefixEnd_1840056 := by exact prefixLift 1840056
  have htrace : WordTrace (prefixWord ++ tailWord_1840056) baseStart_1840056 baseEnd_1840056 := by
    simpa [prefixWord, tailWord_1840056, baseEnd_1840056] using wordTrace_append hprefix tailTrace_1840056
  have hstable : (prefixWord ++ tailWord_1840056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840056).length < 2 ^ (prefixWord ++ tailWord_1840056).sum := by decide
  have hdescent : baseEnd_1840056 < baseStart_1840056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840071 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1840071 : Nat := 118140960795 + 1840071 * 2 ^ 59
def prefixEnd_1840071 : Nat := 4983230072969 + 3 ^ 40 * 1840071 * 2
def baseEnd_1840071 : Nat := 629893907599583631633449

theorem tailTrace_1840071 : CollatzResearch.WordTrace tailWord_1840071 prefixEnd_1840071 629893907599583631633449 := by
  unfold tailWord_1840071
  simp only [CollatzResearch.WordTrace]
  refine ⟨67112902916744500952464067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44741935277829667301642711 67112902916744500952464067)
  ·
    refine ⟨100669354375116751428696101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67112902916744500952464067 100669354375116751428696101)
    ·
      refine ⟨18875503945334390892880519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100669354375116751428696101 18875503945334390892880519)
      ·
        refine ⟨28313255918001586339320779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18875503945334390892880519 28313255918001586339320779)
        ·
          refine ⟨42469883877002379508981169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28313255918001586339320779 42469883877002379508981169)
          ·
            refine ⟨31852412907751784631735877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42469883877002379508981169 31852412907751784631735877)
            ·
              refine ⟨5972327420203459618450477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31852412907751784631735877 5972327420203459618450477)
              ·
                refine ⟨2239622782576297356918929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5972327420203459618450477 2239622782576297356918929)
                ·
                  refine ⟨1679717086932223017689197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239622782576297356918929 1679717086932223017689197)
                  ·
                    refine ⟨629893907599583631633449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679717086932223017689197 629893907599583631633449)
                    ·
                      rfl

theorem cell22_1840071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1840071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840071 prefixEnd_1840071 := by exact prefixLift 1840071
  have htrace : WordTrace (prefixWord ++ tailWord_1840071) baseStart_1840071 baseEnd_1840071 := by
    simpa [prefixWord, tailWord_1840071, baseEnd_1840071] using wordTrace_append hprefix tailTrace_1840071
  have hstable : (prefixWord ++ tailWord_1840071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840071).length < 2 ^ (prefixWord ++ tailWord_1840071).sum := by decide
  have hdescent : baseEnd_1840071 < baseStart_1840071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840101 : List Nat := [1, 3, 1, 6, 1, 1, 9]
def baseStart_1840101 : Nat := 118140960795 + 1840101 * 2 ^ 59
def prefixEnd_1840101 : Nat := 4983230072969 + 3 ^ 40 * 1840101 * 2
def baseEnd_1840101 : Nat := 23329784341210131606791

theorem tailTrace_1840101 : CollatzResearch.WordTrace tailWord_1840101 prefixEnd_1840101 23329784341210131606791 := by
  unfold tailWord_1840101
  simp only [CollatzResearch.WordTrace]
  refine ⟨67113997106635816076056157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44742664737757210717370771 67113997106635816076056157)
  ·
    refine ⟨25167748914988431028521059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67113997106635816076056157 25167748914988431028521059)
    ·
      refine ⟨37751623372482646542781589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167748914988431028521059 37751623372482646542781589)
      ·
        refine ⟨1769607345585124056692887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37751623372482646542781589 1769607345585124056692887)
        ·
          refine ⟨2654411018377686085039331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769607345585124056692887 2654411018377686085039331)
          ·
            refine ⟨3981616527566529127558997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654411018377686085039331 3981616527566529127558997)
            ·
              refine ⟨23329784341210131606791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3981616527566529127558997 23329784341210131606791)
              ·
                rfl

theorem cell22_1840101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 9].length) (baseStart_1840101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840101 prefixEnd_1840101 := by exact prefixLift 1840101
  have htrace : WordTrace (prefixWord ++ tailWord_1840101) baseStart_1840101 baseEnd_1840101 := by
    simpa [prefixWord, tailWord_1840101, baseEnd_1840101] using wordTrace_append hprefix tailTrace_1840101
  have hstable : (prefixWord ++ tailWord_1840101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840101).length < 2 ^ (prefixWord ++ tailWord_1840101).sum := by decide
  have hdescent : baseEnd_1840101 < baseStart_1840101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840180 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1840180 : Nat := 118140960795 + 1840180 * 2 ^ 59
def prefixEnd_1840180 : Nat := 4983230072969 + 3 ^ 40 * 1840180 * 2
def baseEnd_1840180 : Nat := 209977073509047893552705

theorem tailTrace_1840180 : CollatzResearch.WordTrace tailWord_1840180 prefixEnd_1840180 209977073509047893552705 := by
  unfold tailWord_1840180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33558439236674806284090997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44744585648899741712121329 33558439236674806284090997)
  ·
    refine ⟨3146103678438263089133531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33558439236674806284090997 3146103678438263089133531)
    ·
      refine ⟨4719155517657394633700297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3146103678438263089133531 4719155517657394633700297)
      ·
        refine ⟨3539366638243045975275223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719155517657394633700297 3539366638243045975275223)
        ·
          refine ⟨5309049957364568962912835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539366638243045975275223 5309049957364568962912835)
          ·
            refine ⟨7963574936046853444369253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309049957364568962912835 7963574936046853444369253)
            ·
              refine ⟨1493170300508785020819235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7963574936046853444369253 1493170300508785020819235)
              ·
                refine ⟨2239755450763177531228853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493170300508785020819235 2239755450763177531228853)
                ·
                  refine ⟨209977073509047893552705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239755450763177531228853 209977073509047893552705)
                  ·
                    rfl

theorem cell22_1840180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1840180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840180 prefixEnd_1840180 := by exact prefixLift 1840180
  have htrace : WordTrace (prefixWord ++ tailWord_1840180) baseStart_1840180 baseEnd_1840180 := by
    simpa [prefixWord, tailWord_1840180, baseEnd_1840180] using wordTrace_append hprefix tailTrace_1840180
  have hstable : (prefixWord ++ tailWord_1840180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840180).length < 2 ^ (prefixWord ++ tailWord_1840180).sum := by decide
  have hdescent : baseEnd_1840180 < baseStart_1840180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840193 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1840193 : Nat := 118140960795 + 1840193 * 2 ^ 59
def prefixEnd_1840193 : Nat := 4983230072969 + 3 ^ 40 * 1840193 * 2
def baseEnd_1840193 : Nat := 629935670692815980083075

theorem tailTrace_1840193 : CollatzResearch.WordTrace tailWord_1840193 prefixEnd_1840193 629935670692815980083075 := by
  unfold tailWord_1840193
  simp only [CollatzResearch.WordTrace]
  refine ⟨67117352622302515788405233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44744901748201677192270155 67117352622302515788405233)
  ·
    refine ⟨50338014466726886841303925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67117352622302515788405233 50338014466726886841303925)
    ·
      refine ⟨4719188856255645641372243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50338014466726886841303925 4719188856255645641372243)
      ·
        refine ⟨7078783284383468462058365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719188856255645641372243 7078783284383468462058365)
        ·
          refine ⟨2654543731643800673271887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7078783284383468462058365 2654543731643800673271887)
          ·
            refine ⟨3981815597465701009907831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654543731643800673271887 3981815597465701009907831)
            ·
              refine ⟨5972723396198551514861747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981815597465701009907831 5972723396198551514861747)
              ·
                refine ⟨8959085094297827272292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972723396198551514861747 8959085094297827272292621)
                ·
                  refine ⟨3359656910361685227109733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8959085094297827272292621 3359656910361685227109733)
                  ·
                    refine ⟨629935670692815980083075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359656910361685227109733 629935670692815980083075)
                    ·
                      rfl

theorem cell22_1840193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1840193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840193 prefixEnd_1840193 := by exact prefixLift 1840193
  have htrace : WordTrace (prefixWord ++ tailWord_1840193) baseStart_1840193 baseEnd_1840193 := by
    simpa [prefixWord, tailWord_1840193, baseEnd_1840193] using wordTrace_append hprefix tailTrace_1840193
  have hstable : (prefixWord ++ tailWord_1840193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840193).length < 2 ^ (prefixWord ++ tailWord_1840193).sum := by decide
  have hdescent : baseEnd_1840193 < baseStart_1840193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840206 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1840206 : Nat := 118140960795 + 1840206 * 2 ^ 59
def prefixEnd_1840206 : Nat := 4983230072969 + 3 ^ 40 * 1840206 * 2
def baseEnd_1840206 : Nat := 629940120858488279508035

theorem tailTrace_1840206 : CollatzResearch.WordTrace tailWord_1840206 prefixEnd_1840206 629940120858488279508035 := by
  unfold tailWord_1840206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389728346406927376078559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44745217847503612672418981 8389728346406927376078559)
  ·
    refine ⟨12584592519610391064117839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8389728346406927376078559 12584592519610391064117839)
    ·
      refine ⟨18876888779415586596176759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12584592519610391064117839 18876888779415586596176759)
      ·
        refine ⟨28315333169123379894265139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18876888779415586596176759 28315333169123379894265139)
        ·
          refine ⟨42472999753685069841397709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315333169123379894265139 42472999753685069841397709)
          ·
            refine ⟨15927374907631901190524141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42472999753685069841397709 15927374907631901190524141)
            ·
              refine ⟨5972765590361962946446553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15927374907631901190524141 5972765590361962946446553)
              ·
                refine ⟨4479574192771472209834915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5972765590361962946446553 4479574192771472209834915)
                ·
                  refine ⟨6719361289157208314752373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479574192771472209834915 6719361289157208314752373)
                  ·
                    refine ⟨629940120858488279508035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6719361289157208314752373 629940120858488279508035)
                    ·
                      rfl

theorem cell22_1840206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1840206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840206 prefixEnd_1840206 := by exact prefixLift 1840206
  have htrace : WordTrace (prefixWord ++ tailWord_1840206) baseStart_1840206 baseEnd_1840206 := by
    simpa [prefixWord, tailWord_1840206, baseEnd_1840206] using wordTrace_append hprefix tailTrace_1840206
  have hstable : (prefixWord ++ tailWord_1840206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840206).length < 2 ^ (prefixWord ++ tailWord_1840206).sum := by decide
  have hdescent : baseEnd_1840206 < baseStart_1840206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840210 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1840210 : Nat := 118140960795 + 1840210 * 2 ^ 59
def prefixEnd_1840210 : Nat := 4983230072969 + 3 ^ 40 * 1840210 * 2
def baseEnd_1840210 : Nat := 629941490140233602408023

theorem tailTrace_1840210 : CollatzResearch.WordTrace tailWord_1840210 prefixEnd_1840210 629941490140233602408023 := by
  unfold tailWord_1840210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779493165810231922943521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44745315108827285127849389 16779493165810231922943521)
  ·
    refine ⟨12584619874357673942207641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16779493165810231922943521 12584619874357673942207641)
    ·
      refine ⟨9438464905768255456655731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12584619874357673942207641 9438464905768255456655731)
      ·
        refine ⟨14157697358652383184983597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438464905768255456655731 14157697358652383184983597)
        ·
          refine ⟨5309136509494643694368849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14157697358652383184983597 5309136509494643694368849)
          ·
            refine ⟨3981852382120982770776637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309136509494643694368849 3981852382120982770776637)
            ·
              refine ⟨1493194643295368539041239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3981852382120982770776637 1493194643295368539041239)
              ·
                refine ⟨2239791964943052808561859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493194643295368539041239 2239791964943052808561859)
                ·
                  refine ⟨3359687947414579212842789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239791964943052808561859 3359687947414579212842789)
                  ·
                    refine ⟨629941490140233602408023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359687947414579212842789 629941490140233602408023)
                    ·
                      rfl

theorem cell22_1840210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1840210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840210 prefixEnd_1840210 := by exact prefixLift 1840210
  have htrace : WordTrace (prefixWord ++ tailWord_1840210) baseStart_1840210 baseEnd_1840210 := by
    simpa [prefixWord, tailWord_1840210, baseEnd_1840210] using wordTrace_append hprefix tailTrace_1840210
  have hstable : (prefixWord ++ tailWord_1840210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840210).length < 2 ^ (prefixWord ++ tailWord_1840210).sum := by decide
  have hdescent : baseEnd_1840210 < baseStart_1840210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840223 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 2, 3]
def baseStart_1840223 : Nat := 118140960795 + 1840223 * 2 ^ 59
def prefixEnd_1840223 : Nat := 4983230072969 + 3 ^ 40 * 1840223 * 2
def baseEnd_1840223 : Nat := 629945940305905901832983

theorem tailTrace_1840223 : CollatzResearch.WordTrace tailWord_1840223 prefixEnd_1840223 629945940305905901832983 := by
  unfold tailWord_1840223
  simp only [CollatzResearch.WordTrace]
  refine ⟨67118446812193830911997323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44745631208129220607998215 67118446812193830911997323)
  ·
    refine ⟨100677670218290746367995985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67118446812193830911997323 100677670218290746367995985)
    ·
      refine ⟨75508252663718059775996989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100677670218290746367995985 75508252663718059775996989)
      ·
        refine ⟨28315594748894272415998871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75508252663718059775996989 28315594748894272415998871)
        ·
          refine ⟨42473392123341408623998307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28315594748894272415998871 42473392123341408623998307)
          ·
            refine ⟨63710088185012112935997461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42473392123341408623998307 63710088185012112935997461)
            ·
              refine ⟨2986410383672442793874881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63710088185012112935997461 2986410383672442793874881)
              ·
                refine ⟨2239807787754332095406161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986410383672442793874881 2239807787754332095406161)
                ·
                  refine ⟨1679855840815749071554621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239807787754332095406161 1679855840815749071554621)
                  ·
                    refine ⟨629945940305905901832983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679855840815749071554621 629945940305905901832983)
                    ·
                      rfl

theorem cell22_1840223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_1840223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840223 prefixEnd_1840223 := by exact prefixLift 1840223
  have htrace : WordTrace (prefixWord ++ tailWord_1840223) baseStart_1840223 baseEnd_1840223 := by
    simpa [prefixWord, tailWord_1840223, baseEnd_1840223] using wordTrace_append hprefix tailTrace_1840223
  have hstable : (prefixWord ++ tailWord_1840223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840223).length < 2 ^ (prefixWord ++ tailWord_1840223).sum := by decide
  have hdescent : baseEnd_1840223 < baseStart_1840223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840285 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1840285 : Nat := 118140960795 + 1840285 * 2 ^ 59
def prefixEnd_1840285 : Nat := 4983230072969 + 3 ^ 40 * 1840285 * 2
def baseEnd_1840285 : Nat := 629967164172958406782793

theorem tailTrace_1840285 : CollatzResearch.WordTrace tailWord_1840285 prefixEnd_1840285 629967164172958406782793 := by
  unfold tailWord_1840285
  simp only [CollatzResearch.WordTrace]
  refine ⟨67120708137969215500754309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44747138758646143667169539 67120708137969215500754309)
  ·
    refine ⟨12585132775869227906391433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67120708137969215500754309 12585132775869227906391433)
    ·
      refine ⟨9438849581901920929793575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12585132775869227906391433 9438849581901920929793575)
      ·
        refine ⟨14158274372852881394690363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438849581901920929793575 14158274372852881394690363)
        ·
          refine ⟨21237411559279322092035545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14158274372852881394690363 21237411559279322092035545)
          ·
            refine ⟨15928058669459491569026659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21237411559279322092035545 15928058669459491569026659)
            ·
              refine ⟨23892088004189237353539989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15928058669459491569026659 23892088004189237353539989)
              ·
                refine ⟨1119941625196370500947187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23892088004189237353539989 1119941625196370500947187)
                ·
                  refine ⟨1679912437794555751420781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119941625196370500947187 1679912437794555751420781)
                  ·
                    refine ⟨629967164172958406782793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679912437794555751420781 629967164172958406782793)
                    ·
                      rfl

theorem cell22_1840285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1840285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840285 prefixEnd_1840285 := by exact prefixLift 1840285
  have htrace : WordTrace (prefixWord ++ tailWord_1840285) baseStart_1840285 baseEnd_1840285 := by
    simpa [prefixWord, tailWord_1840285, baseEnd_1840285] using wordTrace_append hprefix tailTrace_1840285
  have hstable : (prefixWord ++ tailWord_1840285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840285).length < 2 ^ (prefixWord ++ tailWord_1840285).sum := by decide
  have hdescent : baseEnd_1840285 < baseStart_1840285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840328 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 1, 4]
def baseStart_1840328 : Nat := 118140960795 + 1840328 * 2 ^ 59
def prefixEnd_1840328 : Nat := 4983230072969 + 3 ^ 40 * 1840328 * 2
def baseEnd_1840328 : Nat := 629981883951720627957661

theorem tailTrace_1840328 : CollatzResearch.WordTrace tailWord_1840328 prefixEnd_1840328 629981883951720627957661 := by
  unfold tailWord_1840328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33561138238406716922284819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44748184317875622563046425 33561138238406716922284819)
  ·
    refine ⟨50341707357610075383427229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33561138238406716922284819 50341707357610075383427229)
    ·
      refine ⟨18878140259103778268785211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50341707357610075383427229 18878140259103778268785211)
      ·
        refine ⟨28317210388655667403177817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878140259103778268785211 28317210388655667403177817)
        ·
          refine ⟨21237907791491750552383363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28317210388655667403177817 21237907791491750552383363)
          ·
            refine ⟨31856861687237625828575045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21237907791491750552383363 31856861687237625828575045)
            ·
              refine ⟨5973161566357054842857821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31856861687237625828575045 5973161566357054842857821)
              ·
                refine ⟨2239935587383895566071683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5973161566357054842857821 2239935587383895566071683)
                ·
                  refine ⟨3359903381075843349107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239935587383895566071683 3359903381075843349107525)
                  ·
                    refine ⟨629981883951720627957661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359903381075843349107525 629981883951720627957661)
                    ·
                      rfl

theorem cell22_1840328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_1840328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840328 prefixEnd_1840328 := by exact prefixLift 1840328
  have htrace : WordTrace (prefixWord ++ tailWord_1840328) baseStart_1840328 baseEnd_1840328 := by
    simpa [prefixWord, tailWord_1840328, baseEnd_1840328] using wordTrace_append hprefix tailTrace_1840328
  have hstable : (prefixWord ++ tailWord_1840328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840328).length < 2 ^ (prefixWord ++ tailWord_1840328).sum := by decide
  have hdescent : baseEnd_1840328 < baseStart_1840328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840343 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 4]
def baseStart_1840343 : Nat := 118140960795 + 1840343 * 2 ^ 59
def prefixEnd_1840343 : Nat := 4983230072969 + 3 ^ 40 * 1840343 * 2
def baseEnd_1840343 : Nat := 209995672919421862944205

theorem tailTrace_1840343 : CollatzResearch.WordTrace tailWord_1840343 prefixEnd_1840343 209995672919421862944205 := by
  unfold tailWord_1840343
  simp only [CollatzResearch.WordTrace]
  refine ⟨67122823571759091406365683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44748549047839394270910455 67122823571759091406365683)
  ·
    refine ⟨100684235357638637109548525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67122823571759091406365683 100684235357638637109548525)
    ·
      refine ⟨37756588259114488916080697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100684235357638637109548525 37756588259114488916080697)
      ·
        refine ⟨28317441194335866687060523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37756588259114488916080697 28317441194335866687060523)
        ·
          refine ⟨42476161791503800030590785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28317441194335866687060523 42476161791503800030590785)
          ·
            refine ⟨31857121343627850022943089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42476161791503800030590785 31857121343627850022943089)
            ·
              refine ⟨23892841007720887517207317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31857121343627850022943089 23892841007720887517207317)
              ·
                refine ⟨1119976922236916602369093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23892841007720887517207317 1119976922236916602369093)
                ·
                  refine ⟨209995672919421862944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1119976922236916602369093 209995672919421862944205)
                  ·
                    rfl

theorem cell22_1840343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 4].length) (baseStart_1840343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840343 prefixEnd_1840343 := by exact prefixLift 1840343
  have htrace : WordTrace (prefixWord ++ tailWord_1840343) baseStart_1840343 baseEnd_1840343 := by
    simpa [prefixWord, tailWord_1840343, baseEnd_1840343] using wordTrace_append hprefix tailTrace_1840343
  have hstable : (prefixWord ++ tailWord_1840343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840343).length < 2 ^ (prefixWord ++ tailWord_1840343).sum := by decide
  have hdescent : baseEnd_1840343 < baseStart_1840343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840349 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 5]
def baseStart_1840349 : Nat := 118140960795 + 1840349 * 2 ^ 59
def prefixEnd_1840349 : Nat := 4983230072969 + 3 ^ 40 * 1840349 * 2
def baseEnd_1840349 : Nat := 209996357560294524394199

theorem tailTrace_1840349 : CollatzResearch.WordTrace tailWord_1840349 prefixEnd_1840349 209996357560294524394199 := by
  unfold tailWord_1840349
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123042409737354431084101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44748694939824902954056067 67123042409737354431084101)
  ·
    refine ⟨12585570451825753955828269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67123042409737354431084101 12585570451825753955828269)
    ·
      refine ⟨4719588919434657733435601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12585570451825753955828269 4719588919434657733435601)
      ·
        refine ⟨3539691689575993300076701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719588919434657733435601 3539691689575993300076701)
        ·
          refine ⟨1327384383590997487528763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3539691689575993300076701 1327384383590997487528763)
          ·
            refine ⟨1991076575386496231293145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327384383590997487528763 1991076575386496231293145)
            ·
              refine ⟨1493307431539872173469859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991076575386496231293145 1493307431539872173469859)
              ·
                refine ⟨2239961147309808260204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493307431539872173469859 2239961147309808260204789)
                ·
                  refine ⟨209996357560294524394199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239961147309808260204789 209996357560294524394199)
                  ·
                    rfl

theorem cell22_1840349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_1840349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840349 prefixEnd_1840349 := by exact prefixLift 1840349
  have htrace : WordTrace (prefixWord ++ tailWord_1840349) baseStart_1840349 baseEnd_1840349 := by
    simpa [prefixWord, tailWord_1840349, baseEnd_1840349] using wordTrace_append hprefix tailTrace_1840349
  have hstable : (prefixWord ++ tailWord_1840349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840349).length < 2 ^ (prefixWord ++ tailWord_1840349).sum := by decide
  have hdescent : baseEnd_1840349 < baseStart_1840349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840356 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1840356 : Nat := 118140960795 + 1840356 * 2 ^ 59
def prefixEnd_1840356 : Nat := 4983230072969 + 3 ^ 40 * 1840356 * 2
def baseEnd_1840356 : Nat := 629991468923937888257575

theorem tailTrace_1840356 : CollatzResearch.WordTrace tailWord_1840356 prefixEnd_1840356 629991468923937888257575 := by
  unfold tailWord_1840356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33561648860355997313294461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44748865147141329751059281 33561648860355997313294461)
  ·
    refine ⟨12585618322633498992485423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33561648860355997313294461 12585618322633498992485423)
    ·
      refine ⟨18878427483950248488728135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12585618322633498992485423 18878427483950248488728135)
      ·
        refine ⟨28317641225925372733092203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878427483950248488728135 28317641225925372733092203)
        ·
          refine ⟨42476461838888059099638305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28317641225925372733092203 42476461838888059099638305)
          ·
            refine ⟨31857346379166044324728729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42476461838888059099638305 31857346379166044324728729)
            ·
              refine ⟨23893009784374533243546547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31857346379166044324728729 23893009784374533243546547)
              ·
                refine ⟨35839514676561799865319821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23893009784374533243546547 35839514676561799865319821)
                ·
                  refine ⟨13439818003710674949494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35839514676561799865319821 13439818003710674949494933)
                  ·
                    refine ⟨629991468923937888257575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13439818003710674949494933 629991468923937888257575)
                    ·
                      rfl

theorem cell22_1840356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1840356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840356 prefixEnd_1840356 := by exact prefixLift 1840356
  have htrace : WordTrace (prefixWord ++ tailWord_1840356) baseStart_1840356 baseEnd_1840356 := by
    simpa [prefixWord, tailWord_1840356, baseEnd_1840356] using wordTrace_append hprefix tailTrace_1840356
  have hstable : (prefixWord ++ tailWord_1840356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840356).length < 2 ^ (prefixWord ++ tailWord_1840356).sum := by decide
  have hdescent : baseEnd_1840356 < baseStart_1840356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840371 : List Nat := [1, 1, 1, 2, 2, 5, 2, 8]
def baseStart_1840371 : Nat := 118140960795 + 1840371 * 2 ^ 59
def prefixEnd_1840371 : Nat := 4983230072969 + 3 ^ 40 * 1840371 * 2
def baseEnd_1840371 : Nat := 69999622636720316570281

theorem tailTrace_1840371 : CollatzResearch.WordTrace tailWord_1840371 prefixEnd_1840371 69999622636720316570281 := by
  unfold tailWord_1840371
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123844815657652188384967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44749229877105101458923311 67123844815657652188384967)
  ·
    refine ⟨100685767223486478282577451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67123844815657652188384967 100685767223486478282577451)
    ·
      refine ⟨151028650835229717423866177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100685767223486478282577451 151028650835229717423866177)
      ·
        refine ⟨113271488126422288067899633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151028650835229717423866177 113271488126422288067899633)
        ·
          refine ⟨84953616094816716050924725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113271488126422288067899633 84953616094816716050924725)
          ·
            refine ⟨7964401508889067129774193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84953616094816716050924725 7964401508889067129774193)
            ·
              refine ⟨5973301131666800347330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964401508889067129774193 5973301131666800347330645)
              ·
                refine ⟨69999622636720316570281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5973301131666800347330645 69999622636720316570281)
                ·
                  rfl

theorem cell22_1840371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_1840371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840371 prefixEnd_1840371 := by exact prefixLift 1840371
  have htrace : WordTrace (prefixWord ++ tailWord_1840371) baseStart_1840371 baseEnd_1840371 := by
    simpa [prefixWord, tailWord_1840371, baseEnd_1840371] using wordTrace_append hprefix tailTrace_1840371
  have hstable : (prefixWord ++ tailWord_1840371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840371).length < 2 ^ (prefixWord ++ tailWord_1840371).sum := by decide
  have hdescent : baseEnd_1840371 < baseStart_1840371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840392 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 2, 3]
def baseStart_1840392 : Nat := 118140960795 + 1840392 * 2 ^ 59
def prefixEnd_1840392 : Nat := 4983230072969 + 3 ^ 40 * 1840392 * 2
def baseEnd_1840392 : Nat := 630003792459645794357465

theorem tailTrace_1840392 : CollatzResearch.WordTrace tailWord_1840392 prefixEnd_1840392 630003792459645794357465 := by
  unfold tailWord_1840392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33562305374290786387449715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44749740499054381849932953 33562305374290786387449715)
  ·
    refine ⟨50343458061436179581174573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33562305374290786387449715 50343458061436179581174573)
    ·
      refine ⟨18878796773038567342940465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50343458061436179581174573 18878796773038567342940465)
      ·
        refine ⟨14159097579778925507205349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18878796773038567342940465 14159097579778925507205349)
        ·
          refine ⟨2654830796208548532601003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14159097579778925507205349 2654830796208548532601003)
          ·
            refine ⟨3982246194312822798901505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654830796208548532601003 3982246194312822798901505)
            ·
              refine ⟨2986684645734617099176129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982246194312822798901505 2986684645734617099176129)
              ·
                refine ⟨2240013484300962824382097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986684645734617099176129 2240013484300962824382097)
                ·
                  refine ⟨1680010113225722118286573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2240013484300962824382097 1680010113225722118286573)
                  ·
                    refine ⟨630003792459645794357465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680010113225722118286573 630003792459645794357465)
                    ·
                      rfl

theorem cell22_1840392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_1840392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840392 prefixEnd_1840392 := by exact prefixLift 1840392
  have htrace : WordTrace (prefixWord ++ tailWord_1840392) baseStart_1840392 baseEnd_1840392 := by
    simpa [prefixWord, tailWord_1840392, baseEnd_1840392] using wordTrace_append hprefix tailTrace_1840392
  have hstable : (prefixWord ++ tailWord_1840392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840392).length < 2 ^ (prefixWord ++ tailWord_1840392).sum := by decide
  have hdescent : baseEnd_1840392 < baseStart_1840392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840401 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_1840401 : Nat := 118140960795 + 1840401 * 2 ^ 59
def prefixEnd_1840401 : Nat := 4983230072969 + 3 ^ 40 * 1840401 * 2
def baseEnd_1840401 : Nat := 630006873343572770882437

theorem tailTrace_1840401 : CollatzResearch.WordTrace tailWord_1840401 prefixEnd_1840401 630006873343572770882437 := by
  unfold tailWord_1840401
  simp only [CollatzResearch.WordTrace]
  refine ⟨67124939005548967311977057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44749959337032644874651371 67124939005548967311977057)
  ·
    refine ⟨50343704254161725483982793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67124939005548967311977057 50343704254161725483982793)
    ·
      refine ⟨37757778190621294112987095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50343704254161725483982793 37757778190621294112987095)
      ·
        refine ⟨56636667285931941169480643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37757778190621294112987095 56636667285931941169480643)
        ·
          refine ⟨84955000928897911754220965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56636667285931941169480643 84955000928897911754220965)
          ·
            refine ⟨15929062674168358453916431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84955000928897911754220965 15929062674168358453916431)
            ·
              refine ⟨23893594011252537680874647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929062674168358453916431 23893594011252537680874647)
              ·
                refine ⟨35840391016878806521311971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23893594011252537680874647 35840391016878806521311971)
                ·
                  refine ⟨53760586525318209781967957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35840391016878806521311971 53760586525318209781967957)
                  ·
                    refine ⟨630006873343572770882437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53760586525318209781967957 630006873343572770882437)
                    ·
                      rfl

theorem cell22_1840401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_1840401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840401 prefixEnd_1840401 := by exact prefixLift 1840401
  have htrace : WordTrace (prefixWord ++ tailWord_1840401) baseStart_1840401 baseEnd_1840401 := by
    simpa [prefixWord, tailWord_1840401, baseEnd_1840401] using wordTrace_append hprefix tailTrace_1840401
  have hstable : (prefixWord ++ tailWord_1840401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840401).length < 2 ^ (prefixWord ++ tailWord_1840401).sum := by decide
  have hdescent : baseEnd_1840401 < baseStart_1840401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840420 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_1840420 : Nat := 118140960795 + 1840420 * 2 ^ 59
def prefixEnd_1840420 : Nat := 4983230072969 + 3 ^ 40 * 1840420 * 2
def baseEnd_1840420 : Nat := 630013377431863054657379

theorem tailTrace_1840420 : CollatzResearch.WordTrace tailWord_1840420 prefixEnd_1840420 630013377431863054657379 := by
  unfold tailWord_1840420
  simp only [CollatzResearch.WordTrace]
  refine ⟨33562815996240066778459357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44750421328320089037945809 33562815996240066778459357)
  ·
    refine ⟨12586055998590025041922259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33562815996240066778459357 12586055998590025041922259)
    ·
      refine ⟨18879083997885037562883389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586055998590025041922259 18879083997885037562883389)
      ·
        refine ⟨7079656499206889086081271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18879083997885037562883389 7079656499206889086081271)
        ·
          refine ⟨10619484748810333629121907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7079656499206889086081271 10619484748810333629121907)
          ·
            refine ⟨15929227123215500443682861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10619484748810333629121907 15929227123215500443682861)
            ·
              refine ⟨5973460171205812666381073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15929227123215500443682861 5973460171205812666381073)
              ·
                refine ⟨4480095128404359499785805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973460171205812666381073 4480095128404359499785805)
                ·
                  refine ⟨1680035673151634812419677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4480095128404359499785805 1680035673151634812419677)
                  ·
                    refine ⟨630013377431863054657379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680035673151634812419677 630013377431863054657379)
                    ·
                      rfl

theorem cell22_1840420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_1840420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840420 prefixEnd_1840420 := by exact prefixLift 1840420
  have htrace : WordTrace (prefixWord ++ tailWord_1840420) baseStart_1840420 baseEnd_1840420 := by
    simpa [prefixWord, tailWord_1840420, baseEnd_1840420] using wordTrace_append hprefix tailTrace_1840420
  have hstable : (prefixWord ++ tailWord_1840420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840420).length < 2 ^ (prefixWord ++ tailWord_1840420).sum := by decide
  have hdescent : baseEnd_1840420 < baseStart_1840420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840431 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_1840431 : Nat := 118140960795 + 1840431 * 2 ^ 59
def prefixEnd_1840431 : Nat := 4983230072969 + 3 ^ 40 * 1840431 * 2
def baseEnd_1840431 : Nat := 630017142956662692632345

theorem tailTrace_1840431 : CollatzResearch.WordTrace tailWord_1840431 prefixEnd_1840431 630017142956662692632345 := by
  unfold tailWord_1840431
  simp only [CollatzResearch.WordTrace]
  refine ⟨67126033195440282435569147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44750688796960188290379431 67126033195440282435569147)
  ·
    refine ⟨100689049793160423653353721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67126033195440282435569147 100689049793160423653353721)
    ·
      refine ⟨75516787344870317740015291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100689049793160423653353721 75516787344870317740015291)
      ·
        refine ⟨113275181017305476610022937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75516787344870317740015291 113275181017305476610022937)
        ·
          refine ⟨84956385762979107457517203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113275181017305476610022937 84956385762979107457517203)
          ·
            refine ⟨127434578644468661186275805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84956385762979107457517203 127434578644468661186275805)
            ·
              refine ⟨47787966991675747944853427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127434578644468661186275805 47787966991675747944853427)
              ·
                refine ⟨71681950487513621917280141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47787966991675747944853427 71681950487513621917280141)
                ·
                  refine ⟨26880731432817608218980053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71681950487513621917280141 26880731432817608218980053)
                  ·
                    refine ⟨630017142956662692632345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26880731432817608218980053 630017142956662692632345)
                    ·
                      rfl

theorem cell22_1840431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_1840431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840431 prefixEnd_1840431 := by exact prefixLift 1840431
  have htrace : WordTrace (prefixWord ++ tailWord_1840431) baseStart_1840431 baseEnd_1840431 := by
    simpa [prefixWord, tailWord_1840431, baseEnd_1840431] using wordTrace_append hprefix tailTrace_1840431
  have hstable : (prefixWord ++ tailWord_1840431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840431).length < 2 ^ (prefixWord ++ tailWord_1840431).sum := by decide
  have hdescent : baseEnd_1840431 < baseStart_1840431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840437 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1840437 : Nat := 118140960795 + 1840437 * 2 ^ 59
def prefixEnd_1840437 : Nat := 4983230072969 + 3 ^ 40 * 1840437 * 2
def baseEnd_1840437 : Nat := 630019196879280676982327

theorem tailTrace_1840437 : CollatzResearch.WordTrace tailWord_1840437 prefixEnd_1840437 630019196879280676982327 := by
  unfold tailWord_1840437
  simp only [CollatzResearch.WordTrace]
  refine ⟨67126252033418545460287565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44750834688945696973525043 67126252033418545460287565)
  ·
    refine ⟨25172344512531954547607837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67126252033418545460287565 25172344512531954547607837)
    ·
      refine ⟨9439629192199482955352939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25172344512531954547607837 9439629192199482955352939)
      ·
        refine ⟨14159443788299224433029409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9439629192199482955352939 14159443788299224433029409)
        ·
          refine ⟨10619582841224418324772057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14159443788299224433029409 10619582841224418324772057)
          ·
            refine ⟨7964687130918313743579043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10619582841224418324772057 7964687130918313743579043)
            ·
              refine ⟨11947030696377470615368565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964687130918313743579043 11947030696377470615368565)
              ·
                refine ⟨1120034127785387870190803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11947030696377470615368565 1120034127785387870190803)
                ·
                  refine ⟨1680051191678081805286205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120034127785387870190803 1680051191678081805286205)
                  ·
                    refine ⟨630019196879280676982327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680051191678081805286205 630019196879280676982327)
                    ·
                      rfl

theorem cell22_1840437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1840437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840437 prefixEnd_1840437 := by exact prefixLift 1840437
  have htrace : WordTrace (prefixWord ++ tailWord_1840437) baseStart_1840437 baseEnd_1840437 := by
    simpa [prefixWord, tailWord_1840437, baseEnd_1840437] using wordTrace_append hprefix tailTrace_1840437
  have hstable : (prefixWord ++ tailWord_1840437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840437).length < 2 ^ (prefixWord ++ tailWord_1840437).sum := by decide
  have hdescent : baseEnd_1840437 < baseStart_1840437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840480 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_1840480 : Nat := 118140960795 + 1840480 * 2 ^ 59
def prefixEnd_1840480 : Nat := 4983230072969 + 3 ^ 40 * 1840480 * 2
def baseEnd_1840480 : Nat := 630033916658042898157195

theorem tailTrace_1840480 : CollatzResearch.WordTrace tailWord_1840480 prefixEnd_1840480 630033916658042898157195 := by
  unfold tailWord_1840480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563910186131381902051447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44751880248175175869401929 33563910186131381902051447)
  ·
    refine ⟨50345865279197072853077171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33563910186131381902051447 50345865279197072853077171)
    ·
      refine ⟨75518797918795609279615757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50345865279197072853077171 75518797918795609279615757)
      ·
        refine ⟨28319549219548353479855909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75518797918795609279615757 28319549219548353479855909)
        ·
          refine ⟨5309915478665316277472983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28319549219548353479855909 5309915478665316277472983)
          ·
            refine ⟨7964873217997974416209475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309915478665316277472983 7964873217997974416209475)
            ·
              refine ⟨11947309826996961624314213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964873217997974416209475 11947309826996961624314213)
              ·
                refine ⟨2240120592561930304558915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11947309826996961624314213 2240120592561930304558915)
                ·
                  refine ⟨3360180888842895456838373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240120592561930304558915 3360180888842895456838373)
                  ·
                    refine ⟨630033916658042898157195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360180888842895456838373 630033916658042898157195)
                    ·
                      rfl

theorem cell22_1840480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_1840480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840480 prefixEnd_1840480 := by exact prefixLift 1840480
  have htrace : WordTrace (prefixWord ++ tailWord_1840480) baseStart_1840480 baseEnd_1840480 := by
    simpa [prefixWord, tailWord_1840480, baseEnd_1840480] using wordTrace_append hprefix tailTrace_1840480
  have hstable : (prefixWord ++ tailWord_1840480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840480).length < 2 ^ (prefixWord ++ tailWord_1840480).sum := by decide
  have hdescent : baseEnd_1840480 < baseStart_1840480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840523 : List Nat := [1, 1, 1, 1, 4, 3, 4, 7]
def baseStart_1840523 : Nat := 118140960795 + 1840523 * 2 ^ 59
def prefixEnd_1840523 : Nat := 4983230072969 + 3 ^ 40 * 1840523 * 2
def baseEnd_1840523 : Nat := 70005404048533902148007

theorem tailTrace_1840523 : CollatzResearch.WordTrace tailWord_1840523 prefixEnd_1840523 70005404048533902148007 := by
  unfold tailWord_1840523
  simp only [CollatzResearch.WordTrace]
  refine ⟨67129388711106982147918223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44752925807404654765278815 67129388711106982147918223)
  ·
    refine ⟨100694083066660473221877335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67129388711106982147918223 100694083066660473221877335)
    ·
      refine ⟨151041124599990709832816003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100694083066660473221877335 151041124599990709832816003)
      ·
        refine ⟨226561686899986064749224005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151041124599990709832816003 226561686899986064749224005)
        ·
          refine ⟨42480316293747387140479501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226561686899986064749224005 42480316293747387140479501)
          ·
            refine ⟨15930118610155270177679813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42480316293747387140479501 15930118610155270177679813)
            ·
              refine ⟨2986897239404113158314965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15930118610155270177679813 2986897239404113158314965)
              ·
                refine ⟨70005404048533902148007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2986897239404113158314965 70005404048533902148007)
                ·
                  rfl

theorem cell22_1840523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 7].length) (baseStart_1840523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840523 prefixEnd_1840523 := by exact prefixLift 1840523
  have htrace : WordTrace (prefixWord ++ tailWord_1840523) baseStart_1840523 baseEnd_1840523 := by
    simpa [prefixWord, tailWord_1840523, baseEnd_1840523] using wordTrace_append hprefix tailTrace_1840523
  have hstable : (prefixWord ++ tailWord_1840523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840523).length < 2 ^ (prefixWord ++ tailWord_1840523).sum := by decide
  have hdescent : baseEnd_1840523 < baseStart_1840523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840568 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_1840568 : Nat := 118140960795 + 1840568 * 2 ^ 59
def prefixEnd_1840568 : Nat := 4983230072969 + 3 ^ 40 * 1840568 * 2
def baseEnd_1840568 : Nat := 210021346952146667318975

theorem tailTrace_1840568 : CollatzResearch.WordTrace tailWord_1840568 prefixEnd_1840568 210021346952146667318975 := by
  unfold tailWord_1840568
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565514997971977416653179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44754019997295969888870905 33565514997971977416653179)
  ·
    refine ⟨50348272496957966124979769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33565514997971977416653179 50348272496957966124979769)
    ·
      refine ⟨37761204372718474593734827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50348272496957966124979769 37761204372718474593734827)
      ·
        refine ⟨56641806559077711890602241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37761204372718474593734827 56641806559077711890602241)
        ·
          refine ⟨42481354919308283917951681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56641806559077711890602241 42481354919308283917951681)
          ·
            refine ⟨31861016189481212938463761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42481354919308283917951681 31861016189481212938463761)
            ·
              refine ⟨23895762142110909703847821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31861016189481212938463761 23895762142110909703847821)
              ·
                refine ⟨8960910803291591138942933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23895762142110909703847821 8960910803291591138942933)
                ·
                  refine ⟨210021346952146667318975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8960910803291591138942933 210021346952146667318975)
                  ·
                    rfl

theorem cell22_1840568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_1840568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840568 prefixEnd_1840568 := by exact prefixLift 1840568
  have htrace : WordTrace (prefixWord ++ tailWord_1840568) baseStart_1840568 baseEnd_1840568 := by
    simpa [prefixWord, tailWord_1840568, baseEnd_1840568] using wordTrace_append hprefix tailTrace_1840568
  have hstable : (prefixWord ++ tailWord_1840568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840568).length < 2 ^ (prefixWord ++ tailWord_1840568).sum := by decide
  have hdescent : baseEnd_1840568 < baseStart_1840568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840578 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1840578 : Nat := 118140960795 + 1840578 * 2 ^ 59
def prefixEnd_1840578 : Nat := 4983230072969 + 3 ^ 40 * 1840578 * 2
def baseEnd_1840578 : Nat := 630067464060803309206895

theorem tailTrace_1840578 : CollatzResearch.WordTrace tailWord_1840578 prefixEnd_1840578 630067464060803309206895 := by
  unfold tailWord_1840578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782848681476931635292597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44754263150605151027446925 16782848681476931635292597)
  ·
    refine ⟨1573392063888462340808681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16782848681476931635292597 1573392063888462340808681)
    ·
      refine ⟨1180044047916346755606511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1573392063888462340808681 1180044047916346755606511)
      ·
        refine ⟨1770066071874520133409767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180044047916346755606511 1770066071874520133409767)
        ·
          refine ⟨2655099107811780200114651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770066071874520133409767 2655099107811780200114651)
          ·
            refine ⟨3982648661717670300171977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655099107811780200114651 3982648661717670300171977)
            ·
              refine ⟨2986986496288252725128983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982648661717670300171977 2986986496288252725128983)
              ·
                refine ⟨4480479744432379087693475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986986496288252725128983 4480479744432379087693475)
                ·
                  refine ⟨6720719616648568631540213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480479744432379087693475 6720719616648568631540213)
                  ·
                    refine ⟨630067464060803309206895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6720719616648568631540213 630067464060803309206895)
                    ·
                      rfl

theorem cell22_1840578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1840578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840578 prefixEnd_1840578 := by exact prefixLift 1840578
  have htrace : WordTrace (prefixWord ++ tailWord_1840578) baseStart_1840578 baseEnd_1840578 := by
    simpa [prefixWord, tailWord_1840578, baseEnd_1840578] using wordTrace_append hprefix tailTrace_1840578
  have hstable : (prefixWord ++ tailWord_1840578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840578).length < 2 ^ (prefixWord ++ tailWord_1840578).sum := by decide
  have hdescent : baseEnd_1840578 < baseStart_1840578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840696 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_1840696 : Nat := 118140960795 + 1840696 * 2 ^ 59
def prefixEnd_1840696 : Nat := 4983230072969 + 3 ^ 40 * 1840696 * 2
def baseEnd_1840696 : Nat := 630107857872290334756533

theorem tailTrace_1840696 : CollatzResearch.WordTrace tailWord_1840696 prefixEnd_1840696 630107857872290334756533 := by
  unfold tailWord_1840696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33567849269740116346982971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44757132359653488462643961 33567849269740116346982971)
  ·
    refine ⟨50351773904610174520474457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33567849269740116346982971 50351773904610174520474457)
    ·
      refine ⟨37763830428457630890355843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50351773904610174520474457 37763830428457630890355843)
      ·
        refine ⟨56645745642686446335533765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37763830428457630890355843 56645745642686446335533765)
        ·
          refine ⟨10621077308003708687912581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56645745642686446335533765 10621077308003708687912581)
          ·
            refine ⟨1991451995250695378983609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10621077308003708687912581 1991451995250695378983609)
            ·
              refine ⟨1493588996438021534237707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991451995250695378983609 1493588996438021534237707)
              ·
                refine ⟨2240383494657032301356561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493588996438021534237707 2240383494657032301356561)
                ·
                  refine ⟨1680287620992774226017421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2240383494657032301356561 1680287620992774226017421)
                  ·
                    refine ⟨630107857872290334756533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680287620992774226017421 630107857872290334756533)
                    ·
                      rfl

theorem cell22_1840696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_1840696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840696 prefixEnd_1840696 := by exact prefixLift 1840696
  have htrace : WordTrace (prefixWord ++ tailWord_1840696) baseStart_1840696 baseEnd_1840696 := by
    simpa [prefixWord, tailWord_1840696, baseEnd_1840696] using wordTrace_append hprefix tailTrace_1840696
  have hstable : (prefixWord ++ tailWord_1840696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840696).length < 2 ^ (prefixWord ++ tailWord_1840696).sum := by decide
  have hdescent : baseEnd_1840696 < baseStart_1840696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840726 : List Nat := [5, 2, 2, 2, 2, 9]
def baseStart_1840726 : Nat := 118140960795 + 1840726 * 2 ^ 59
def prefixEnd_1840726 : Nat := 4983230072969 + 3 ^ 40 * 1840726 * 2
def baseEnd_1840726 : Nat := 7779236141794817981561

theorem tailTrace_1840726 : CollatzResearch.WordTrace tailWord_1840726 prefixEnd_1840726 7779236141794817981561 := by
  unfold tailWord_1840726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196049545585721738597377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44757861819581031878372021 4196049545585721738597377)
  ·
    refine ⟨3147037159189291303948033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4196049545585721738597377 3147037159189291303948033)
    ·
      refine ⟨2360277869391968477961025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3147037159189291303948033 2360277869391968477961025)
      ·
        refine ⟨1770208402043976358470769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360277869391968477961025 1770208402043976358470769)
        ·
          refine ⟨1327656301532982268853077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770208402043976358470769 1327656301532982268853077)
          ·
            refine ⟨7779236141794817981561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1327656301532982268853077 7779236141794817981561)
            ·
              rfl

theorem cell22_1840726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 9].length) (baseStart_1840726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840726 prefixEnd_1840726 := by exact prefixLift 1840726
  have htrace : WordTrace (prefixWord ++ tailWord_1840726) baseStart_1840726 baseEnd_1840726 := by
    simpa [prefixWord, tailWord_1840726, baseEnd_1840726] using wordTrace_append hprefix tailTrace_1840726
  have hstable : (prefixWord ++ tailWord_1840726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840726).length < 2 ^ (prefixWord ++ tailWord_1840726).sum := by decide
  have hdescent : baseEnd_1840726 < baseStart_1840726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840737 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 5]
def baseStart_1840737 : Nat := 118140960795 + 1840737 * 2 ^ 59
def prefixEnd_1840737 : Nat := 4983230072969 + 3 ^ 40 * 1840737 * 2
def baseEnd_1840737 : Nat := 210040631003393298160469

theorem tailTrace_1840737 : CollatzResearch.WordTrace tailWord_1840737 prefixEnd_1840737 210040631003393298160469 := by
  unfold tailWord_1840737
  simp only [CollatzResearch.WordTrace]
  refine ⟨67137193932331696696208465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44758129288221131130805643 67137193932331696696208465)
  ·
    refine ⟨50352895449248772522156349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67137193932331696696208465 50352895449248772522156349)
    ·
      refine ⟨18882335793468289695808631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50352895449248772522156349 18882335793468289695808631)
      ·
        refine ⟨28323503690202434543712947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18882335793468289695808631 28323503690202434543712947)
        ·
          refine ⟨42485255535303651815569421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28323503690202434543712947 42485255535303651815569421)
          ·
            refine ⟨15931970825738869430838533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42485255535303651815569421 15931970825738869430838533)
            ·
              refine ⟨2987244529826038018282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15931970825738869430838533 2987244529826038018282225)
              ·
                refine ⟨2240433397369528513711669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987244529826038018282225 2240433397369528513711669)
                ·
                  refine ⟨210040631003393298160469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240433397369528513711669 210040631003393298160469)
                  ·
                    rfl

theorem cell22_1840737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_1840737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840737 prefixEnd_1840737 := by exact prefixLift 1840737
  have htrace : WordTrace (prefixWord ++ tailWord_1840737) baseStart_1840737 baseEnd_1840737 := by
    simpa [prefixWord, tailWord_1840737, baseEnd_1840737] using wordTrace_append hprefix tailTrace_1840737
  have hstable : (prefixWord ++ tailWord_1840737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840737).length < 2 ^ (prefixWord ++ tailWord_1840737).sum := by decide
  have hdescent : baseEnd_1840737 < baseStart_1840737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840741 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_1840741 : Nat := 118140960795 + 1840741 * 2 ^ 59
def prefixEnd_1840741 : Nat := 4983230072969 + 3 ^ 40 * 1840741 * 2
def baseEnd_1840741 : Nat := 630123262291925217381395

theorem tailTrace_1840741 : CollatzResearch.WordTrace tailWord_1840741 prefixEnd_1840741 630123262291925217381395 := by
  unfold tailWord_1840741
  simp only [CollatzResearch.WordTrace]
  refine ⟨67137339824317205379354077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44758226549544803586236051 67137339824317205379354077)
  ·
    refine ⟨25176502434118952017257779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67137339824317205379354077 25176502434118952017257779)
    ·
      refine ⟨37764753651178428025886669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25176502434118952017257779 37764753651178428025886669)
      ·
        refine ⟨14161782619191910509707501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37764753651178428025886669 14161782619191910509707501)
        ·
          refine ⟨5310668482196966441140313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14161782619191910509707501 5310668482196966441140313)
          ·
            refine ⟨3983001361647724830855235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310668482196966441140313 3983001361647724830855235)
            ·
              refine ⟨5974502042471587246282853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983001361647724830855235 5974502042471587246282853)
              ·
                refine ⟨1120219132963422608678035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5974502042471587246282853 1120219132963422608678035)
                ·
                  refine ⟨1680328699445133913017053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120219132963422608678035 1680328699445133913017053)
                  ·
                    refine ⟨630123262291925217381395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680328699445133913017053 630123262291925217381395)
                    ·
                      rfl

theorem cell22_1840741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_1840741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840741 prefixEnd_1840741 := by exact prefixLift 1840741
  have htrace : WordTrace (prefixWord ++ tailWord_1840741) baseStart_1840741 baseEnd_1840741 := by
    simpa [prefixWord, tailWord_1840741, baseEnd_1840741] using wordTrace_append hprefix tailTrace_1840741
  have hstable : (prefixWord ++ tailWord_1840741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840741).length < 2 ^ (prefixWord ++ tailWord_1840741).sum := by decide
  have hdescent : baseEnd_1840741 < baseStart_1840741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840752 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 5]
def baseStart_1840752 : Nat := 118140960795 + 1840752 * 2 ^ 59
def prefixEnd_1840752 : Nat := 4983230072969 + 3 ^ 40 * 1840752 * 2
def baseEnd_1840752 : Nat := 630127027816724855356361

theorem tailTrace_1840752 : CollatzResearch.WordTrace tailWord_1840752 prefixEnd_1840752 630127027816724855356361 := by
  unfold tailWord_1840752
  simp only [CollatzResearch.WordTrace]
  refine ⟨33568870513638677129002255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44758494018184902838669673 33568870513638677129002255)
  ·
    refine ⟨50353305770458015693503383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33568870513638677129002255 50353305770458015693503383)
    ·
      refine ⟨75529958655687023540255075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50353305770458015693503383 75529958655687023540255075)
      ·
        refine ⟨113294937983530535310382613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75529958655687023540255075 113294937983530535310382613)
        ·
          refine ⟨5310700217977993842674185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113294937983530535310382613 5310700217977993842674185)
          ·
            refine ⟨3983025163483495382005639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310700217977993842674185 3983025163483495382005639)
            ·
              refine ⟨5974537745225243073008459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983025163483495382005639 5974537745225243073008459)
              ·
                refine ⟨8961806617837864609512689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974537745225243073008459 8961806617837864609512689)
                ·
                  refine ⟨6721354963378398457134517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961806617837864609512689 6721354963378398457134517)
                  ·
                    refine ⟨630127027816724855356361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6721354963378398457134517 630127027816724855356361)
                    ·
                      rfl

theorem cell22_1840752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_1840752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840752 prefixEnd_1840752 := by exact prefixLift 1840752
  have htrace : WordTrace (prefixWord ++ tailWord_1840752) baseStart_1840752 baseEnd_1840752 := by
    simpa [prefixWord, tailWord_1840752, baseEnd_1840752] using wordTrace_append hprefix tailTrace_1840752
  have hstable : (prefixWord ++ tailWord_1840752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840752).length < 2 ^ (prefixWord ++ tailWord_1840752).sum := by decide
  have hdescent : baseEnd_1840752 < baseStart_1840752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840788 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1840788 : Nat := 118140960795 + 1840788 * 2 ^ 59
def prefixEnd_1840788 : Nat := 4983230072969 + 3 ^ 40 * 1840788 * 2
def baseEnd_1840788 : Nat := 210046450450810920485417

theorem tailTrace_1840788 : CollatzResearch.WordTrace tailWord_1840788 prefixEnd_1840788 210046450450810920485417 := by
  unfold tailWord_1840788
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569527027573466203157509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44759369370097954937543345 33569527027573466203157509)
  ·
    refine ⟨6294286317670024913092033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33569527027573466203157509 6294286317670024913092033)
    ·
      refine ⟨4720714738252518684819025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6294286317670024913092033 4720714738252518684819025)
      ·
        refine ⟨3540536053689389013614269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4720714738252518684819025 3540536053689389013614269)
        ·
          refine ⟨1327701020133520880105351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3540536053689389013614269 1327701020133520880105351)
          ·
            refine ⟨1991551530200281320158027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327701020133520880105351 1991551530200281320158027)
            ·
              refine ⟨2987327295300421980237041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991551530200281320158027 2987327295300421980237041)
              ·
                refine ⟨2240495471475316485177781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987327295300421980237041 2240495471475316485177781)
                ·
                  refine ⟨210046450450810920485417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240495471475316485177781 210046450450810920485417)
                  ·
                    rfl

theorem cell22_1840788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1840788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840788 prefixEnd_1840788 := by exact prefixLift 1840788
  have htrace : WordTrace (prefixWord ++ tailWord_1840788) baseStart_1840788 baseEnd_1840788 := by
    simpa [prefixWord, tailWord_1840788, baseEnd_1840788] using wordTrace_append hprefix tailTrace_1840788
  have hstable : (prefixWord ++ tailWord_1840788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840788).length < 2 ^ (prefixWord ++ tailWord_1840788).sum := by decide
  have hdescent : baseEnd_1840788 < baseStart_1840788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840844 : List Nat := [2, 2, 1, 5, 2, 2, 8]
def baseStart_1840844 : Nat := 118140960795 + 1840844 * 2 ^ 59
def prefixEnd_1840844 : Nat := 4983230072969 + 3 ^ 40 * 1840844 * 2
def baseEnd_1840844 : Nat := 23339204492476566002077

theorem tailTrace_1840844 : CollatzResearch.WordTrace tailWord_1840844 prefixEnd_1840844 23339204492476566002077 := by
  unfold tailWord_1840844
  simp only [CollatzResearch.WordTrace]
  refine ⟨33570548271472026985176793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44760731028629369313569057 33570548271472026985176793)
  ·
    refine ⟨25177911203604020238882595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33570548271472026985176793 25177911203604020238882595)
    ·
      refine ⟨37766866805406030358323893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25177911203604020238882595 37766866805406030358323893)
      ·
        refine ⟨3540643763006815346092865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37766866805406030358323893 3540643763006815346092865)
        ·
          refine ⟨2655482822255111509569649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540643763006815346092865 2655482822255111509569649)
          ·
            refine ⟨1991612116691333632177237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655482822255111509569649 1991612116691333632177237)
            ·
              refine ⟨23339204492476566002077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1991612116691333632177237 23339204492476566002077)
              ·
                rfl

theorem cell22_1840844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 8].length) (baseStart_1840844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840844 prefixEnd_1840844 := by exact prefixLift 1840844
  have htrace : WordTrace (prefixWord ++ tailWord_1840844) baseStart_1840844 baseEnd_1840844 := by
    simpa [prefixWord, tailWord_1840844, baseEnd_1840844] using wordTrace_append hprefix tailTrace_1840844
  have hstable : (prefixWord ++ tailWord_1840844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840844).length < 2 ^ (prefixWord ++ tailWord_1840844).sum := by decide
  have hdescent : baseEnd_1840844 < baseStart_1840844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840861 : List Nat := [1, 4, 3, 3, 1, 1, 2, 7]
def baseStart_1840861 : Nat := 118140960795 + 1840861 * 2 ^ 59
def prefixEnd_1840861 : Nat := 4983230072969 + 3 ^ 40 * 1840861 * 2
def baseEnd_1840861 : Nat := 70018260082698322709003

theorem tailTrace_1840861 : CollatzResearch.WordTrace tailWord_1840861 prefixEnd_1840861 70018260082698322709003 := by
  unfold tailWord_1840861
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141716583882465873722437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761144389254977249148291 67141716583882465873722437)
  ·
    refine ⟨12589071859477962351322957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67141716583882465873722437 12589071859477962351322957)
    ·
      refine ⟨4720901947304235881746109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12589071859477962351322957 4720901947304235881746109)
      ·
        refine ⟨1770338230239088455654791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4720901947304235881746109 1770338230239088455654791)
        ·
          refine ⟨2655507345358632683482187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770338230239088455654791 2655507345358632683482187)
          ·
            refine ⟨3983261018037949025223281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655507345358632683482187 3983261018037949025223281)
            ·
              refine ⟨2987445763528461768917461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983261018037949025223281 2987445763528461768917461)
              ·
                refine ⟨70018260082698322709003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2987445763528461768917461 70018260082698322709003)
                ·
                  rfl

theorem cell22_1840861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 7].length) (baseStart_1840861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840861 prefixEnd_1840861 := by exact prefixLift 1840861
  have htrace : WordTrace (prefixWord ++ tailWord_1840861) baseStart_1840861 baseEnd_1840861 := by
    simpa [prefixWord, tailWord_1840861, baseEnd_1840861] using wordTrace_append hprefix tailTrace_1840861
  have hstable : (prefixWord ++ tailWord_1840861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840861).length < 2 ^ (prefixWord ++ tailWord_1840861).sum := by decide
  have hdescent : baseEnd_1840861 < baseStart_1840861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840865 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_1840865 : Nat := 118140960795 + 1840865 * 2 ^ 59
def prefixEnd_1840865 : Nat := 4983230072969 + 3 ^ 40 * 1840865 * 2
def baseEnd_1840865 : Nat := 630165710026030227281015

theorem tailTrace_1840865 : CollatzResearch.WordTrace tailWord_1840865 prefixEnd_1840865 630165710026030227281015 := by
  unfold tailWord_1840865
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141862475867974556868049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44761241650578649704578699 67141862475867974556868049)
  ·
    refine ⟨50356396856900980917651037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67141862475867974556868049 50356396856900980917651037)
    ·
      refine ⟨18883648821337867844119139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50356396856900980917651037 18883648821337867844119139)
      ·
        refine ⟨28325473232006801766178709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883648821337867844119139 28325473232006801766178709)
        ·
          refine ⟨1327756557750318832789627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28325473232006801766178709 1327756557750318832789627)
          ·
            refine ⟨1991634836625478249184441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327756557750318832789627 1991634836625478249184441)
            ·
              refine ⟨1493726127469108686888331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991634836625478249184441 1493726127469108686888331)
              ·
                refine ⟨2240589191203663030332497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493726127469108686888331 2240589191203663030332497)
                ·
                  refine ⟨1680441893402747272749373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2240589191203663030332497 1680441893402747272749373)
                  ·
                    refine ⟨630165710026030227281015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680441893402747272749373 630165710026030227281015)
                    ·
                      rfl

theorem cell22_1840865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_1840865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840865 prefixEnd_1840865 := by exact prefixLift 1840865
  have htrace : WordTrace (prefixWord ++ tailWord_1840865) baseStart_1840865 baseEnd_1840865 := by
    simpa [prefixWord, tailWord_1840865, baseEnd_1840865] using wordTrace_append hprefix tailTrace_1840865
  have hstable : (prefixWord ++ tailWord_1840865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840865).length < 2 ^ (prefixWord ++ tailWord_1840865).sum := by decide
  have hdescent : baseEnd_1840865 < baseStart_1840865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840919 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_1840919 : Nat := 118140960795 + 1840919 * 2 ^ 59
def prefixEnd_1840919 : Nat := 4983230072969 + 3 ^ 40 * 1840919 * 2
def baseEnd_1840919 : Nat := 630184195329592086430849

theorem tailTrace_1840919 : CollatzResearch.WordTrace tailWord_1840919 prefixEnd_1840919 630184195329592086430849 := by
  unfold tailWord_1840919
  simp only [CollatzResearch.WordTrace]
  refine ⟨67143832017672341779333811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44762554678448227852889207 67143832017672341779333811)
  ·
    refine ⟨100715748026508512669000717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67143832017672341779333811 100715748026508512669000717)
    ·
      refine ⟨37768405509940692250875269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100715748026508512669000717 37768405509940692250875269)
      ·
        refine ⟨7081576033113879797039113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37768405509940692250875269 7081576033113879797039113)
        ·
          refine ⟨5311182024835409847779335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7081576033113879797039113 5311182024835409847779335)
          ·
            refine ⟨7966773037253114771669003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311182024835409847779335 7966773037253114771669003)
            ·
              refine ⟨11950159555879672157503505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966773037253114771669003 11950159555879672157503505)
              ·
                refine ⟨8962619666909754118127629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11950159555879672157503505 8962619666909754118127629)
                ·
                  refine ⟨3360982375091157794297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8962619666909754118127629 3360982375091157794297861)
                  ·
                    refine ⟨630184195329592086430849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360982375091157794297861 630184195329592086430849)
                    ·
                      rfl

theorem cell22_1840919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_1840919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840919 prefixEnd_1840919 := by exact prefixLift 1840919
  have htrace : WordTrace (prefixWord ++ tailWord_1840919) baseStart_1840919 baseEnd_1840919 := by
    simpa [prefixWord, tailWord_1840919, baseEnd_1840919] using wordTrace_append hprefix tailTrace_1840919
  have hstable : (prefixWord ++ tailWord_1840919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840919).length < 2 ^ (prefixWord ++ tailWord_1840919).sum := by decide
  have hdescent : baseEnd_1840919 < baseStart_1840919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840953 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_1840953 : Nat := 118140960795 + 1840953 * 2 ^ 59
def prefixEnd_1840953 : Nat := 4983230072969 + 3 ^ 40 * 1840953 * 2
def baseEnd_1840953 : Nat := 630195834224427331080745

theorem tailTrace_1840953 : CollatzResearch.WordTrace tailWord_1840953 prefixEnd_1840953 630195834224427331080745 := by
  unfold tailWord_1840953
  simp only [CollatzResearch.WordTrace]
  refine ⟨67145072099549165586071513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44763381399699443724047675 67145072099549165586071513)
  ·
    refine ⟨50358804074661874189553635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67145072099549165586071513 50358804074661874189553635)
    ·
      refine ⟨75538206111992811284330453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50358804074661874189553635 75538206111992811284330453)
      ·
        refine ⟨1770426705749831514476495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75538206111992811284330453 1770426705749831514476495)
        ·
          refine ⟨2655640058624747271714743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770426705749831514476495 2655640058624747271714743)
          ·
            refine ⟨3983460087937120907572115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655640058624747271714743 3983460087937120907572115)
            ·
              refine ⟨5975190131905681361358173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983460087937120907572115 5975190131905681361358173)
              ·
                refine ⟨2240696299464630510509315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5975190131905681361358173 2240696299464630510509315)
                ·
                  refine ⟨3361044449196945765763973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240696299464630510509315 3361044449196945765763973)
                  ·
                    refine ⟨630195834224427331080745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361044449196945765763973 630195834224427331080745)
                    ·
                      rfl

theorem cell22_1840953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_1840953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840953 prefixEnd_1840953 := by exact prefixLift 1840953
  have htrace : WordTrace (prefixWord ++ tailWord_1840953) baseStart_1840953 baseEnd_1840953 := by
    simpa [prefixWord, tailWord_1840953, baseEnd_1840953] using wordTrace_append hprefix tailTrace_1840953
  have hstable : (prefixWord ++ tailWord_1840953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840953).length < 2 ^ (prefixWord ++ tailWord_1840953).sum := by decide
  have hdescent : baseEnd_1840953 < baseStart_1840953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840983 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 5]
def baseStart_1840983 : Nat := 118140960795 + 1840983 * 2 ^ 59
def prefixEnd_1840983 : Nat := 4983230072969 + 3 ^ 40 * 1840983 * 2
def baseEnd_1840983 : Nat := 630206103837517252830653

theorem tailTrace_1840983 : CollatzResearch.WordTrace tailWord_1840983 prefixEnd_1840983 630206103837517252830653 := by
  unfold tailWord_1840983
  simp only [CollatzResearch.WordTrace]
  refine ⟨67146166289440480709663603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44764110859626987139775735 67146166289440480709663603)
  ·
    refine ⟨100719249434160721064495405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67146166289440480709663603 100719249434160721064495405)
    ·
      refine ⟨37769718537810270399185777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100719249434160721064495405 37769718537810270399185777)
      ·
        refine ⟨28327288903357702799389333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37769718537810270399185777 28327288903357702799389333)
        ·
          refine ⟨1327841667344892318721375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28327288903357702799389333 1327841667344892318721375)
          ·
            refine ⟨1991762501017338478082063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327841667344892318721375 1991762501017338478082063)
            ·
              refine ⟨2987643751526007717123095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991762501017338478082063 2987643751526007717123095)
              ·
                refine ⟨4481465627289011575684643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987643751526007717123095 4481465627289011575684643)
                ·
                  refine ⟨6722198440933517363526965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481465627289011575684643 6722198440933517363526965)
                  ·
                    refine ⟨630206103837517252830653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6722198440933517363526965 630206103837517252830653)
                    ·
                      rfl

theorem cell22_1840983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_1840983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1840983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1840983 prefixEnd_1840983 := by exact prefixLift 1840983
  have htrace : WordTrace (prefixWord ++ tailWord_1840983) baseStart_1840983 baseEnd_1840983 := by
    simpa [prefixWord, tailWord_1840983, baseEnd_1840983] using wordTrace_append hprefix tailTrace_1840983
  have hstable : (prefixWord ++ tailWord_1840983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840983).length < 2 ^ (prefixWord ++ tailWord_1840983).sum := by decide
  have hdescent : baseEnd_1840983 < baseStart_1840983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841002 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_1841002 : Nat := 118140960795 + 1841002 * 2 ^ 59
def prefixEnd_1841002 : Nat := 4983230072969 + 3 ^ 40 * 1841002 * 2
def baseEnd_1841002 : Nat := 210070869308602512201865

theorem tailTrace_1841002 : CollatzResearch.WordTrace tailWord_1841002 prefixEnd_1841002 210070869308602512201865 := by
  unfold tailWord_1841002
  simp only [CollatzResearch.WordTrace]
  refine ⟨16786714819092911738651315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44764572850914431303070173 16786714819092911738651315)
  ·
    refine ⟨25180072228639367607976973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16786714819092911738651315 25180072228639367607976973)
    ·
      refine ⟨9442527085739762852991365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25180072228639367607976973 9442527085739762852991365)
      ·
        refine ⟨1770473828576205534935881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9442527085739762852991365 1770473828576205534935881)
        ·
          refine ⟨1327855371432154151201911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770473828576205534935881 1327855371432154151201911)
          ·
            refine ⟨1991783057148231226802867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327855371432154151201911 1991783057148231226802867)
            ·
              refine ⟨2987674585722346840204301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991783057148231226802867 2987674585722346840204301)
              ·
                refine ⟨1120377969645880065076613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987674585722346840204301 1120377969645880065076613)
                ·
                  refine ⟨210070869308602512201865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120377969645880065076613 210070869308602512201865)
                  ·
                    rfl

theorem cell22_1841002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_1841002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841002 prefixEnd_1841002 := by exact prefixLift 1841002
  have htrace : WordTrace (prefixWord ++ tailWord_1841002) baseStart_1841002 baseEnd_1841002 := by
    simpa [prefixWord, tailWord_1841002, baseEnd_1841002] using wordTrace_append hprefix tailTrace_1841002
  have hstable : (prefixWord ++ tailWord_1841002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841002).length < 2 ^ (prefixWord ++ tailWord_1841002).sum := by decide
  have hdescent : baseEnd_1841002 < baseStart_1841002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841024 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 5]
def baseStart_1841024 : Nat := 118140960795 + 1841024 * 2 ^ 59
def prefixEnd_1841024 : Nat := 4983230072969 + 3 ^ 40 * 1841024 * 2
def baseEnd_1841024 : Nat := 210073379658468937518509

theorem tailTrace_1841024 : CollatzResearch.WordTrace tailWord_1841024 prefixEnd_1841024 210073379658468937518509 := by
  unfold tailWord_1841024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573830841145972355953063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44765107788194629807937417 33573830841145972355953063)
  ·
    refine ⟨50360746261718958533929595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33573830841145972355953063 50360746261718958533929595)
    ·
      refine ⟨75541119392578437800894393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50360746261718958533929595 75541119392578437800894393)
      ·
        refine ⟨56655839544433828350670795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75541119392578437800894393 56655839544433828350670795)
        ·
          refine ⟨84983759316650742526006193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56655839544433828350670795 84983759316650742526006193)
          ·
            refine ⟨63737819487488056894504645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84983759316650742526006193 63737819487488056894504645)
            ·
              refine ⟨11950841153904010667719621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63737819487488056894504645 11950841153904010667719621)
              ·
                refine ⟨2240782716357002000197429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11950841153904010667719621 2240782716357002000197429)
                ·
                  refine ⟨210073379658468937518509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240782716357002000197429 210073379658468937518509)
                  ·
                    rfl

theorem cell22_1841024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 5].length) (baseStart_1841024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841024 prefixEnd_1841024 := by exact prefixLift 1841024
  have htrace : WordTrace (prefixWord ++ tailWord_1841024) baseStart_1841024 baseEnd_1841024 := by
    simpa [prefixWord, tailWord_1841024, baseEnd_1841024] using wordTrace_append hprefix tailTrace_1841024
  have hstable : (prefixWord ++ tailWord_1841024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841024).length < 2 ^ (prefixWord ++ tailWord_1841024).sum := by decide
  have hdescent : baseEnd_1841024 < baseStart_1841024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841028 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1841028 : Nat := 118140960795 + 1841028 * 2 ^ 59
def prefixEnd_1841028 : Nat := 4983230072969 + 3 ^ 40 * 1841028 * 2
def baseEnd_1841028 : Nat := 630221508257152135455515

theorem tailTrace_1841028 : CollatzResearch.WordTrace tailWord_1841028 prefixEnd_1841028 630221508257152135455515 := by
  unfold tailWord_1841028
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573903787138726697525869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44765205049518302263367825 33573903787138726697525869)
  ·
    refine ⟨12590213920177022511572201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33573903787138726697525869 12590213920177022511572201)
    ·
      refine ⟨9442660440132766883679151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12590213920177022511572201 9442660440132766883679151)
      ·
        refine ⟨14163990660199150325518727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9442660440132766883679151 14163990660199150325518727)
        ·
          refine ⟨21245985990298725488278091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163990660199150325518727 21245985990298725488278091)
          ·
            refine ⟨31868978985448088232417137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21245985990298725488278091 31868978985448088232417137)
            ·
              refine ⟨23901734239086066174312853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31868978985448088232417137 23901734239086066174312853)
              ·
                refine ⟨1120393792457159351920915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23901734239086066174312853 1120393792457159351920915)
                ·
                  refine ⟨1680590688685739027881373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120393792457159351920915 1680590688685739027881373)
                  ·
                    refine ⟨630221508257152135455515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680590688685739027881373 630221508257152135455515)
                    ·
                      rfl

theorem cell22_1841028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1841028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841028 prefixEnd_1841028 := by exact prefixLift 1841028
  have htrace : WordTrace (prefixWord ++ tailWord_1841028) baseStart_1841028 baseEnd_1841028 := by
    simpa [prefixWord, tailWord_1841028, baseEnd_1841028] using wordTrace_append hprefix tailTrace_1841028
  have hstable : (prefixWord ++ tailWord_1841028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841028).length < 2 ^ (prefixWord ++ tailWord_1841028).sum := by decide
  have hdescent : baseEnd_1841028 < baseStart_1841028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841041 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 5]
def baseStart_1841041 : Nat := 118140960795 + 1841041 * 2 ^ 59
def prefixEnd_1841041 : Nat := 4983230072969 + 3 ^ 40 * 1841041 * 2
def baseEnd_1841041 : Nat := 210075319474274811626825

theorem tailTrace_1841041 : CollatzResearch.WordTrace tailWord_1841041 prefixEnd_1841041 210075319474274811626825 := by
  unfold tailWord_1841041
  simp only [CollatzResearch.WordTrace]
  refine ⟨67148281723230356615274977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44765521148820237743516651 67148281723230356615274977)
  ·
    refine ⟨50361211292422767461456233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67148281723230356615274977 50361211292422767461456233)
    ·
      refine ⟨37770908469317075596092175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50361211292422767461456233 37770908469317075596092175)
      ·
        refine ⟨56656362703975613394138263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37770908469317075596092175 56656362703975613394138263)
        ·
          refine ⟨84984544055963420091207395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56656362703975613394138263 84984544055963420091207395)
          ·
            refine ⟨127476816083945130136811093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84984544055963420091207395 127476816083945130136811093)
            ·
              refine ⟨1493868938483731993790755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 127476816083945130136811093 1493868938483731993790755)
              ·
                refine ⟨2240803407725597990686133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493868938483731993790755 2240803407725597990686133)
                ·
                  refine ⟨210075319474274811626825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2240803407725597990686133 210075319474274811626825)
                  ·
                    rfl

theorem cell22_1841041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_1841041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841041 prefixEnd_1841041 := by exact prefixLift 1841041
  have htrace : WordTrace (prefixWord ++ tailWord_1841041) baseStart_1841041 baseEnd_1841041 := by
    simpa [prefixWord, tailWord_1841041, baseEnd_1841041] using wordTrace_append hprefix tailTrace_1841041
  have hstable : (prefixWord ++ tailWord_1841041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841041).length < 2 ^ (prefixWord ++ tailWord_1841041).sum := by decide
  have hdescent : baseEnd_1841041 < baseStart_1841041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841099 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_1841099 : Nat := 118140960795 + 1841099 * 2 ^ 59
def prefixEnd_1841099 : Nat := 4983230072969 + 3 ^ 40 * 1841099 * 2
def baseEnd_1841099 : Nat := 630245813008131616930297

theorem tailTrace_1841099 : CollatzResearch.WordTrace tailWord_1841099 prefixEnd_1841099 630245813008131616930297 := by
  unfold tailWord_1841099
  simp only [CollatzResearch.WordTrace]
  refine ⟨67150397157020232520886351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44766931438013488347257567 67150397157020232520886351)
  ·
    refine ⟨100725595735530348781329527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67150397157020232520886351 100725595735530348781329527)
    ·
      refine ⟨151088393603295523171994291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100725595735530348781329527 151088393603295523171994291)
      ·
        refine ⟨226632590404943284757991437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151088393603295523171994291 226632590404943284757991437)
        ·
          refine ⟨84987221401853731784246789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226632590404943284757991437 84987221401853731784246789)
          ·
            refine ⟨15935104012847574709546273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84987221401853731784246789 15935104012847574709546273)
            ·
              refine ⟨11951328009635681032159705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15935104012847574709546273 11951328009635681032159705)
              ·
                refine ⟨8963496007226760774119779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11951328009635681032159705 8963496007226760774119779)
                ·
                  refine ⟨13445244010840141161179669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963496007226760774119779 13445244010840141161179669)
                  ·
                    refine ⟨630245813008131616930297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13445244010840141161179669 630245813008131616930297)
                    ·
                      rfl

theorem cell22_1841099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_1841099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841099 prefixEnd_1841099 := by exact prefixLift 1841099
  have htrace : WordTrace (prefixWord ++ tailWord_1841099) baseStart_1841099 baseEnd_1841099 := by
    simpa [prefixWord, tailWord_1841099, baseEnd_1841099] using wordTrace_append hprefix tailTrace_1841099
  have hstable : (prefixWord ++ tailWord_1841099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841099).length < 2 ^ (prefixWord ++ tailWord_1841099).sum := by decide
  have hdescent : baseEnd_1841099 < baseStart_1841099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841144 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 8]
def baseStart_1841144 : Nat := 118140960795 + 1841144 * 2 ^ 59
def prefixEnd_1841144 : Nat := 4983230072969 + 3 ^ 40 * 1841144 * 2
def baseEnd_1841144 : Nat := 630261217427766499555159

theorem tailTrace_1841144 : CollatzResearch.WordTrace tailWord_1841144 prefixEnd_1841144 630261217427766499555159 := by
  unfold tailWord_1841144
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576019220928602603137243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44768025627904803470849657 33576019220928602603137243)
  ·
    refine ⟨50364028831392903904705865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33576019220928602603137243 50364028831392903904705865)
    ·
      refine ⟨37773021623544677928529399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50364028831392903904705865 37773021623544677928529399)
      ·
        refine ⟨56659532435317016892794099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37773021623544677928529399 56659532435317016892794099)
        ·
          refine ⟨84989298652975525339191149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56659532435317016892794099 84989298652975525339191149)
          ·
            refine ⟨31870986994865822002196681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84989298652975525339191149 31870986994865822002196681)
            ·
              refine ⟨23903240246149366501647511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31870986994865822002196681 23903240246149366501647511)
              ·
                refine ⟨35854860369224049752471267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23903240246149366501647511 35854860369224049752471267)
                ·
                  refine ⟨53782290553836074628706901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35854860369224049752471267 53782290553836074628706901)
                  ·
                    refine ⟨630261217427766499555159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53782290553836074628706901 630261217427766499555159)
                    ·
                      rfl

theorem cell22_1841144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_1841144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841144 prefixEnd_1841144 := by exact prefixLift 1841144
  have htrace : WordTrace (prefixWord ++ tailWord_1841144) baseStart_1841144 baseEnd_1841144 := by
    simpa [prefixWord, tailWord_1841144, baseEnd_1841144] using wordTrace_append hprefix tailTrace_1841144
  have hstable : (prefixWord ++ tailWord_1841144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841144).length < 2 ^ (prefixWord ++ tailWord_1841144).sum := by decide
  have hdescent : baseEnd_1841144 < baseStart_1841144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841240 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 1, 4]
def baseStart_1841240 : Nat := 118140960795 + 1841240 * 2 ^ 59
def prefixEnd_1841240 : Nat := 4983230072969 + 3 ^ 40 * 1841240 * 2
def baseEnd_1841240 : Nat := 630294080189654249154865

theorem tailTrace_1841240 : CollatzResearch.WordTrace tailWord_1841240 prefixEnd_1841240 630294080189654249154865 := by
  unfold tailWord_1841240
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577769924754706800884587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44770359899672942401179449 33577769924754706800884587)
  ·
    refine ⟨50366654887132060201326881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577769924754706800884587 50366654887132060201326881)
    ·
      refine ⟨37774991165349045150995161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50366654887132060201326881 37774991165349045150995161)
      ·
        refine ⟨28331243374011783863246371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37774991165349045150995161 28331243374011783863246371)
        ·
          refine ⟨42496865061017675794869557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28331243374011783863246371 42496865061017675794869557)
          ·
            refine ⟨3984081099470407105769021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42496865061017675794869557 3984081099470407105769021)
            ·
              refine ⟨1494030412301402664663383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984081099470407105769021 1494030412301402664663383)
              ·
                refine ⟨2241045618452103996995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494030412301402664663383 2241045618452103996995075)
                ·
                  refine ⟨3361568427678155995492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241045618452103996995075 3361568427678155995492613)
                  ·
                    refine ⟨630294080189654249154865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361568427678155995492613 630294080189654249154865)
                    ·
                      rfl

theorem cell22_1841240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_1841240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841240 prefixEnd_1841240 := by exact prefixLift 1841240
  have htrace : WordTrace (prefixWord ++ tailWord_1841240) baseStart_1841240 baseEnd_1841240 := by
    simpa [prefixWord, tailWord_1841240, baseEnd_1841240] using wordTrace_append hprefix tailTrace_1841240
  have hstable : (prefixWord ++ tailWord_1841240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841240).length < 2 ^ (prefixWord ++ tailWord_1841240).sum := by decide
  have hdescent : baseEnd_1841240 < baseStart_1841240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841270 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1841270 : Nat := 118140960795 + 1841270 * 2 ^ 59
def prefixEnd_1841270 : Nat := 4983230072969 + 3 ^ 40 * 1841270 * 2
def baseEnd_1841270 : Nat := 630304349802744170904773

theorem tailTrace_1841270 : CollatzResearch.WordTrace tailWord_1841270 prefixEnd_1841270 630304349802744170904773 := by
  unfold tailWord_1841270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197289627462545545335079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44771089359600485816907509 4197289627462545545335079)
  ·
    refine ⟨6295934441193818318002619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197289627462545545335079 6295934441193818318002619)
    ·
      refine ⟨9443901661790727477003929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6295934441193818318002619 9443901661790727477003929)
      ·
        refine ⟨7082926246343045607752947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9443901661790727477003929 7082926246343045607752947)
        ·
          refine ⟨10624389369514568411629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082926246343045607752947 10624389369514568411629421)
          ·
            refine ⟨3984146013567963154361033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10624389369514568411629421 3984146013567963154361033)
            ·
              refine ⟨2988109510175972365770775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984146013567963154361033 2988109510175972365770775)
              ·
                refine ⟨4482164265263958548656163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988109510175972365770775 4482164265263958548656163)
                ·
                  refine ⟨6723246397895937822984245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482164265263958548656163 6723246397895937822984245)
                  ·
                    refine ⟨630304349802744170904773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6723246397895937822984245 630304349802744170904773)
                    ·
                      rfl

theorem cell22_1841270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1841270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841270 prefixEnd_1841270 := by exact prefixLift 1841270
  have htrace : WordTrace (prefixWord ++ tailWord_1841270) baseStart_1841270 baseEnd_1841270 := by
    simpa [prefixWord, tailWord_1841270, baseEnd_1841270] using wordTrace_append hprefix tailTrace_1841270
  have hstable : (prefixWord ++ tailWord_1841270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841270).length < 2 ^ (prefixWord ++ tailWord_1841270).sum := by decide
  have hdescent : baseEnd_1841270 < baseStart_1841270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841283 : List Nat := [1, 1, 1, 3, 3, 4, 3, 6]
def baseStart_1841283 : Nat := 118140960795 + 1841283 * 2 ^ 59
def prefixEnd_1841283 : Nat := 4983230072969 + 3 ^ 40 * 1841283 * 2
def baseEnd_1841283 : Nat := 70034311107601830036637

theorem tailTrace_1841283 : CollatzResearch.WordTrace tailWord_1841283 prefixEnd_1841283 70034311107601830036637 := by
  unfold tailWord_1841283
  simp only [CollatzResearch.WordTrace]
  refine ⟨67157108188353631945584503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44771405458902421297056335 67157108188353631945584503)
  ·
    refine ⟨100735662282530447918376755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67157108188353631945584503 100735662282530447918376755)
    ·
      refine ⟨151103493423795671877565133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100735662282530447918376755 151103493423795671877565133)
      ·
        refine ⟨56663810033923376954086925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151103493423795671877565133 56663810033923376954086925)
        ·
          refine ⟨21248928762721266357782597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56663810033923376954086925 21248928762721266357782597)
          ·
            refine ⟨3984174143010237442084237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21248928762721266357782597 3984174143010237442084237)
            ·
              refine ⟨1494065303628839040781589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984174143010237442084237 1494065303628839040781589)
              ·
                refine ⟨70034311107601830036637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1494065303628839040781589 70034311107601830036637)
                ·
                  rfl

theorem cell22_1841283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 6].length) (baseStart_1841283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841283 prefixEnd_1841283 := by exact prefixLift 1841283
  have htrace : WordTrace (prefixWord ++ tailWord_1841283) baseStart_1841283 baseEnd_1841283 := by
    simpa [prefixWord, tailWord_1841283, baseEnd_1841283] using wordTrace_append hprefix tailTrace_1841283
  have hstable : (prefixWord ++ tailWord_1841283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841283).length < 2 ^ (prefixWord ++ tailWord_1841283).sum := by decide
  have hdescent : baseEnd_1841283 < baseStart_1841283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841285 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_1841285 : Nat := 118140960795 + 1841285 * 2 ^ 59
def prefixEnd_1841285 : Nat := 4983230072969 + 3 ^ 40 * 1841285 * 2
def baseEnd_1841285 : Nat := 630309484609289131779727

theorem tailTrace_1841285 : CollatzResearch.WordTrace tailWord_1841285 prefixEnd_1841285 630309484609289131779727 := by
  unfold tailWord_1841285
  simp only [CollatzResearch.WordTrace]
  refine ⟨67157181134346386287157309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44771454089564257524771539 67157181134346386287157309)
  ·
    refine ⟨25183942925379894857683991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67157181134346386287157309 25183942925379894857683991)
    ·
      refine ⟨37775914388069842286525987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183942925379894857683991 37775914388069842286525987)
      ·
        refine ⟨56663871582104763429788981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37775914388069842286525987 56663871582104763429788981)
        ·
          refine ⟨5312237960822321571542717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56663871582104763429788981 5312237960822321571542717)
          ·
            refine ⟨1992089235308370589328519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5312237960822321571542717 1992089235308370589328519)
            ·
              refine ⟨2988133852962555883992779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992089235308370589328519 2988133852962555883992779)
              ·
                refine ⟨4482200779443833825989169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988133852962555883992779 4482200779443833825989169)
                ·
                  refine ⟨3361650584582875369491877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4482200779443833825989169 3361650584582875369491877)
                  ·
                    refine ⟨630309484609289131779727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361650584582875369491877 630309484609289131779727)
                    ·
                      rfl

theorem cell22_1841285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_1841285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841285 prefixEnd_1841285 := by exact prefixLift 1841285
  have htrace : WordTrace (prefixWord ++ tailWord_1841285) baseStart_1841285 baseEnd_1841285 := by
    simpa [prefixWord, tailWord_1841285, baseEnd_1841285] using wordTrace_append hprefix tailTrace_1841285
  have hstable : (prefixWord ++ tailWord_1841285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841285).length < 2 ^ (prefixWord ++ tailWord_1841285).sum := by decide
  have hdescent : baseEnd_1841285 < baseStart_1841285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841300 : List Nat := [2, 4, 2, 3, 1, 1, 9]
def baseStart_1841300 : Nat := 118140960795 + 1841300 * 2 ^ 59
def prefixEnd_1841300 : Nat := 4983230072969 + 3 ^ 40 * 1841300 * 2
def baseEnd_1841300 : Nat := 23344985904290151579803

theorem tailTrace_1841300 : CollatzResearch.WordTrace tailWord_1841300 prefixEnd_1841300 23344985904290151579803 := by
  unfold tailWord_1841300
  simp only [CollatzResearch.WordTrace]
  refine ⟨33578864114646021924476677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44771818819528029232635569 33578864114646021924476677)
  ·
    refine ⟨6296037021496129110839377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33578864114646021924476677 6296037021496129110839377)
    ·
      refine ⟨4722027766122096833129533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6296037021496129110839377 4722027766122096833129533)
      ·
        refine ⟨1770760412295786312423575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4722027766122096833129533 1770760412295786312423575)
        ·
          refine ⟨2656140618443679468635363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770760412295786312423575 2656140618443679468635363)
          ·
            refine ⟨3984210927665519202953045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656140618443679468635363 3984210927665519202953045)
            ·
              refine ⟨23344985904290151579803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3984210927665519202953045 23344985904290151579803)
              ·
                rfl

theorem cell22_1841300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 9].length) (baseStart_1841300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841300 prefixEnd_1841300 := by exact prefixLift 1841300
  have htrace : WordTrace (prefixWord ++ tailWord_1841300) baseStart_1841300 baseEnd_1841300 := by
    simpa [prefixWord, tailWord_1841300, baseEnd_1841300] using wordTrace_append hprefix tailTrace_1841300
  have hstable : (prefixWord ++ tailWord_1841300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841300).length < 2 ^ (prefixWord ++ tailWord_1841300).sum := by decide
  have hdescent : baseEnd_1841300 < baseStart_1841300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841304 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 2, 3]
def baseStart_1841304 : Nat := 118140960795 + 1841304 * 2 ^ 59
def prefixEnd_1841304 : Nat := 4983230072969 + 3 ^ 40 * 1841304 * 2
def baseEnd_1841304 : Nat := 630315988697579415554669

theorem tailTrace_1841304 : CollatzResearch.WordTrace tailWord_1841304 prefixEnd_1841304 630315988697579415554669 := by
  unfold tailWord_1841304
  simp only [CollatzResearch.WordTrace]
  refine ⟨33578937060638776266049483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44771916080851701688065977 33578937060638776266049483)
  ·
    refine ⟨50368405590958164399074225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33578937060638776266049483 50368405590958164399074225)
    ·
      refine ⟨37776304193218623299305669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50368405590958164399074225 37776304193218623299305669)
      ·
        refine ⟨7083057036228491868619813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37776304193218623299305669 7083057036228491868619813)
        ·
          refine ⟨1328073194292842225366215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7083057036228491868619813 1328073194292842225366215)
          ·
            refine ⟨1992109791439263338049323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328073194292842225366215 1992109791439263338049323)
            ·
              refine ⟨2988164687158895007073985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992109791439263338049323 2988164687158895007073985)
              ·
                refine ⟨2241123515369171255305489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988164687158895007073985 2241123515369171255305489)
                ·
                  refine ⟨1680842636526878441479117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241123515369171255305489 1680842636526878441479117)
                  ·
                    refine ⟨630315988697579415554669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680842636526878441479117 630315988697579415554669)
                    ·
                      rfl

theorem cell22_1841304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_1841304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841304 prefixEnd_1841304 := by exact prefixLift 1841304
  have htrace : WordTrace (prefixWord ++ tailWord_1841304) baseStart_1841304 baseEnd_1841304 := by
    simpa [prefixWord, tailWord_1841304, baseEnd_1841304] using wordTrace_append hprefix tailTrace_1841304
  have hstable : (prefixWord ++ tailWord_1841304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841304).length < 2 ^ (prefixWord ++ tailWord_1841304).sum := by decide
  have hdescent : baseEnd_1841304 < baseStart_1841304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841379 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 5]
def baseStart_1841379 : Nat := 118140960795 + 1841379 * 2 ^ 59
def prefixEnd_1841379 : Nat := 4983230072969 + 3 ^ 40 * 1841379 * 2
def baseEnd_1841379 : Nat := 210113887576768073309813

theorem tailTrace_1841379 : CollatzResearch.WordTrace tailWord_1841379 prefixEnd_1841379 210113887576768073309813 := by
  unfold tailWord_1841379
  simp only [CollatzResearch.WordTrace]
  refine ⟨67160609596005840341079191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44773739730670560227386127 67160609596005840341079191)
  ·
    refine ⟨100740914394008760511618787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67160609596005840341079191 100740914394008760511618787)
    ·
      refine ⟨151111371591013140767428181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100740914394008760511618787 151111371591013140767428181)
      ·
        refine ⟨1770836385832185243368299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 151111371591013140767428181 1770836385832185243368299)
        ·
          refine ⟨2656254578748277865052449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770836385832185243368299 2656254578748277865052449)
          ·
            refine ⟨1992190934061208398789337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656254578748277865052449 1992190934061208398789337)
            ·
              refine ⟨1494143200545906299092003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992190934061208398789337 1494143200545906299092003)
              ·
                refine ⟨2241214800818859448638005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494143200545906299092003 2241214800818859448638005)
                ·
                  refine ⟨210113887576768073309813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241214800818859448638005 210113887576768073309813)
                  ·
                    rfl

theorem cell22_1841379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 5].length) (baseStart_1841379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841379 prefixEnd_1841379 := by exact prefixLift 1841379
  have htrace : WordTrace (prefixWord ++ tailWord_1841379) baseStart_1841379 baseEnd_1841379 := by
    simpa [prefixWord, tailWord_1841379, baseEnd_1841379] using wordTrace_append hprefix tailTrace_1841379
  have hstable : (prefixWord ++ tailWord_1841379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841379).length < 2 ^ (prefixWord ++ tailWord_1841379).sum := by decide
  have hdescent : baseEnd_1841379 < baseStart_1841379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841388 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_1841388 : Nat := 118140960795 + 1841388 * 2 ^ 59
def prefixEnd_1841388 : Nat := 4983230072969 + 3 ^ 40 * 1841388 * 2
def baseEnd_1841388 : Nat := 630344743614231196454411

theorem tailTrace_1841388 : CollatzResearch.WordTrace tailWord_1841388 prefixEnd_1841388 630344743614231196454411 := by
  unfold tailWord_1841388
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580468926486617439078409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44773958568648823252104545 33580468926486617439078409)
  ·
    refine ⟨25185351694864963079308807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33580468926486617439078409 25185351694864963079308807)
    ·
      refine ⟨37778027542297444618963211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25185351694864963079308807 37778027542297444618963211)
      ·
        refine ⟨56667041313446166928444817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37778027542297444618963211 56667041313446166928444817)
        ·
          refine ⟨42500280985084625196333613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56667041313446166928444817 42500280985084625196333613)
          ·
            refine ⟨15937605369406734448625105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42500280985084625196333613 15937605369406734448625105)
            ·
              refine ⟨11953204027055050836468829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15937605369406734448625105 11953204027055050836468829)
              ·
                refine ⟨4482451510145644063675811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11953204027055050836468829 4482451510145644063675811)
                ·
                  refine ⟨6723677265218466095513717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482451510145644063675811 6723677265218466095513717)
                  ·
                    refine ⟨630344743614231196454411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6723677265218466095513717 630344743614231196454411)
                    ·
                      rfl

theorem cell22_1841388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_1841388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841388 prefixEnd_1841388 := by exact prefixLift 1841388
  have htrace : WordTrace (prefixWord ++ tailWord_1841388) baseStart_1841388 baseEnd_1841388 := by
    simpa [prefixWord, tailWord_1841388, baseEnd_1841388] using wordTrace_append hprefix tailTrace_1841388
  have hstable : (prefixWord ++ tailWord_1841388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841388).length < 2 ^ (prefixWord ++ tailWord_1841388).sum := by decide
  have hdescent : baseEnd_1841388 < baseStart_1841388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841422 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_1841422 : Nat := 118140960795 + 1841422 * 2 ^ 59
def prefixEnd_1841422 : Nat := 4983230072969 + 3 ^ 40 * 1841422 * 2
def baseEnd_1841422 : Nat := 630356382509066441104307

theorem tailTrace_1841422 : CollatzResearch.WordTrace tailWord_1841422 prefixEnd_1841422 630356382509066441104307 := by
  unfold tailWord_1841422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395272241856257335611815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44774785289900039123263013 8395272241856257335611815)
  ·
    refine ⟨12592908362784386003417723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8395272241856257335611815 12592908362784386003417723)
    ·
      refine ⟨18889362544176579005126585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12592908362784386003417723 18889362544176579005126585)
      ·
        refine ⟨14167021908132434253844939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18889362544176579005126585 14167021908132434253844939)
        ·
          refine ⟨21250532862198651380767409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167021908132434253844939 21250532862198651380767409)
          ·
            refine ⟨15937899646648988535575557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21250532862198651380767409 15937899646648988535575557)
            ·
              refine ⟨2988356183746685350420417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15937899646648988535575557 2988356183746685350420417)
              ·
                refine ⟨2241267137810014012815313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988356183746685350420417 2241267137810014012815313)
                ·
                  refine ⟨1680950353357510509611485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241267137810014012815313 1680950353357510509611485)
                  ·
                    refine ⟨630356382509066441104307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680950353357510509611485 630356382509066441104307)
                    ·
                      rfl

theorem cell22_1841422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_1841422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841422 prefixEnd_1841422 := by exact prefixLift 1841422
  have htrace : WordTrace (prefixWord ++ tailWord_1841422) baseStart_1841422 baseEnd_1841422 := by
    simpa [prefixWord, tailWord_1841422, baseEnd_1841422] using wordTrace_append hprefix tailTrace_1841422
  have hstable : (prefixWord ++ tailWord_1841422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841422).length < 2 ^ (prefixWord ++ tailWord_1841422).sum := by decide
  have hdescent : baseEnd_1841422 < baseStart_1841422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841480 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 5]
def baseStart_1841480 : Nat := 118140960795 + 1841480 * 2 ^ 59
def prefixEnd_1841480 : Nat := 4983230072969 + 3 ^ 40 * 1841480 * 2
def baseEnd_1841480 : Nat := 210125412364791207718043

theorem tailTrace_1841480 : CollatzResearch.WordTrace tailWord_1841480 prefixEnd_1841480 210125412364791207718043 := by
  unfold tailWord_1841480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582146684319967295252947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44776195579093289727003929 33582146684319967295252947)
  ·
    refine ⟨50373220026479950942879421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33582146684319967295252947 50373220026479950942879421)
    ·
      refine ⟨18889957509929981603579783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50373220026479950942879421 18889957509929981603579783)
      ·
        refine ⟨28334936264894972405369675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18889957509929981603579783 28334936264894972405369675)
        ·
          refine ⟨42502404397342458608054513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28334936264894972405369675 42502404397342458608054513)
          ·
            refine ⟨31876803298006843956040885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42502404397342458608054513 31876803298006843956040885)
            ·
              refine ⟨2988450309188141620878833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31876803298006843956040885 2988450309188141620878833)
              ·
                refine ⟨2241337731891106215659125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988450309188141620878833 2241337731891106215659125)
                ·
                  refine ⟨210125412364791207718043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241337731891106215659125 210125412364791207718043)
                  ·
                    rfl

theorem cell22_1841480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 5].length) (baseStart_1841480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841480 prefixEnd_1841480 := by exact prefixLift 1841480
  have htrace : WordTrace (prefixWord ++ tailWord_1841480) baseStart_1841480 baseEnd_1841480 := by
    simpa [prefixWord, tailWord_1841480, baseEnd_1841480] using wordTrace_append hprefix tailTrace_1841480
  have hstable : (prefixWord ++ tailWord_1841480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841480).length < 2 ^ (prefixWord ++ tailWord_1841480).sum := by decide
  have hdescent : baseEnd_1841480 < baseStart_1841480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841570 : List Nat := [3, 3, 1, 2, 1, 1, 1, 10]
def baseStart_1841570 : Nat := 118140960795 + 1841570 * 2 ^ 59
def prefixEnd_1841570 : Nat := 4983230072969 + 3 ^ 40 * 1841570 * 2
def baseEnd_1841570 : Nat := 70045227325960376489317

theorem tailTrace_1841570 : CollatzResearch.WordTrace tailWord_1841570 prefixEnd_1841570 70045227325960376489317 := by
  unfold tailWord_1841570
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791893984578469990320541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44778383958875919974188109 16791893984578469990320541)
  ·
    refine ⟨6296960244216926246370203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16791893984578469990320541 6296960244216926246370203)
    ·
      refine ⟨9445440366325389369555305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296960244216926246370203 9445440366325389369555305)
      ·
        refine ⟨7084080274744042027166479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9445440366325389369555305 7084080274744042027166479)
        ·
          refine ⟨10626120412116063040749719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084080274744042027166479 10626120412116063040749719)
          ·
            refine ⟨15939180618174094561124579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626120412116063040749719 15939180618174094561124579)
            ·
              refine ⟨23908770927261141841686869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15939180618174094561124579 23908770927261141841686869)
              ·
                refine ⟨70045227325960376489317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23908770927261141841686869 70045227325960376489317)
                ·
                  rfl

theorem cell22_1841570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_1841570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841570 prefixEnd_1841570 := by exact prefixLift 1841570
  have htrace : WordTrace (prefixWord ++ tailWord_1841570) baseStart_1841570 baseEnd_1841570 := by
    simpa [prefixWord, tailWord_1841570, baseEnd_1841570] using wordTrace_append hprefix tailTrace_1841570
  have hstable : (prefixWord ++ tailWord_1841570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841570).length < 2 ^ (prefixWord ++ tailWord_1841570).sum := by decide
  have hdescent : baseEnd_1841570 < baseStart_1841570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841604 : List Nat := [2, 3, 3, 2, 2, 2, 1, 7]
def baseStart_1841604 : Nat := 118140960795 + 1841604 * 2 ^ 59
def prefixEnd_1841604 : Nat := 4983230072969 + 3 ^ 40 * 1841604 * 2
def baseEnd_1841604 : Nat := 70046520536497625894861

theorem tailTrace_1841604 : CollatzResearch.WordTrace tailWord_1841604 prefixEnd_1841604 70046520536497625894861 := by
  unfold tailWord_1841604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33584408010095351884009933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44779210680127135845346577 33584408010095351884009933)
  ·
    refine ⟨12594153003785756956503725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33584408010095351884009933 12594153003785756956503725)
    ·
      refine ⟨4722807376419658858688897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12594153003785756956503725 4722807376419658858688897)
      ·
        refine ⟨3542105532314744144016673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4722807376419658858688897 3542105532314744144016673)
        ·
          refine ⟨2656579149236058108012505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3542105532314744144016673 2656579149236058108012505)
          ·
            refine ⟨1992434361927043581009379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656579149236058108012505 1992434361927043581009379)
            ·
              refine ⟨2988651542890565371514069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992434361927043581009379 2988651542890565371514069)
              ·
                refine ⟨70046520536497625894861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2988651542890565371514069 70046520536497625894861)
                ·
                  rfl

theorem cell22_1841604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 7].length) (baseStart_1841604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841604 prefixEnd_1841604 := by exact prefixLift 1841604
  have htrace : WordTrace (prefixWord ++ tailWord_1841604) baseStart_1841604 baseEnd_1841604 := by
    simpa [prefixWord, tailWord_1841604, baseEnd_1841604] using wordTrace_append hprefix tailTrace_1841604
  have hstable : (prefixWord ++ tailWord_1841604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841604).length < 2 ^ (prefixWord ++ tailWord_1841604).sum := by decide
  have hdescent : baseEnd_1841604 < baseStart_1841604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841722 : List Nat := [3, 1, 1, 1, 3, 4, 2, 7]
def baseStart_1841722 : Nat := 118140960795 + 1841722 * 2 ^ 59
def prefixEnd_1841722 : Nat := 4983230072969 + 3 ^ 40 * 1841722 * 2
def baseEnd_1841722 : Nat := 70051008737773962067043

theorem tailTrace_1841722 : CollatzResearch.WordTrace tailWord_1841722 prefixEnd_1841722 70051008737773962067043 := by
  unfold tailWord_1841722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793279958440802480203855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44782079889175473280543613 16793279958440802480203855)
  ·
    refine ⟨25189919937661203720305783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793279958440802480203855 25189919937661203720305783)
    ·
      refine ⟨37784879906491805580458675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25189919937661203720305783 37784879906491805580458675)
      ·
        refine ⟨56677319859737708370688013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37784879906491805580458675 56677319859737708370688013)
        ·
          refine ⟨21253994947401640639008005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56677319859737708370688013 21253994947401640639008005)
          ·
            refine ⟨3985124052637807619814001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21253994947401640639008005 3985124052637807619814001)
            ·
              refine ⟨2988843039478355714860501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985124052637807619814001 2988843039478355714860501)
              ·
                refine ⟨70051008737773962067043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2988843039478355714860501 70051008737773962067043)
                ·
                  rfl

theorem cell22_1841722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_1841722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841722 prefixEnd_1841722 := by exact prefixLift 1841722
  have htrace : WordTrace (prefixWord ++ tailWord_1841722) baseStart_1841722 baseEnd_1841722 := by
    simpa [prefixWord, tailWord_1841722, baseEnd_1841722] using wordTrace_append hprefix tailTrace_1841722
  have hstable : (prefixWord ++ tailWord_1841722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841722).length < 2 ^ (prefixWord ++ tailWord_1841722).sum := by decide
  have hdescent : baseEnd_1841722 < baseStart_1841722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841741 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1841741 : Nat := 118140960795 + 1841741 * 2 ^ 59
def prefixEnd_1841741 : Nat := 4983230072969 + 3 ^ 40 * 1841741 * 2
def baseEnd_1841741 : Nat := 630465582728255942378329

theorem tailTrace_1841741 : CollatzResearch.WordTrace tailWord_1841741 prefixEnd_1841741 630465582728255942378329 := by
  unfold tailWord_1841741
  simp only [CollatzResearch.WordTrace]
  refine ⟨67173812820694376165757077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44782541880462917443838051 67173812820694376165757077)
  ·
    refine ⟨3148772475970048882769863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67173812820694376165757077 3148772475970048882769863)
    ·
      refine ⟨4723158713955073324154795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148772475970048882769863 4723158713955073324154795)
      ·
        refine ⟨7084738070932609986232193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4723158713955073324154795 7084738070932609986232193)
        ·
          refine ⟨5313553553199457489674145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7084738070932609986232193 5313553553199457489674145)
          ·
            refine ⟨3985165164899593117255609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5313553553199457489674145 3985165164899593117255609)
            ·
              refine ⟨2988873873674694837941707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985165164899593117255609 2988873873674694837941707)
              ·
                refine ⟨4483310810512042256912561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988873873674694837941707 4483310810512042256912561)
                ·
                  refine ⟨3362483107884031692684421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483310810512042256912561 3362483107884031692684421)
                  ·
                    refine ⟨630465582728255942378329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362483107884031692684421 630465582728255942378329)
                    ·
                      rfl

theorem cell22_1841741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1841741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841741 prefixEnd_1841741 := by exact prefixLift 1841741
  have htrace : WordTrace (prefixWord ++ tailWord_1841741) baseStart_1841741 baseEnd_1841741 := by
    simpa [prefixWord, tailWord_1841741, baseEnd_1841741] using wordTrace_append hprefix tailTrace_1841741
  have hstable : (prefixWord ++ tailWord_1841741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841741).length < 2 ^ (prefixWord ++ tailWord_1841741).sum := by decide
  have hdescent : baseEnd_1841741 < baseStart_1841741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841762 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1841762 : Nat := 118140960795 + 1841762 * 2 ^ 59
def prefixEnd_1841762 : Nat := 4983230072969 + 3 ^ 40 * 1841762 * 2
def baseEnd_1841762 : Nat := 210157590485806295867755

theorem tailTrace_1841762 : CollatzResearch.WordTrace tailWord_1841762 prefixEnd_1841762 210157590485806295867755 := by
  unfold tailWord_1841762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793644688404574188067885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44783052502412197834847693 16793644688404574188067885)
  ·
    refine ⟨6297616758151715320525457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16793644688404574188067885 6297616758151715320525457)
    ·
      refine ⟨4723212568613786490394093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6297616758151715320525457 4723212568613786490394093)
      ·
        refine ⟨1771204713230169933897785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4723212568613786490394093 1771204713230169933897785)
        ·
          refine ⟨1328403534922627450423339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771204713230169933897785 1328403534922627450423339)
          ·
            refine ⟨1992605302383941175635009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328403534922627450423339 1992605302383941175635009)
            ·
              refine ⟨1494453976787955881726257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992605302383941175635009 1494453976787955881726257)
              ·
                refine ⟨1120840482590966911294693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494453976787955881726257 1120840482590966911294693)
                ·
                  refine ⟨210157590485806295867755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1120840482590966911294693 210157590485806295867755)
                  ·
                    rfl

theorem cell22_1841762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1841762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841762 prefixEnd_1841762 := by exact prefixLift 1841762
  have htrace : WordTrace (prefixWord ++ tailWord_1841762) baseStart_1841762 baseEnd_1841762 := by
    simpa [prefixWord, tailWord_1841762, baseEnd_1841762] using wordTrace_append hprefix tailTrace_1841762
  have hstable : (prefixWord ++ tailWord_1841762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841762).length < 2 ^ (prefixWord ++ tailWord_1841762).sum := by decide
  have hdescent : baseEnd_1841762 < baseStart_1841762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841818 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1841818 : Nat := 118140960795 + 1841818 * 2 ^ 59
def prefixEnd_1841818 : Nat := 4983230072969 + 3 ^ 40 * 1841818 * 2
def baseEnd_1841818 : Nat := 210163980467284469401031

theorem tailTrace_1841818 : CollatzResearch.WordTrace tailWord_1841818 prefixEnd_1841818 210163980467284469401031 := by
  unfold tailWord_1841818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794155310353854579077527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44784414160943612210873405 16794155310353854579077527)
  ·
    refine ⟨25191232965530781868616291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16794155310353854579077527 25191232965530781868616291)
    ·
      refine ⟨37786849448296172802924437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25191232965530781868616291 37786849448296172802924437)
      ·
        refine ⟨1771258567888883100137083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37786849448296172802924437 1771258567888883100137083)
        ·
          refine ⟨2656887851833324650205625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771258567888883100137083 2656887851833324650205625)
          ·
            refine ⟨1992665888874993487654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656887851833324650205625 1992665888874993487654219)
            ·
              refine ⟨2988998833312490231481329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992665888874993487654219 2988998833312490231481329)
              ·
                refine ⟨2241749124984367673610997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988998833312490231481329 2241749124984367673610997)
                ·
                  refine ⟨210163980467284469401031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241749124984367673610997 210163980467284469401031)
                  ·
                    rfl

theorem cell22_1841818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1841818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841818 prefixEnd_1841818 := by exact prefixLift 1841818
  have htrace : WordTrace (prefixWord ++ tailWord_1841818) baseStart_1841818 baseEnd_1841818 := by
    simpa [prefixWord, tailWord_1841818, baseEnd_1841818] using wordTrace_append hprefix tailTrace_1841818
  have hstable : (prefixWord ++ tailWord_1841818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841818).length < 2 ^ (prefixWord ++ tailWord_1841818).sum := by decide
  have hdescent : baseEnd_1841818 < baseStart_1841818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841934 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1841934 : Nat := 118140960795 + 1841934 * 2 ^ 59
def prefixEnd_1841934 : Nat := 4983230072969 + 3 ^ 40 * 1841934 * 2
def baseEnd_1841934 : Nat := 630531650572467772302737

theorem tailTrace_1841934 : CollatzResearch.WordTrace tailWord_1841934 prefixEnd_1841934 630531650572467772302737 := by
  unfold tailWord_1841934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397606513624396265941607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44787234739330113418355237 8397606513624396265941607)
  ·
    refine ⟨12596409770436594398912411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8397606513624396265941607 12596409770436594398912411)
    ·
      refine ⟨18894614655654891598368617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596409770436594398912411 18894614655654891598368617)
      ·
        refine ⟨14170960991741168698776463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18894614655654891598368617 14170960991741168698776463)
        ·
          refine ⟨21256441487611753048164695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14170960991741168698776463 21256441487611753048164695)
          ·
            refine ⟨31884662231417629572247043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21256441487611753048164695 31884662231417629572247043)
            ·
              refine ⟨47826993347126444358370565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31884662231417629572247043 47826993347126444358370565)
              ·
                refine ⟨8967561252586208317194481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47826993347126444358370565 8967561252586208317194481)
                ·
                  refine ⟨6725670939439656237895861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967561252586208317194481 6725670939439656237895861)
                  ·
                    refine ⟨630531650572467772302737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6725670939439656237895861 630531650572467772302737)
                    ·
                      rfl

theorem cell22_1841934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1841934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841934 prefixEnd_1841934 := by exact prefixLift 1841934
  have htrace : WordTrace (prefixWord ++ tailWord_1841934) baseStart_1841934 baseEnd_1841934 := by
    simpa [prefixWord, tailWord_1841934, baseEnd_1841934] using wordTrace_append hprefix tailTrace_1841934
  have hstable : (prefixWord ++ tailWord_1841934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841934).length < 2 ^ (prefixWord ++ tailWord_1841934).sum := by decide
  have hdescent : baseEnd_1841934 < baseStart_1841934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841964 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 6]
def baseStart_1841964 : Nat := 118140960795 + 1841964 * 2 ^ 59
def prefixEnd_1841964 : Nat := 4983230072969 + 3 ^ 40 * 1841964 * 2
def baseEnd_1841964 : Nat := 210180640061852564684215

theorem tailTrace_1841964 : CollatzResearch.WordTrace tailWord_1841964 prefixEnd_1841964 210180640061852564684215 := by
  unfold tailWord_1841964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33590973149443242625562473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44787964199257656834083297 33590973149443242625562473)
  ·
    refine ⟨25193229862082431969171855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33590973149443242625562473 25193229862082431969171855)
    ·
      refine ⟨37789844793123647953757783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193229862082431969171855 37789844793123647953757783)
      ·
        refine ⟨56684767189685471930636675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37789844793123647953757783 56684767189685471930636675)
        ·
          refine ⟨85027150784528207895955013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56684767189685471930636675 85027150784528207895955013)
          ·
            refine ⟨15942590772099038980491565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85027150784528207895955013 15942590772099038980491565)
            ·
              refine ⟨5978471539537139617684337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15942590772099038980491565 5978471539537139617684337)
              ·
                refine ⟨4483853654652854713263253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978471539537139617684337 4483853654652854713263253)
                ·
                  refine ⟨210180640061852564684215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4483853654652854713263253 210180640061852564684215)
                  ·
                    rfl

theorem cell22_1841964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_1841964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841964 prefixEnd_1841964 := by exact prefixLift 1841964
  have htrace : WordTrace (prefixWord ++ tailWord_1841964) baseStart_1841964 baseEnd_1841964 := by
    simpa [prefixWord, tailWord_1841964, baseEnd_1841964] using wordTrace_append hprefix tailTrace_1841964
  have hstable : (prefixWord ++ tailWord_1841964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841964).length < 2 ^ (prefixWord ++ tailWord_1841964).sum := by decide
  have hdescent : baseEnd_1841964 < baseStart_1841964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841983 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 1, 4]
def baseStart_1841983 : Nat := 118140960795 + 1841983 * 2 ^ 59
def prefixEnd_1841983 : Nat := 4983230072969 + 3 ^ 40 * 1841983 * 2
def baseEnd_1841983 : Nat := 630548424273847977827587

theorem tailTrace_1841983 : CollatzResearch.WordTrace tailWord_1841983 prefixEnd_1841983 630548424273847977827587 := by
  unfold tailWord_1841983
  simp only [CollatzResearch.WordTrace]
  refine ⟨67182639285817651496066603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44788426190545100997377735 67182639285817651496066603)
  ·
    refine ⟨100773958928726477244099905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67182639285817651496066603 100773958928726477244099905)
    ·
      refine ⟨75580469196544857933074929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100773958928726477244099905 75580469196544857933074929)
      ·
        refine ⟨56685351897408643449806197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75580469196544857933074929 56685351897408643449806197)
        ·
          refine ⟨5314251740382060323419331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56685351897408643449806197 5314251740382060323419331)
          ·
            refine ⟨7971377610573090485128997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314251740382060323419331 7971377610573090485128997)
            ·
              refine ⟨1494633301982454465961687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7971377610573090485128997 1494633301982454465961687)
              ·
                refine ⟨2241949952973681698942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494633301982454465961687 2241949952973681698942531)
                ·
                  refine ⟨3362924929460522548413797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241949952973681698942531 3362924929460522548413797)
                  ·
                    refine ⟨630548424273847977827587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362924929460522548413797 630548424273847977827587)
                    ·
                      rfl

theorem cell22_1841983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_1841983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1841983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1841983 prefixEnd_1841983 := by exact prefixLift 1841983
  have htrace : WordTrace (prefixWord ++ tailWord_1841983) baseStart_1841983 baseEnd_1841983 := by
    simpa [prefixWord, tailWord_1841983, baseEnd_1841983] using wordTrace_append hprefix tailTrace_1841983
  have hstable : (prefixWord ++ tailWord_1841983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841983).length < 2 ^ (prefixWord ++ tailWord_1841983).sum := by decide
  have hdescent : baseEnd_1841983 < baseStart_1841983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842071 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 5]
def baseStart_1842071 : Nat := 118140960795 + 1842071 * 2 ^ 59
def prefixEnd_1842071 : Nat := 4983230072969 + 3 ^ 40 * 1842071 * 2
def baseEnd_1842071 : Nat := 210192849490748360542439

theorem tailTrace_1842071 : CollatzResearch.WordTrace tailWord_1842071 prefixEnd_1842071 210192849490748360542439 := by
  unfold tailWord_1842071
  simp only [CollatzResearch.WordTrace]
  refine ⟨67185848909498842525270067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44790565939665895016846711 67185848909498842525270067)
  ·
    refine ⟨100778773364248263787905101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67185848909498842525270067 100778773364248263787905101)
    ·
      refine ⟨37792040011593098920464413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100778773364248263787905101 37792040011593098920464413)
      ·
        refine ⟨14172015004347412095174155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37792040011593098920464413 14172015004347412095174155)
        ·
          refine ⟨21258022506521118142761233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14172015004347412095174155 21258022506521118142761233)
          ·
            refine ⟨15943516879890838607070925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21258022506521118142761233 15943516879890838607070925)
            ·
              refine ⟨5978818829959064477651597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15943516879890838607070925 5978818829959064477651597)
              ·
                refine ⟨2242057061234649179119349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978818829959064477651597 2242057061234649179119349)
                ·
                  refine ⟨210192849490748360542439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242057061234649179119349 210192849490748360542439)
                  ·
                    rfl

theorem cell22_1842071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 5].length) (baseStart_1842071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842071 prefixEnd_1842071 := by exact prefixLift 1842071
  have htrace : WordTrace (prefixWord ++ tailWord_1842071) baseStart_1842071 baseEnd_1842071 := by
    simpa [prefixWord, tailWord_1842071, baseEnd_1842071] using wordTrace_append hprefix tailTrace_1842071
  have hstable : (prefixWord ++ tailWord_1842071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842071).length < 2 ^ (prefixWord ++ tailWord_1842071).sum := by decide
  have hdescent : baseEnd_1842071 < baseStart_1842071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842099 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 10]
def baseStart_1842099 : Nat := 118140960795 + 1842099 * 2 ^ 59
def prefixEnd_1842099 : Nat := 4983230072969 + 3 ^ 40 * 1842099 * 2
def baseEnd_1842099 : Nat := 210196044481487447309077

theorem tailTrace_1842099 : CollatzResearch.WordTrace tailWord_1842099 prefixEnd_1842099 210196044481487447309077 := by
  unfold tailWord_1842099
  simp only [CollatzResearch.WordTrace]
  refine ⟨67186870153397403307289351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44791246768931602204859567 67186870153397403307289351)
  ·
    refine ⟨100780305230096104960934027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67186870153397403307289351 100780305230096104960934027)
    ·
      refine ⟨151170457845144157441401041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100780305230096104960934027 151170457845144157441401041)
      ·
        refine ⟨113377843383858118081050781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151170457845144157441401041 113377843383858118081050781)
        ·
          refine ⟨42516691268946794280394043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113377843383858118081050781 42516691268946794280394043)
          ·
            refine ⟨63775036903420191420591065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42516691268946794280394043 63775036903420191420591065)
            ·
              refine ⟨47831277677565143565443299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63775036903420191420591065 47831277677565143565443299)
              ·
                refine ⟨71746916516347715348164949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47831277677565143565443299 71746916516347715348164949)
                ·
                  refine ⟨210196044481487447309077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71746916516347715348164949 210196044481487447309077)
                  ·
                    rfl

theorem cell22_1842099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_1842099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842099 prefixEnd_1842099 := by exact prefixLift 1842099
  have htrace : WordTrace (prefixWord ++ tailWord_1842099) baseStart_1842099 baseEnd_1842099 := by
    simpa [prefixWord, tailWord_1842099, baseEnd_1842099] using wordTrace_append hprefix tailTrace_1842099
  have hstable : (prefixWord ++ tailWord_1842099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842099).length < 2 ^ (prefixWord ++ tailWord_1842099).sum := by decide
  have hdescent : baseEnd_1842099 < baseStart_1842099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842109 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1842109 : Nat := 118140960795 + 1842109 * 2 ^ 59
def prefixEnd_1842109 : Nat := 4983230072969 + 3 ^ 40 * 1842109 * 2
def baseEnd_1842109 : Nat := 630591556648825649177201

theorem tailTrace_1842109 : CollatzResearch.WordTrace tailWord_1842109 prefixEnd_1842109 630591556648825649177201 := by
  unfold tailWord_1842109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67187234883361175015153381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44791489922240783343435587 67187234883361175015153381)
  ·
    refine ⟨12597606540630220315341259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67187234883361175015153381 12597606540630220315341259)
    ·
      refine ⟨18896409810945330473011889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12597606540630220315341259 18896409810945330473011889)
      ·
        refine ⟨14172307358208997854758917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18896409810945330473011889 14172307358208997854758917)
        ·
          refine ⟨2657307629664187097767297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14172307358208997854758917 2657307629664187097767297)
          ·
            refine ⟨1992980722248140323325473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657307629664187097767297 1992980722248140323325473)
            ·
              refine ⟨1494735541686105242494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992980722248140323325473 1494735541686105242494105)
              ·
                refine ⟨1121051656264578931870579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494735541686105242494105 1121051656264578931870579)
                ·
                  refine ⟨1681577484396868397805869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121051656264578931870579 1681577484396868397805869)
                  ·
                    refine ⟨630591556648825649177201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1681577484396868397805869 630591556648825649177201)
                    ·
                      rfl

theorem cell22_1842109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1842109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842109 prefixEnd_1842109 := by exact prefixLift 1842109
  have htrace : WordTrace (prefixWord ++ tailWord_1842109) baseStart_1842109 baseEnd_1842109 := by
    simpa [prefixWord, tailWord_1842109, baseEnd_1842109] using wordTrace_append hprefix tailTrace_1842109
  have hstable : (prefixWord ++ tailWord_1842109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842109).length < 2 ^ (prefixWord ++ tailWord_1842109).sum := by decide
  have hdescent : baseEnd_1842109 < baseStart_1842109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842133 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 6]
def baseStart_1842133 : Nat := 118140960795 + 1842133 * 2 ^ 59
def prefixEnd_1842133 : Nat := 4983230072969 + 3 ^ 40 * 1842133 * 2
def baseEnd_1842133 : Nat := 210199924113099195525709

theorem tailTrace_1842133 : CollatzResearch.WordTrace tailWord_1842133 prefixEnd_1842133 210199924113099195525709 := by
  unfold tailWord_1842133
  simp only [CollatzResearch.WordTrace]
  refine ⟨67188110235274227114027053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44792073490182818076018035 67188110235274227114027053)
  ·
    refine ⟨25195541338227835167760145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67188110235274227114027053 25195541338227835167760145)
    ·
      refine ⟨18896656003670876375820109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25195541338227835167760145 18896656003670876375820109)
      ·
        refine ⟨7086246001376578640932541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18896656003670876375820109 7086246001376578640932541)
        ·
          refine ⟨2657342250516216990349703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7086246001376578640932541 2657342250516216990349703)
          ·
            refine ⟨3986013375774325485524555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657342250516216990349703 3986013375774325485524555)
            ·
              refine ⟨5979020063661488228286833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986013375774325485524555 5979020063661488228286833)
              ·
                refine ⟨4484265047746116171215125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979020063661488228286833 4484265047746116171215125)
                ·
                  refine ⟨210199924113099195525709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4484265047746116171215125 210199924113099195525709)
                  ·
                    rfl

theorem cell22_1842133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_1842133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842133 prefixEnd_1842133 := by exact prefixLift 1842133
  have htrace : WordTrace (prefixWord ++ tailWord_1842133) baseStart_1842133 baseEnd_1842133 := by
    simpa [prefixWord, tailWord_1842133, baseEnd_1842133] using wordTrace_append hprefix tailTrace_1842133
  have hstable : (prefixWord ++ tailWord_1842133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842133).length < 2 ^ (prefixWord ++ tailWord_1842133).sum := by decide
  have hdescent : baseEnd_1842133 < baseStart_1842133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842161 : List Nat := [1, 2, 2, 2, 4, 2, 9]
def baseStart_1842161 : Nat := 118140960795 + 1842161 * 2 ^ 59
def prefixEnd_1842161 : Nat := 4983230072969 + 3 ^ 40 * 1842161 * 2
def baseEnd_1842161 : Nat := 23355902122648698032483

theorem tailTrace_1842161 : CollatzResearch.WordTrace tailWord_1842161 prefixEnd_1842161 23355902122648698032483 := by
  unfold tailWord_1842161
  simp only [CollatzResearch.WordTrace]
  refine ⟨67189131479172787896046337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44792754319448525264030891 67189131479172787896046337)
  ·
    refine ⟨50391848609379590922034753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67189131479172787896046337 50391848609379590922034753)
    ·
      refine ⟨37793886457034693191526065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50391848609379590922034753 37793886457034693191526065)
      ·
        refine ⟨28345414842776019893644549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37793886457034693191526065 28345414842776019893644549)
        ·
          refine ⟨5314765283020503730058353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28345414842776019893644549 5314765283020503730058353)
          ·
            refine ⟨3986073962265377797543765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314765283020503730058353 3986073962265377797543765)
            ·
              refine ⟨23355902122648698032483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3986073962265377797543765 23355902122648698032483)
              ·
                rfl

theorem cell22_1842161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 9].length) (baseStart_1842161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842161 prefixEnd_1842161 := by exact prefixLift 1842161
  have htrace : WordTrace (prefixWord ++ tailWord_1842161) baseStart_1842161 baseEnd_1842161 := by
    simpa [prefixWord, tailWord_1842161, baseEnd_1842161] using wordTrace_append hprefix tailTrace_1842161
  have hstable : (prefixWord ++ tailWord_1842161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842161).length < 2 ^ (prefixWord ++ tailWord_1842161).sum := by decide
  have hdescent : baseEnd_1842161 < baseStart_1842161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842300 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1842300 : Nat := 118140960795 + 1842300 * 2 ^ 59
def prefixEnd_1842300 : Nat := 4983230072969 + 3 ^ 40 * 1842300 * 2
def baseEnd_1842300 : Nat := 630656939852164817651615

theorem tailTrace_1842300 : CollatzResearch.WordTrace tailWord_1842300 prefixEnd_1842300 630656939852164817651615 := by
  unfold tailWord_1842300
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597100612834607317678177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44796134150446143090237569 33597100612834607317678177)
  ·
    refine ⟨25197825459625955488258633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33597100612834607317678177 25197825459625955488258633)
    ·
      refine ⟨18898369094719466616193975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25197825459625955488258633 18898369094719466616193975)
      ·
        refine ⟨28347553642079199924290963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898369094719466616193975 28347553642079199924290963)
        ·
          refine ⟨42521330463118799886436445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28347553642079199924290963 42521330463118799886436445)
          ·
            refine ⟨15945498923669549957413667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42521330463118799886436445 15945498923669549957413667)
            ·
              refine ⟨23918248385504324936120501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945498923669549957413667 23918248385504324936120501)
              ·
                refine ⟨2242335786141030462761297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23918248385504324936120501 2242335786141030462761297)
                ·
                  refine ⟨1681751839605772847070973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242335786141030462761297 1681751839605772847070973)
                  ·
                    refine ⟨630656939852164817651615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1681751839605772847070973 630656939852164817651615)
                    ·
                      rfl

theorem cell22_1842300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1842300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842300 prefixEnd_1842300 := by exact prefixLift 1842300
  have htrace : WordTrace (prefixWord ++ tailWord_1842300) baseStart_1842300 baseEnd_1842300 := by
    simpa [prefixWord, tailWord_1842300, baseEnd_1842300] using wordTrace_append hprefix tailTrace_1842300
  have hstable : (prefixWord ++ tailWord_1842300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842300).length < 2 ^ (prefixWord ++ tailWord_1842300).sum := by decide
  have hdescent : baseEnd_1842300 < baseStart_1842300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842334 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1842334 : Nat := 118140960795 + 1842334 * 2 ^ 59
def prefixEnd_1842334 : Nat := 4983230072969 + 3 ^ 40 * 1842334 * 2
def baseEnd_1842334 : Nat := 630668578747000062301511

theorem tailTrace_1842334 : CollatzResearch.WordTrace tailWord_1842334 prefixEnd_1842334 630668578747000062301511 := by
  unfold tailWord_1842334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399430163443254805261757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44796960871697358961396037 8399430163443254805261757)
  ·
    refine ⟨3149786311291220551973159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8399430163443254805261757 3149786311291220551973159)
    ·
      refine ⟨4724679466936830827959739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149786311291220551973159 4724679466936830827959739)
      ·
        refine ⟨7087019200405246241939609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4724679466936830827959739 7087019200405246241939609)
        ·
          refine ⟨5315264400303934681454707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7087019200405246241939609 5315264400303934681454707)
          ·
            refine ⟨7972896600455902022182061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315264400303934681454707 7972896600455902022182061)
            ·
              refine ⟨2989836225170963258318273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7972896600455902022182061 2989836225170963258318273)
              ·
                refine ⟨2242377168878222443738705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989836225170963258318273 2242377168878222443738705)
                ·
                  refine ⟨1681782876658666832804029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242377168878222443738705 1681782876658666832804029)
                  ·
                    refine ⟨630668578747000062301511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1681782876658666832804029 630668578747000062301511)
                    ·
                      rfl

theorem cell22_1842334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1842334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842334 prefixEnd_1842334 := by exact prefixLift 1842334
  have htrace : WordTrace (prefixWord ++ tailWord_1842334) baseStart_1842334 baseEnd_1842334 := by
    simpa [prefixWord, tailWord_1842334, baseEnd_1842334] using wordTrace_append hprefix tailTrace_1842334
  have hstable : (prefixWord ++ tailWord_1842334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842334).length < 2 ^ (prefixWord ++ tailWord_1842334).sum := by decide
  have hdescent : baseEnd_1842334 < baseStart_1842334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842435 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_1842435 : Nat := 118140960795 + 1842435 * 2 ^ 59
def prefixEnd_1842435 : Nat := 4983230072969 + 3 ^ 40 * 1842435 * 2
def baseEnd_1842435 : Nat := 630703153111069465526201

theorem tailTrace_1842435 : CollatzResearch.WordTrace tailWord_1842435 prefixEnd_1842435 630703153111069465526201 := by
  unfold tailWord_1842435
  simp only [CollatzResearch.WordTrace]
  refine ⟨67199125080180132691520759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44799416720120088461013839 67199125080180132691520759)
  ·
    refine ⟨100798687620270199037281139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67199125080180132691520759 100798687620270199037281139)
    ·
      refine ⟨151198031430405298555921709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100798687620270199037281139 151198031430405298555921709)
      ·
        refine ⟨56699261786401986958470641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151198031430405298555921709 56699261786401986958470641)
        ·
          refine ⟨42524446339801490218852981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56699261786401986958470641 42524446339801490218852981)
          ·
            refine ⟨3986666844356389708017467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42524446339801490218852981 3986666844356389708017467)
            ·
              refine ⟨5980000266534584562026201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986666844356389708017467 5980000266534584562026201)
              ·
                refine ⟨4485000199900938421519651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980000266534584562026201 4485000199900938421519651)
                ·
                  refine ⟨6727500299851407632279477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4485000199900938421519651 6727500299851407632279477)
                  ·
                    refine ⟨630703153111069465526201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6727500299851407632279477 630703153111069465526201)
                    ·
                      rfl

theorem cell22_1842435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_1842435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842435 prefixEnd_1842435 := by exact prefixLift 1842435
  have htrace : WordTrace (prefixWord ++ tailWord_1842435) baseStart_1842435 baseEnd_1842435 := by
    simpa [prefixWord, tailWord_1842435, baseEnd_1842435] using wordTrace_append hprefix tailTrace_1842435
  have hstable : (prefixWord ++ tailWord_1842435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842435).length < 2 ^ (prefixWord ++ tailWord_1842435).sum := by decide
  have hdescent : baseEnd_1842435 < baseStart_1842435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842482 : List Nat := [3, 2, 1, 1, 4, 2, 3, 6]
def baseStart_1842482 : Nat := 118140960795 + 1842482 * 2 ^ 59
def prefixEnd_1842482 : Nat := 4983230072969 + 3 ^ 40 * 1842482 * 2
def baseEnd_1842482 : Nat := 70079915796841889955673

theorem tailTrace_1842482 : CollatzResearch.WordTrace tailWord_1842482 prefixEnd_1842482 70079915796841889955673 := by
  unfold tailWord_1842482
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800209827752464929620425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44800559540673239812321133 16800209827752464929620425)
  ·
    refine ⟨12600157370814348697215319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16800209827752464929620425 12600157370814348697215319)
    ·
      refine ⟨18900236056221523045822979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600157370814348697215319 18900236056221523045822979)
      ·
        refine ⟨28350354084332284568734469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18900236056221523045822979 28350354084332284568734469)
        ·
          refine ⟨5315691390812303356637713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28350354084332284568734469 5315691390812303356637713)
          ·
            refine ⟨3986768543109227517478285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5315691390812303356637713 3986768543109227517478285)
            ·
              refine ⟨1495038203665960319054357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986768543109227517478285 1495038203665960319054357)
              ·
                refine ⟨70079915796841889955673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1495038203665960319054357 70079915796841889955673)
                ·
                  rfl

theorem cell22_1842482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_1842482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842482 prefixEnd_1842482 := by exact prefixLift 1842482
  have htrace : WordTrace (prefixWord ++ tailWord_1842482) baseStart_1842482 baseEnd_1842482 := by
    simpa [prefixWord, tailWord_1842482, baseEnd_1842482] using wordTrace_append hprefix tailTrace_1842482
  have hstable : (prefixWord ++ tailWord_1842482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842482).length < 2 ^ (prefixWord ++ tailWord_1842482).sum := by decide
  have hdescent : baseEnd_1842482 < baseStart_1842482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842510 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_1842510 : Nat := 118140960795 + 1842510 * 2 ^ 59
def prefixEnd_1842510 : Nat := 4983230072969 + 3 ^ 40 * 1842510 * 2
def baseEnd_1842510 : Nat := 210242942381264756633657

theorem tailTrace_1842510 : CollatzResearch.WordTrace tailWord_1842510 prefixEnd_1842510 210242942381264756633657 := by
  unfold tailWord_1842510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400232569363552562562623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44801240369938947000333989 8400232569363552562562623)
  ·
    refine ⟨12600348854045328843843935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8400232569363552562562623 12600348854045328843843935)
    ·
      refine ⟨18900523281067993265765903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600348854045328843843935 18900523281067993265765903)
      ·
        refine ⟨28350784921601989898648855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18900523281067993265765903 28350784921601989898648855)
        ·
          refine ⟨42526177382402984847973283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28350784921601989898648855 42526177382402984847973283)
          ·
            refine ⟨63789266073604477271959925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42526177382402984847973283 63789266073604477271959925)
            ·
              refine ⟨5980243694400419744246243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63789266073604477271959925 5980243694400419744246243)
              ·
                refine ⟨8970365541600629616369365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980243694400419744246243 8970365541600629616369365)
                ·
                  refine ⟨210242942381264756633657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8970365541600629616369365 210242942381264756633657)
                  ·
                    rfl

theorem cell22_1842510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_1842510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842510 prefixEnd_1842510 := by exact prefixLift 1842510
  have htrace : WordTrace (prefixWord ++ tailWord_1842510) baseStart_1842510 baseEnd_1842510 := by
    simpa [prefixWord, tailWord_1842510, baseEnd_1842510] using wordTrace_append hprefix tailTrace_1842510
  have hstable : (prefixWord ++ tailWord_1842510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842510).length < 2 ^ (prefixWord ++ tailWord_1842510).sum := by decide
  have hdescent : baseEnd_1842510 < baseStart_1842510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842557 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1842557 : Nat := 118140960795 + 1842557 * 2 ^ 59
def prefixEnd_1842557 : Nat := 4983230072969 + 3 ^ 40 * 1842557 * 2
def baseEnd_1842557 : Nat := 630744916204301813975827

theorem tailTrace_1842557 : CollatzResearch.WordTrace tailWord_1842557 prefixEnd_1842557 630744916204301813975827 := by
  unfold tailWord_1842557
  simp only [CollatzResearch.WordTrace]
  refine ⟨67203574785738147527461925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44802383190492098351641283 67203574785738147527461925)
  ·
    refine ⟨12600670272325902661399111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67203574785738147527461925 12600670272325902661399111)
    ·
      refine ⟨18901005408488853992098667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600670272325902661399111 18901005408488853992098667)
      ·
        refine ⟨28351508112733280988148001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18901005408488853992098667 28351508112733280988148001)
        ·
          refine ⟨21263631084549960741111001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28351508112733280988148001 21263631084549960741111001)
          ·
            refine ⟨15947723313412470555833251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21263631084549960741111001 15947723313412470555833251)
            ·
              refine ⟨23921584970118705833749877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15947723313412470555833251 23921584970118705833749877)
              ·
                refine ⟨2242648590948628671914051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23921584970118705833749877 2242648590948628671914051)
                ·
                  refine ⟨3363972886422943007871077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242648590948628671914051 3363972886422943007871077)
                  ·
                    refine ⟨630744916204301813975827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363972886422943007871077 630744916204301813975827)
                    ·
                      rfl

theorem cell22_1842557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1842557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842557 prefixEnd_1842557 := by exact prefixLift 1842557
  have htrace : WordTrace (prefixWord ++ tailWord_1842557) baseStart_1842557 baseEnd_1842557 := by
    simpa [prefixWord, tailWord_1842557, baseEnd_1842557] using wordTrace_append hprefix tailTrace_1842557
  have hstable : (prefixWord ++ tailWord_1842557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842557).length < 2 ^ (prefixWord ++ tailWord_1842557).sum := by decide
  have hdescent : baseEnd_1842557 < baseStart_1842557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842578 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1842578 : Nat := 118140960795 + 1842578 * 2 ^ 59
def prefixEnd_1842578 : Nat := 4983230072969 + 3 ^ 40 * 1842578 * 2
def baseEnd_1842578 : Nat := 210250701644488253066921

theorem tailTrace_1842578 : CollatzResearch.WordTrace tailWord_1842578 prefixEnd_1842578 210250701644488253066921 := by
  unfold tailWord_1842578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16801085179665517028494097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44802893812441378742650925 16801085179665517028494097)
  ·
    refine ⟨12600813884749137771370573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16801085179665517028494097 12600813884749137771370573)
    ·
      refine ⟨4725305206780926664263965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12600813884749137771370573 4725305206780926664263965)
      ·
        refine ⟨1771989452542847499098987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4725305206780926664263965 1771989452542847499098987)
        ·
          refine ⟨2657984178814271248648481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771989452542847499098987 2657984178814271248648481)
          ·
            refine ⟨1993488134110703436486361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657984178814271248648481 1993488134110703436486361)
            ·
              refine ⟨1495116100583027577364771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993488134110703436486361 1495116100583027577364771)
              ·
                refine ⟨2242674150874541366047157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495116100583027577364771 2242674150874541366047157)
                ·
                  refine ⟨210250701644488253066921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242674150874541366047157 210250701644488253066921)
                  ·
                    rfl

theorem cell22_1842578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1842578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842578 prefixEnd_1842578 := by exact prefixLift 1842578
  have htrace : WordTrace (prefixWord ++ tailWord_1842578) baseStart_1842578 baseEnd_1842578 := by
    simpa [prefixWord, tailWord_1842578, baseEnd_1842578] using wordTrace_append hprefix tailTrace_1842578
  have hstable : (prefixWord ++ tailWord_1842578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842578).length < 2 ^ (prefixWord ++ tailWord_1842578).sum := by decide
  have hdescent : baseEnd_1842578 < baseStart_1842578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842617 : List Nat := [1, 2, 1, 4, 5, 9]
def baseStart_1842617 : Nat := 118140960795 + 1842617 * 2 ^ 59
def prefixEnd_1842617 : Nat := 4983230072969 + 3 ^ 40 * 1842617 * 2
def baseEnd_1842617 : Nat := 7787227844820761203403

theorem tailTrace_1842617 : CollatzResearch.WordTrace tailWord_1842617 prefixEnd_1842617 7787227844820761203403 := by
  unfold tailWord_1842617
  simp only [CollatzResearch.WordTrace]
  refine ⟨67205763165520777774646105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44803842110347185183097403 67205763165520777774646105)
  ·
    refine ⟨50404322374140583330984579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67205763165520777774646105 50404322374140583330984579)
    ·
      refine ⟨75606483561210874996476869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50404322374140583330984579 75606483561210874996476869)
      ·
        refine ⟨14176215667727039061839413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75606483561210874996476869 14176215667727039061839413)
        ·
          refine ⟨1329020218849409912047445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14176215667727039061839413 1329020218849409912047445)
          ·
            refine ⟨7787227844820761203403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1329020218849409912047445 7787227844820761203403)
            ·
              rfl

theorem cell22_1842617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 9].length) (baseStart_1842617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842617 prefixEnd_1842617 := by exact prefixLift 1842617
  have htrace : WordTrace (prefixWord ++ tailWord_1842617) baseStart_1842617 baseEnd_1842617 := by
    simpa [prefixWord, tailWord_1842617, baseEnd_1842617] using wordTrace_append hprefix tailTrace_1842617
  have hstable : (prefixWord ++ tailWord_1842617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842617).length < 2 ^ (prefixWord ++ tailWord_1842617).sum := by decide
  have hdescent : baseEnd_1842617 < baseStart_1842617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842649 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_1842649 : Nat := 118140960795 + 1842649 * 2 ^ 59
def prefixEnd_1842649 : Nat := 4983230072969 + 3 ^ 40 * 1842649 * 2
def baseEnd_1842649 : Nat := 630776409684444240675545

theorem tailTrace_1842649 : CollatzResearch.WordTrace tailWord_1842649 prefixEnd_1842649 630776409684444240675545 := by
  unfold tailWord_1842649
  simp only [CollatzResearch.WordTrace]
  refine ⟨67206930301404847239811001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44804620200936564826540667 67206930301404847239811001)
  ·
    refine ⟨50405197726053635429858251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67206930301404847239811001 50405197726053635429858251)
    ·
      refine ⟨75607796589080453144787377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50405197726053635429858251 75607796589080453144787377)
      ·
        refine ⟨56705847441810339858590533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75607796589080453144787377 56705847441810339858590533)
        ·
          refine ⟨10632346395339438723485725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56705847441810339858590533 10632346395339438723485725)
          ·
            refine ⟨3987129898252289521307147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10632346395339438723485725 3987129898252289521307147)
            ·
              refine ⟨5980694847378434281960721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987129898252289521307147 5980694847378434281960721)
              ·
                refine ⟨4485521135533825711470541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980694847378434281960721 4485521135533825711470541)
                ·
                  refine ⟨1682070425825184641801453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4485521135533825711470541 1682070425825184641801453)
                  ·
                    refine ⟨630776409684444240675545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682070425825184641801453 630776409684444240675545)
                    ·
                      rfl

theorem cell22_1842649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_1842649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842649 prefixEnd_1842649 := by exact prefixLift 1842649
  have htrace : WordTrace (prefixWord ++ tailWord_1842649) baseStart_1842649 baseEnd_1842649 := by
    simpa [prefixWord, tailWord_1842649, baseEnd_1842649] using wordTrace_append hprefix tailTrace_1842649
  have hstable : (prefixWord ++ tailWord_1842649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842649).length < 2 ^ (prefixWord ++ tailWord_1842649).sum := by decide
  have hdescent : baseEnd_1842649 < baseStart_1842649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842707 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 6]
def baseStart_1842707 : Nat := 118140960795 + 1842707 * 2 ^ 59
def prefixEnd_1842707 : Nat := 4983230072969 + 3 ^ 40 * 1842707 * 2
def baseEnd_1842707 : Nat := 210265421423250474241789

theorem tailTrace_1842707 : CollatzResearch.WordTrace tailWord_1842707 prefixEnd_1842707 210265421423250474241789 := by
  unfold tailWord_1842707
  simp only [CollatzResearch.WordTrace]
  refine ⟨67209045735194723145422375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44806030490129815430281583 67209045735194723145422375)
  ·
    refine ⟨100813568602792084718133563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67209045735194723145422375 100813568602792084718133563)
    ·
      refine ⟨151220352904188127077200345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100813568602792084718133563 151220352904188127077200345)
      ·
        refine ⟨113415264678141095307900259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151220352904188127077200345 113415264678141095307900259)
        ·
          refine ⟨170122897017211642961850389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113415264678141095307900259 170122897017211642961850389)
          ·
            refine ⟨7974510797681795763836737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170122897017211642961850389 7974510797681795763836737)
            ·
              refine ⟨5980883098261346822877553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974510797681795763836737 5980883098261346822877553)
              ·
                refine ⟨4485662323696010117158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980883098261346822877553 4485662323696010117158165)
                ·
                  refine ⟨210265421423250474241789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4485662323696010117158165 210265421423250474241789)
                  ·
                    rfl

theorem cell22_1842707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_1842707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842707 prefixEnd_1842707 := by exact prefixLift 1842707
  have htrace : WordTrace (prefixWord ++ tailWord_1842707) baseStart_1842707 baseEnd_1842707 := by
    simpa [prefixWord, tailWord_1842707, baseEnd_1842707] using wordTrace_append hprefix tailTrace_1842707
  have hstable : (prefixWord ++ tailWord_1842707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842707).length < 2 ^ (prefixWord ++ tailWord_1842707).sum := by decide
  have hdescent : baseEnd_1842707 < baseStart_1842707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842709 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1842709 : Nat := 118140960795 + 1842709 * 2 ^ 59
def prefixEnd_1842709 : Nat := 4983230072969 + 3 ^ 40 * 1842709 * 2
def baseEnd_1842709 : Nat := 630796948910624084175361

theorem tailTrace_1842709 : CollatzResearch.WordTrace tailWord_1842709 prefixEnd_1842709 630796948910624084175361 := by
  unfold tailWord_1842709
  simp only [CollatzResearch.WordTrace]
  refine ⟨67209118681187477486995181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44806079120791651657996787 67209118681187477486995181)
  ·
    refine ⟨25203419505445304057623193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67209118681187477486995181 25203419505445304057623193)
    ·
      refine ⟨18902564629083978043217395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25203419505445304057623193 18902564629083978043217395)
      ·
        refine ⟨28353846943625967064826093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18902564629083978043217395 28353846943625967064826093)
        ·
          refine ⟨10632692603859737649309785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28353846943625967064826093 10632692603859737649309785)
          ·
            refine ⟨7974519452894803236982339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10632692603859737649309785 7974519452894803236982339)
            ·
              refine ⟨11961779179342204855473509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974519452894803236982339 11961779179342204855473509)
              ·
                refine ⟨2242833596126663410401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11961779179342204855473509 2242833596126663410401283)
                ·
                  refine ⟨3364250394189995115601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242833596126663410401283 3364250394189995115601925)
                  ·
                    refine ⟨630796948910624084175361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364250394189995115601925 630796948910624084175361)
                    ·
                      rfl

theorem cell22_1842709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1842709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842709 prefixEnd_1842709 := by exact prefixLift 1842709
  have htrace : WordTrace (prefixWord ++ tailWord_1842709) baseStart_1842709 baseEnd_1842709 := by
    simpa [prefixWord, tailWord_1842709, baseEnd_1842709] using wordTrace_append hprefix tailTrace_1842709
  have hstable : (prefixWord ++ tailWord_1842709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842709).length < 2 ^ (prefixWord ++ tailWord_1842709).sum := by decide
  have hdescent : baseEnd_1842709 < baseStart_1842709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842739 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 4, 3]
def baseStart_1842739 : Nat := 118140960795 + 1842739 * 2 ^ 59
def prefixEnd_1842739 : Nat := 4983230072969 + 3 ^ 40 * 1842739 * 2
def baseEnd_1842739 : Nat := 630807218523714005925269

theorem tailTrace_1842739 : CollatzResearch.WordTrace tailWord_1842739 prefixEnd_1842739 630807218523714005925269 := by
  unfold tailWord_1842739
  simp only [CollatzResearch.WordTrace]
  refine ⟨67210212871078792610587271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44806808580719195073724847 67210212871078792610587271)
  ·
    refine ⟨100815319306618188915880907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67210212871078792610587271 100815319306618188915880907)
    ·
      refine ⟨151222978959927283373821361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100815319306618188915880907 151222978959927283373821361)
      ·
        refine ⟨113417234219945462530366021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151222978959927283373821361 113417234219945462530366021)
        ·
          refine ⟨21265731416239774224443629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113417234219945462530366021 21265731416239774224443629)
          ·
            refine ⟨7974649281089915334166361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21265731416239774224443629 7974649281089915334166361)
            ·
              refine ⟨5980986960817436500624771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974649281089915334166361 5980986960817436500624771)
              ·
                refine ⟨8971480441226154750937157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980986960817436500624771 8971480441226154750937157)
                ·
                  refine ⟨1682152582729904015800717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8971480441226154750937157 1682152582729904015800717)
                  ·
                    refine ⟨630807218523714005925269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682152582729904015800717 630807218523714005925269)
                    ·
                      rfl

theorem cell22_1842739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 3].length) (baseStart_1842739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842739 prefixEnd_1842739 := by exact prefixLift 1842739
  have htrace : WordTrace (prefixWord ++ tailWord_1842739) baseStart_1842739 baseEnd_1842739 := by
    simpa [prefixWord, tailWord_1842739, baseEnd_1842739] using wordTrace_append hprefix tailTrace_1842739
  have hstable : (prefixWord ++ tailWord_1842739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842739).length < 2 ^ (prefixWord ++ tailWord_1842739).sum := by decide
  have hdescent : baseEnd_1842739 < baseStart_1842739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842846 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1842846 : Nat := 118140960795 + 1842846 * 2 ^ 59
def prefixEnd_1842846 : Nat := 4983230072969 + 3 ^ 40 * 1842846 * 2
def baseEnd_1842846 : Nat := 630843846810401393499941

theorem tailTrace_1842846 : CollatzResearch.WordTrace tailWord_1842846 prefixEnd_1842846 630843846810401393499941 := by
  unfold tailWord_1842846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401764435211393735591549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44809410321127433256488261 8401764435211393735591549)
  ·
    refine ⟨3150661663204272650846831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8401764435211393735591549 3150661663204272650846831)
    ·
      refine ⟨4725992494806408976270247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150661663204272650846831 4725992494806408976270247)
      ·
        refine ⟨7088988742209613464405371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725992494806408976270247 7088988742209613464405371)
        ·
          refine ⟨10633483113314420196608057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088988742209613464405371 10633483113314420196608057)
          ·
            refine ⟨7975112334985815147456043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633483113314420196608057 7975112334985815147456043)
            ·
              refine ⟨11962668502478722721184065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975112334985815147456043 11962668502478722721184065)
              ·
                refine ⟨8972001376859042040888049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962668502478722721184065 8972001376859042040888049)
                ·
                  refine ⟨6729001032644281530666037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972001376859042040888049 6729001032644281530666037)
                  ·
                    refine ⟨630843846810401393499941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6729001032644281530666037 630843846810401393499941)
                    ·
                      rfl

theorem cell22_1842846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1842846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842846 prefixEnd_1842846 := by exact prefixLift 1842846
  have htrace : WordTrace (prefixWord ++ tailWord_1842846) baseStart_1842846 baseEnd_1842846 := by
    simpa [prefixWord, tailWord_1842846, baseEnd_1842846] using wordTrace_append hprefix tailTrace_1842846
  have hstable : (prefixWord ++ tailWord_1842846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842846).length < 2 ^ (prefixWord ++ tailWord_1842846).sum := by decide
  have hdescent : baseEnd_1842846 < baseStart_1842846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842878 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1842878 : Nat := 118140960795 + 1842878 * 2 ^ 59
def prefixEnd_1842878 : Nat := 4983230072969 + 3 ^ 40 * 1842878 * 2
def baseEnd_1842878 : Nat := 630854801064363976699843

theorem tailTrace_1842878 : CollatzResearch.WordTrace tailWord_1842878 prefixEnd_1842878 630854801064363976699843 := by
  unfold tailWord_1842878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401910327196902418737161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44810188411716812899931525 8401910327196902418737161)
  ·
    refine ⟨6301432745397676814052871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8401910327196902418737161 6301432745397676814052871)
    ·
      refine ⟨9452149118096515221079307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301432745397676814052871 9452149118096515221079307)
      ·
        refine ⟨14178223677144772831618961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452149118096515221079307 14178223677144772831618961)
        ·
          refine ⟨10633667757858579623714221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178223677144772831618961 10633667757858579623714221)
          ·
            refine ⟨3987625409196967358892833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10633667757858579623714221 3987625409196967358892833)
            ·
              refine ⟨2990719056897725519169625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987625409196967358892833 2990719056897725519169625)
              ·
                refine ⟨2243039292673294139377219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990719056897725519169625 2243039292673294139377219)
                ·
                  refine ⟨3364558939009941209065829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243039292673294139377219 3364558939009941209065829)
                  ·
                    refine ⟨630854801064363976699843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364558939009941209065829 630854801064363976699843)
                    ·
                      rfl

theorem cell22_1842878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1842878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842878 prefixEnd_1842878 := by exact prefixLift 1842878
  have htrace : WordTrace (prefixWord ++ tailWord_1842878) baseStart_1842878 baseEnd_1842878 := by
    simpa [prefixWord, tailWord_1842878, baseEnd_1842878] using wordTrace_append hprefix tailTrace_1842878
  have hstable : (prefixWord ++ tailWord_1842878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842878).length < 2 ^ (prefixWord ++ tailWord_1842878).sum := by decide
  have hdescent : baseEnd_1842878 < baseStart_1842878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842906 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1842906 : Nat := 118140960795 + 1842906 * 2 ^ 59
def prefixEnd_1842906 : Nat := 4983230072969 + 3 ^ 40 * 1842906 * 2
def baseEnd_1842906 : Nat := 630864386036581236999757

theorem tailTrace_1842906 : CollatzResearch.WordTrace tailWord_1842906 prefixEnd_1842906 630864386036581236999757 := by
  unfold tailWord_1842906
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804075965368445032979143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44810869240982520087944381 16804075965368445032979143)
  ·
    refine ⟨25206113948052667549468715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804075965368445032979143 25206113948052667549468715)
    ·
      refine ⟨37809170922079001324203073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25206113948052667549468715 37809170922079001324203073)
      ·
        refine ⟨28356878191559250993152305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37809170922079001324203073 28356878191559250993152305)
        ·
          refine ⟨21267658643669438244864229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28356878191559250993152305 21267658643669438244864229)
          ·
            refine ⟨3987685995688019670912043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21267658643669438244864229 3987685995688019670912043)
            ·
              refine ⟨5981528993532029506368065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987685995688019670912043 5981528993532029506368065)
              ·
                refine ⟨4486146745149022129776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981528993532029506368065 4486146745149022129776049)
                ·
                  refine ⟨3364610058861766597332037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486146745149022129776049 3364610058861766597332037)
                  ·
                    refine ⟨630864386036581236999757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364610058861766597332037 630864386036581236999757)
                    ·
                      rfl

theorem cell22_1842906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1842906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842906 prefixEnd_1842906 := by exact prefixLift 1842906
  have htrace : WordTrace (prefixWord ++ tailWord_1842906) baseStart_1842906 baseEnd_1842906 := by
    simpa [prefixWord, tailWord_1842906, baseEnd_1842906] using wordTrace_append hprefix tailTrace_1842906
  have hstable : (prefixWord ++ tailWord_1842906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842906).length < 2 ^ (prefixWord ++ tailWord_1842906).sum := by decide
  have hdescent : baseEnd_1842906 < baseStart_1842906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842925 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1842925 : Nat := 118140960795 + 1842925 * 2 ^ 59
def prefixEnd_1842925 : Nat := 4983230072969 + 3 ^ 40 * 1842925 * 2
def baseEnd_1842925 : Nat := 630870890124871520774699

theorem tailTrace_1842925 : CollatzResearch.WordTrace tailWord_1842925 prefixEnd_1842925 630870890124871520774699 := by
  unfold tailWord_1842925
  simp only [CollatzResearch.WordTrace]
  refine ⟨67216996848404946376858229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44811331232269964251238819 67216996848404946376858229)
  ·
    refine ⟨6301593454537963722830459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67216996848404946376858229 6301593454537963722830459)
    ·
      refine ⟨9452390181806945584245689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301593454537963722830459 9452390181806945584245689)
      ·
        refine ⟨7089292636355209188184267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9452390181806945584245689 7089292636355209188184267)
        ·
          refine ⟨10633938954532813782276401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089292636355209188184267 10633938954532813782276401)
          ·
            refine ⟨7975454215899610336707301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633938954532813782276401 7975454215899610336707301)
            ·
              refine ⟨1495397665481176938132619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7975454215899610336707301 1495397665481176938132619)
              ·
                refine ⟨2243096498221765407198929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495397665481176938132619 2243096498221765407198929)
                ·
                  refine ⟨1682322373666324055399197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243096498221765407198929 1682322373666324055399197)
                  ·
                    refine ⟨630870890124871520774699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682322373666324055399197 630870890124871520774699)
                    ·
                      rfl

theorem cell22_1842925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1842925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842925 prefixEnd_1842925 := by exact prefixLift 1842925
  have htrace : WordTrace (prefixWord ++ tailWord_1842925) baseStart_1842925 baseEnd_1842925 := by
    simpa [prefixWord, tailWord_1842925, baseEnd_1842925] using wordTrace_append hprefix tailTrace_1842925
  have hstable : (prefixWord ++ tailWord_1842925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842925).length < 2 ^ (prefixWord ++ tailWord_1842925).sum := by decide
  have hdescent : baseEnd_1842925 < baseStart_1842925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842953 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_1842953 : Nat := 118140960795 + 1842953 * 2 ^ 59
def prefixEnd_1842953 : Nat := 4983230072969 + 3 ^ 40 * 1842953 * 2
def baseEnd_1842953 : Nat := 630880475097088781074613

theorem tailTrace_1842953 : CollatzResearch.WordTrace tailWord_1842953 prefixEnd_1842953 630880475097088781074613 := by
  unfold tailWord_1842953
  simp only [CollatzResearch.WordTrace]
  refine ⟨67218018092303507158877513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44812012061535671439251675 67218018092303507158877513)
  ·
    refine ⟨50413513569227630369158135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67218018092303507158877513 50413513569227630369158135)
    ·
      refine ⟨75620270353841445553737203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50413513569227630369158135 75620270353841445553737203)
      ·
        refine ⟨113430405530762168330605805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75620270353841445553737203 113430405530762168330605805)
        ·
          refine ⟨42536402074035813123977177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113430405530762168330605805 42536402074035813123977177)
          ·
            refine ⟨31902301555526859842982883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42536402074035813123977177 31902301555526859842982883)
            ·
              refine ⟨47853452333290289764474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31902301555526859842982883 47853452333290289764474325)
              ·
                refine ⟨1121565289061491166354867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47853452333290289764474325 1121565289061491166354867)
                ·
                  refine ⟨1682347933592236749532301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121565289061491166354867 1682347933592236749532301)
                  ·
                    refine ⟨630880475097088781074613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682347933592236749532301 630880475097088781074613)
                    ·
                      rfl

theorem cell22_1842953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_1842953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842953 prefixEnd_1842953 := by exact prefixLift 1842953
  have htrace : WordTrace (prefixWord ++ tailWord_1842953) baseStart_1842953 baseEnd_1842953 := by
    simpa [prefixWord, tailWord_1842953, baseEnd_1842953] using wordTrace_append hprefix tailTrace_1842953
  have hstable : (prefixWord ++ tailWord_1842953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842953).length < 2 ^ (prefixWord ++ tailWord_1842953).sum := by decide
  have hdescent : baseEnd_1842953 < baseStart_1842953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842970 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_1842970 : Nat := 118140960795 + 1842970 * 2 ^ 59
def prefixEnd_1842970 : Nat := 4983230072969 + 3 ^ 40 * 1842970 * 2
def baseEnd_1842970 : Nat := 630886294544506403399561

theorem tailTrace_1842970 : CollatzResearch.WordTrace tailWord_1842970 prefixEnd_1842970 630886294544506403399561 := by
  unfold tailWord_1842970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804659533310479765561591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44812425422161279374830909 16804659533310479765561591)
  ·
    refine ⟨25206989299965719648342387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804659533310479765561591 25206989299965719648342387)
    ·
      refine ⟨37810483949948579472513581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25206989299965719648342387 37810483949948579472513581)
      ·
        refine ⟨14178931481230717302192593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37810483949948579472513581 14178931481230717302192593)
        ·
          refine ⟨10634198610923037976644445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178931481230717302192593 10634198610923037976644445)
          ·
            refine ⟨3987824479096139241241667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10634198610923037976644445 3987824479096139241241667)
            ·
              refine ⟨5981736718644208861862501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987824479096139241241667 5981736718644208861862501)
              ·
                refine ⟨1121575634745789161599219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5981736718644208861862501 1121575634745789161599219)
                ·
                  refine ⟨1682363452118683742398829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121575634745789161599219 1682363452118683742398829)
                  ·
                    refine ⟨630886294544506403399561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682363452118683742398829 630886294544506403399561)
                    ·
                      rfl

theorem cell22_1842970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_1842970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842970 prefixEnd_1842970 := by exact prefixLift 1842970
  have htrace : WordTrace (prefixWord ++ tailWord_1842970) baseStart_1842970 baseEnd_1842970 := by
    simpa [prefixWord, tailWord_1842970, baseEnd_1842970] using wordTrace_append hprefix tailTrace_1842970
  have hstable : (prefixWord ++ tailWord_1842970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842970).length < 2 ^ (prefixWord ++ tailWord_1842970).sum := by decide
  have hdescent : baseEnd_1842970 < baseStart_1842970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842981 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1842981 : Nat := 118140960795 + 1842981 * 2 ^ 59
def prefixEnd_1842981 : Nat := 4983230072969 + 3 ^ 40 * 1842981 * 2
def baseEnd_1842981 : Nat := 630890060069306041374527

theorem tailTrace_1842981 : CollatzResearch.WordTrace tailWord_1842981 prefixEnd_1842981 630890060069306041374527 := by
  unfold tailWord_1842981
  simp only [CollatzResearch.WordTrace]
  refine ⟨67219039336202067940896797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44812692890801378627264531 67219039336202067940896797)
  ·
    refine ⟨25207139751075775477836299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67219039336202067940896797 25207139751075775477836299)
    ·
      refine ⟨37810709626613663216754449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25207139751075775477836299 37810709626613663216754449)
      ·
        refine ⟨28358032219960247412565837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37810709626613663216754449 28358032219960247412565837)
        ·
          refine ⟨10634262082485092779712189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28358032219960247412565837 10634262082485092779712189)
          ·
            refine ⟨3987848280931909792392071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10634262082485092779712189 3987848280931909792392071)
            ·
              refine ⟨5981772421397864688588107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987848280931909792392071 5981772421397864688588107)
              ·
                refine ⟨8972658632096797032882161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981772421397864688588107 8972658632096797032882161)
                ·
                  refine ⟨6729493974072597774661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972658632096797032882161 6729493974072597774661621)
                  ·
                    refine ⟨630890060069306041374527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6729493974072597774661621 630890060069306041374527)
                    ·
                      rfl

theorem cell22_1842981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1842981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1842981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1842981 prefixEnd_1842981 := by exact prefixLift 1842981
  have htrace : WordTrace (prefixWord ++ tailWord_1842981) baseStart_1842981 baseEnd_1842981 := by
    simpa [prefixWord, tailWord_1842981, baseEnd_1842981] using wordTrace_append hprefix tailTrace_1842981
  have hstable : (prefixWord ++ tailWord_1842981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842981).length < 2 ^ (prefixWord ++ tailWord_1842981).sum := by decide
  have hdescent : baseEnd_1842981 < baseStart_1842981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843028 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1843028 : Nat := 118140960795 + 1843028 * 2 ^ 59
def prefixEnd_1843028 : Nat := 4983230072969 + 3 ^ 40 * 1843028 * 2
def baseEnd_1843028 : Nat := 210302049709937861816461

theorem tailTrace_1843028 : CollatzResearch.WordTrace tailWord_1843028 prefixEnd_1843028 210302049709937861816461 := by
  unfold tailWord_1843028
  simp only [CollatzResearch.WordTrace]
  refine ⟨33610376783515897483928869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44813835711354529978571825 33610376783515897483928869)
  ·
    refine ⟨6301945646909230778236663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33610376783515897483928869 6301945646909230778236663)
    ·
      refine ⟨9452918470363846167354995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301945646909230778236663 9452918470363846167354995)
      ·
        refine ⟨14179377705545769251032493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452918470363846167354995 14179377705545769251032493)
        ·
          refine ⟨5317266639579663469137185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14179377705545769251032493 5317266639579663469137185)
          ·
            refine ⟨3987949979684747601852889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317266639579663469137185 3987949979684747601852889)
            ·
              refine ⟨2990962484763560701389667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987949979684747601852889 2990962484763560701389667)
              ·
                refine ⟨4486443727145341052084501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990962484763560701389667 4486443727145341052084501)
                ·
                  refine ⟨210302049709937861816461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4486443727145341052084501 210302049709937861816461)
                  ·
                    rfl

theorem cell22_1843028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1843028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843028 prefixEnd_1843028 := by exact prefixLift 1843028
  have htrace : WordTrace (prefixWord ++ tailWord_1843028) baseStart_1843028 baseEnd_1843028 := by
    simpa [prefixWord, tailWord_1843028, baseEnd_1843028] using wordTrace_append hprefix tailTrace_1843028
  have hstable : (prefixWord ++ tailWord_1843028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843028).length < 2 ^ (prefixWord ++ tailWord_1843028).sum := by decide
  have hdescent : baseEnd_1843028 < baseStart_1843028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_1843131 : Nat := 118140960795 + 1843131 * 2 ^ 59
def prefixEnd_1843131 : Nat := 4983230072969 + 3 ^ 40 * 1843131 * 2
def baseEnd_1843131 : Nat := 630941408134755650124067

theorem tailTrace_1843131 : CollatzResearch.WordTrace tailWord_1843131 prefixEnd_1843131 630941408134755650124067 := by
  unfold tailWord_1843131
  simp only [CollatzResearch.WordTrace]
  refine ⟨67224510285658643558857247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44816340190439095705904831 67224510285658643558857247)
  ·
    refine ⟨100836765428487965338285871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67224510285658643558857247 100836765428487965338285871)
    ·
      refine ⟨151255148142731948007428807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100836765428487965338285871 151255148142731948007428807)
      ·
        refine ⟨226882722214097922011143211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151255148142731948007428807 226882722214097922011143211)
        ·
          refine ⟨340324083321146883016714817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226882722214097922011143211 340324083321146883016714817)
          ·
            refine ⟨255243062490860162262536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340324083321146883016714817 255243062490860162262536113)
            ·
              refine ⟨191432296868145121696902085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255243062490860162262536113 191432296868145121696902085)
              ·
                refine ⟨35893555662777210318169141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191432296868145121696902085 35893555662777210318169141)
                ·
                  refine ⟨3365020843385363467328357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35893555662777210318169141 3365020843385363467328357)
                  ·
                    refine ⟨630941408134755650124067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365020843385363467328357 630941408134755650124067)
                    ·
                      rfl

theorem cell22_1843131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_1843131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843131 prefixEnd_1843131 := by exact prefixLift 1843131
  have htrace : WordTrace (prefixWord ++ tailWord_1843131) baseStart_1843131 baseEnd_1843131 := by
    simpa [prefixWord, tailWord_1843131, baseEnd_1843131] using wordTrace_append hprefix tailTrace_1843131
  have hstable : (prefixWord ++ tailWord_1843131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843131).length < 2 ^ (prefixWord ++ tailWord_1843131).sum := by decide
  have hdescent : baseEnd_1843131 < baseStart_1843131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843148 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_1843148 : Nat := 118140960795 + 1843148 * 2 ^ 59
def prefixEnd_1843148 : Nat := 4983230072969 + 3 ^ 40 * 1843148 * 2
def baseEnd_1843148 : Nat := 630947227582173272449015

theorem tailTrace_1843148 : CollatzResearch.WordTrace tailWord_1843148 prefixEnd_1843148 630947227582173272449015 := by
  unfold tailWord_1843148
  simp only [CollatzResearch.WordTrace]
  refine ⟨33612565163298527731113049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44816753551064703641484065 33612565163298527731113049)
  ·
    refine ⟨25209423872473895798334787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33612565163298527731113049 25209423872473895798334787)
    ·
      refine ⟨37814135808710843697502181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25209423872473895798334787 37814135808710843697502181)
      ·
        refine ⟨7090150464133283193281659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37814135808710843697502181 7090150464133283193281659)
        ·
          refine ⟨10635225696199924789922489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090150464133283193281659 10635225696199924789922489)
          ·
            refine ⟨7976419272149943592441867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635225696199924789922489 7976419272149943592441867)
            ·
              refine ⟨11964628908224915388662801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976419272149943592441867 11964628908224915388662801)
              ·
                refine ⟨8973471681168686541497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11964628908224915388662801 8973471681168686541497101)
                ·
                  refine ⟨3365051880438257453061413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8973471681168686541497101 3365051880438257453061413)
                  ·
                    refine ⟨630947227582173272449015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365051880438257453061413 630947227582173272449015)
                    ·
                      rfl

theorem cell22_1843148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_1843148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843148 prefixEnd_1843148 := by exact prefixLift 1843148
  have htrace : WordTrace (prefixWord ++ tailWord_1843148) baseStart_1843148 baseEnd_1843148 := by
    simpa [prefixWord, tailWord_1843148, baseEnd_1843148] using wordTrace_append hprefix tailTrace_1843148
  have hstable : (prefixWord ++ tailWord_1843148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843148).length < 2 ^ (prefixWord ++ tailWord_1843148).sum := by decide
  have hdescent : baseEnd_1843148 < baseStart_1843148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843178 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1843178 : Nat := 118140960795 + 1843178 * 2 ^ 59
def prefixEnd_1843178 : Nat := 4983230072969 + 3 ^ 40 * 1843178 * 2
def baseEnd_1843178 : Nat := 630957497195263194198923

theorem tailTrace_1843178 : CollatzResearch.WordTrace tailWord_1843178 prefixEnd_1843178 630957497195263194198923 := by
  unfold tailWord_1843178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806556129122092646454547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44817483010992247057212125 16806556129122092646454547)
  ·
    refine ⟨25209834193683138969681821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16806556129122092646454547 25209834193683138969681821)
    ·
      refine ⟨9453687822631177113630683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25209834193683138969681821 9453687822631177113630683)
      ·
        refine ⟨14180531733946765670446025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453687822631177113630683 14180531733946765670446025)
        ·
          refine ⟨10635398800460074252834519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180531733946765670446025 10635398800460074252834519)
          ·
            refine ⟨15953098200690111379251779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635398800460074252834519 15953098200690111379251779)
            ·
              refine ⟨23929647301035167068877669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15953098200690111379251779 23929647301035167068877669)
              ·
                refine ⟨4486808868944093825414563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23929647301035167068877669 4486808868944093825414563)
                ·
                  refine ⟨6730213303416140738121845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486808868944093825414563 6730213303416140738121845)
                  ·
                    refine ⟨630957497195263194198923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6730213303416140738121845 630957497195263194198923)
                    ·
                      rfl

theorem cell22_1843178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1843178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843178 prefixEnd_1843178 := by exact prefixLift 1843178
  have htrace : WordTrace (prefixWord ++ tailWord_1843178) baseStart_1843178 baseEnd_1843178 := by
    simpa [prefixWord, tailWord_1843178, baseEnd_1843178] using wordTrace_append hprefix tailTrace_1843178
  have hstable : (prefixWord ++ tailWord_1843178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843178).length < 2 ^ (prefixWord ++ tailWord_1843178).sum := by decide
  have hdescent : baseEnd_1843178 < baseStart_1843178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843182 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1843182 : Nat := 118140960795 + 1843182 * 2 ^ 59
def prefixEnd_1843182 : Nat := 4983230072969 + 3 ^ 40 * 1843182 * 2
def baseEnd_1843182 : Nat := 630958866477008517098911

theorem tailTrace_1843182 : CollatzResearch.WordTrace tailWord_1843182 prefixEnd_1843182 630958866477008517098911 := by
  unfold tailWord_1843182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403296301059234908620475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44817580272315919512642533 8403296301059234908620475)
  ·
    refine ⟨12604944451588852362930713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403296301059234908620475 12604944451588852362930713)
    ·
      refine ⟨9453708338691639272198035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12604944451588852362930713 9453708338691639272198035)
      ·
        refine ⟨14180562508037458908297053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453708338691639272198035 14180562508037458908297053)
        ·
          refine ⟨5317710940514047090611395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14180562508037458908297053 5317710940514047090611395)
          ·
            refine ⟨7976566410771070635917093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317710940514047090611395 7976566410771070635917093)
            ·
              refine ⟨1495606202019575744234455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7976566410771070635917093 1495606202019575744234455)
              ·
                refine ⟨2243409303029363616351683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495606202019575744234455 2243409303029363616351683)
                ·
                  refine ⟨3365113954544045424527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243409303029363616351683 3365113954544045424527525)
                  ·
                    refine ⟨630958866477008517098911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365113954544045424527525 630958866477008517098911)
                    ·
                      rfl

theorem cell22_1843182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1843182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843182 prefixEnd_1843182 := by exact prefixLift 1843182
  have htrace : WordTrace (prefixWord ++ tailWord_1843182) baseStart_1843182 baseEnd_1843182 := by
    simpa [prefixWord, tailWord_1843182, baseEnd_1843182] using wordTrace_append hprefix tailTrace_1843182
  have hstable : (prefixWord ++ tailWord_1843182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843182).length < 2 ^ (prefixWord ++ tailWord_1843182).sum := by decide
  have hdescent : baseEnd_1843182 < baseStart_1843182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843195 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 2, 3]
def baseStart_1843195 : Nat := 118140960795 + 1843195 * 2 ^ 59
def prefixEnd_1843195 : Nat := 4983230072969 + 3 ^ 40 * 1843195 * 2
def baseEnd_1843195 : Nat := 630963316642680816523871

theorem tailTrace_1843195 : CollatzResearch.WordTrace tailWord_1843195 prefixEnd_1843195 630963316642680816523871 := by
  unfold tailWord_1843195
  simp only [CollatzResearch.WordTrace]
  refine ⟨67226844557426782489187039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44817896371617854992791359 67226844557426782489187039)
  ·
    refine ⟨100840266836140173733780559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67226844557426782489187039 100840266836140173733780559)
    ·
      refine ⟨151260400254210260600670839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100840266836140173733780559 151260400254210260600670839)
      ·
        refine ⟨226890600381315390901006259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151260400254210260600670839 226890600381315390901006259)
        ·
          refine ⟨340335900571973086351509389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226890600381315390901006259 340335900571973086351509389)
          ·
            refine ⟨127625962714489907381816021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340335900571973086351509389 127625962714489907381816021)
            ·
              refine ⟨2991233501120857204261313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127625962714489907381816021 2991233501120857204261313)
              ·
                refine ⟨2243425125840642903195985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991233501120857204261313 2243425125840642903195985)
                ·
                  refine ⟨1682568844380482177396989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243425125840642903195985 1682568844380482177396989)
                  ·
                    refine ⟨630963316642680816523871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682568844380482177396989 630963316642680816523871)
                    ·
                      rfl

theorem cell22_1843195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 3].length) (baseStart_1843195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843195 prefixEnd_1843195 := by exact prefixLift 1843195
  have htrace : WordTrace (prefixWord ++ tailWord_1843195) baseStart_1843195 baseEnd_1843195 := by
    simpa [prefixWord, tailWord_1843195, baseEnd_1843195] using wordTrace_append hprefix tailTrace_1843195
  have hstable : (prefixWord ++ tailWord_1843195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843195).length < 2 ^ (prefixWord ++ tailWord_1843195).sum := by decide
  have hdescent : baseEnd_1843195 < baseStart_1843195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843212 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_1843212 : Nat := 118140960795 + 1843212 * 2 ^ 59
def prefixEnd_1843212 : Nat := 4983230072969 + 3 ^ 40 * 1843212 * 2
def baseEnd_1843212 : Nat := 630969136090098438848819

theorem tailTrace_1843212 : CollatzResearch.WordTrace tailWord_1843212 prefixEnd_1843212 630969136090098438848819 := by
  unfold tailWord_1843212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33613732299182597196277945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44818309732243462928370593 33613732299182597196277945)
  ·
    refine ⟨25210299224386947897208459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33613732299182597196277945 25210299224386947897208459)
    ·
      refine ⟨37815448836580421845812689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25210299224386947897208459 37815448836580421845812689)
      ·
        refine ⟨28361586627435316384359517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37815448836580421845812689 28361586627435316384359517)
        ·
          refine ⟨10635594985288243644134819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28361586627435316384359517 10635594985288243644134819)
          ·
            refine ⟨15953392477932365466202229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635594985288243644134819 15953392477932365466202229)
            ·
              refine ⟨1495630544806159262456459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15953392477932365466202229 1495630544806159262456459)
              ·
                refine ⟨2243445817209238893684689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495630544806159262456459 2243445817209238893684689)
                ·
                  refine ⟨1682584362906929170263517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243445817209238893684689 1682584362906929170263517)
                  ·
                    refine ⟨630969136090098438848819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682584362906929170263517 630969136090098438848819)
                    ·
                      rfl

theorem cell22_1843212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_1843212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843212 prefixEnd_1843212 := by exact prefixLift 1843212
  have htrace : WordTrace (prefixWord ++ tailWord_1843212) baseStart_1843212 baseEnd_1843212 := by
    simpa [prefixWord, tailWord_1843212, baseEnd_1843212] using wordTrace_append hprefix tailTrace_1843212
  have hstable : (prefixWord ++ tailWord_1843212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843212).length < 2 ^ (prefixWord ++ tailWord_1843212).sum := by decide
  have hdescent : baseEnd_1843212 < baseStart_1843212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843253 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 7]
def baseStart_1843253 : Nat := 118140960795 + 1843253 * 2 ^ 59
def prefixEnd_1843253 : Nat := 4983230072969 + 3 ^ 40 * 1843253 * 2
def baseEnd_1843253 : Nat := 210327723742662666191231

theorem tailTrace_1843253 : CollatzResearch.WordTrace tailWord_1843253 prefixEnd_1843253 210327723742662666191231 := by
  unfold tailWord_1843253
  simp only [CollatzResearch.WordTrace]
  refine ⟨67228959991216658394798413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44819306660811105596532275 67228959991216658394798413)
  ·
    refine ⟨25210859996706246898049405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67228959991216658394798413 25210859996706246898049405)
    ·
      refine ⟨9454072498764842586768527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25210859996706246898049405 9454072498764842586768527)
      ·
        refine ⟨14181108748147263880152791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9454072498764842586768527 14181108748147263880152791)
        ·
          refine ⟨21271663122220895820229187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14181108748147263880152791 21271663122220895820229187)
          ·
            refine ⟨31907494683331343730343781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21271663122220895820229187 31907494683331343730343781)
            ·
              refine ⟨5982655253124626949439459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31907494683331343730343781 5982655253124626949439459)
              ·
                refine ⟨8973982879686940424159189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982655253124626949439459 8973982879686940424159189)
                ·
                  refine ⟨210327723742662666191231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8973982879686940424159189 210327723742662666191231)
                  ·
                    rfl

theorem cell22_1843253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_1843253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843253 prefixEnd_1843253 := by exact prefixLift 1843253
  have htrace : WordTrace (prefixWord ++ tailWord_1843253) baseStart_1843253 baseEnd_1843253 := by
    simpa [prefixWord, tailWord_1843253, baseEnd_1843253] using wordTrace_append hprefix tailTrace_1843253
  have hstable : (prefixWord ++ tailWord_1843253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843253).length < 2 ^ (prefixWord ++ tailWord_1843253).sum := by decide
  have hdescent : baseEnd_1843253 < baseStart_1843253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843300 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_1843300 : Nat := 118140960795 + 1843300 * 2 ^ 59
def prefixEnd_1843300 : Nat := 4983230072969 + 3 ^ 40 * 1843300 * 2
def baseEnd_1843300 : Nat := 630999260288495542648549

theorem tailTrace_1843300 : CollatzResearch.WordTrace tailWord_1843300 prefixEnd_1843300 630999260288495542648549 := by
  unfold tailWord_1843300
  simp only [CollatzResearch.WordTrace]
  refine ⟨33615337111023192710879677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44820449481364256947839569 33615337111023192710879677)
  ·
    refine ⟨12605751416633697266579879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33615337111023192710879677 12605751416633697266579879)
    ·
      refine ⟨18908627124950545899869819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605751416633697266579879 18908627124950545899869819)
      ·
        refine ⟨28362940687425818849804729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908627124950545899869819 28362940687425818849804729)
        ·
          refine ⟨21272205515569364137353547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28362940687425818849804729 21272205515569364137353547)
          ·
            refine ⟨31908308273354046206030321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21272205515569364137353547 31908308273354046206030321)
            ·
              refine ⟨23931231205015534654522741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31908308273354046206030321 23931231205015534654522741)
              ·
                refine ⟨2243552925470206373861507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23931231205015534654522741 2243552925470206373861507)
                ·
                  refine ⟨3365329388205309560792261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243552925470206373861507 3365329388205309560792261)
                  ·
                    refine ⟨630999260288495542648549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365329388205309560792261 630999260288495542648549)
                    ·
                      rfl

theorem cell22_1843300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_1843300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843300 prefixEnd_1843300 := by exact prefixLift 1843300
  have htrace : WordTrace (prefixWord ++ tailWord_1843300) baseStart_1843300 baseEnd_1843300 := by
    simpa [prefixWord, tailWord_1843300, baseEnd_1843300] using wordTrace_append hprefix tailTrace_1843300
  have hstable : (prefixWord ++ tailWord_1843300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843300).length < 2 ^ (prefixWord ++ tailWord_1843300).sum := by decide
  have hdescent : baseEnd_1843300 < baseStart_1843300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843313 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_1843313 : Nat := 118140960795 + 1843313 * 2 ^ 59
def prefixEnd_1843313 : Nat := 4983230072969 + 3 ^ 40 * 1843313 * 2
def baseEnd_1843313 : Nat := 631003710454167842073509

theorem tailTrace_1843313 : CollatzResearch.WordTrace tailWord_1843313 prefixEnd_1843313 631003710454167842073509 := by
  unfold tailWord_1843313
  simp only [CollatzResearch.WordTrace]
  refine ⟨67231148370999288641982593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44820765580666192427988395 67231148370999288641982593)
  ·
    refine ⟨50423361278249466481486945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67231148370999288641982593 50423361278249466481486945)
    ·
      refine ⟨37817520958687099861115209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50423361278249466481486945 37817520958687099861115209)
      ·
        refine ⟨28363140719015324895836407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37817520958687099861115209 28363140719015324895836407)
        ·
          refine ⟨42544711078522987343754611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28363140719015324895836407 42544711078522987343754611)
          ·
            refine ⟨63817066617784481015631917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42544711078522987343754611 63817066617784481015631917)
            ·
              refine ⟨23931399981669180380861969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63817066617784481015631917 23931399981669180380861969)
              ·
                refine ⟨17948549986251885285646477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23931399981669180380861969 17948549986251885285646477)
                ·
                  refine ⟨6730706244844456982117429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17948549986251885285646477 6730706244844456982117429)
                  ·
                    refine ⟨631003710454167842073509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6730706244844456982117429 631003710454167842073509)
                    ·
                      rfl

theorem cell22_1843313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_1843313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843313 prefixEnd_1843313 := by exact prefixLift 1843313
  have htrace : WordTrace (prefixWord ++ tailWord_1843313) baseStart_1843313 baseEnd_1843313 := by
    simpa [prefixWord, tailWord_1843313, baseEnd_1843313] using wordTrace_append hprefix tailTrace_1843313
  have hstable : (prefixWord ++ tailWord_1843313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843313).length < 2 ^ (prefixWord ++ tailWord_1843313).sum := by decide
  have hdescent : baseEnd_1843313 < baseStart_1843313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843328 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_1843328 : Nat := 118140960795 + 1843328 * 2 ^ 59
def prefixEnd_1843328 : Nat := 4983230072969 + 3 ^ 40 * 1843328 * 2
def baseEnd_1843328 : Nat := 631008845260712802948463

theorem tailTrace_1843328 : CollatzResearch.WordTrace tailWord_1843328 prefixEnd_1843328 631008845260712802948463 := by
  unfold tailWord_1843328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33615847732972473101889319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44821130310629964135852425 33615847732972473101889319)
  ·
    refine ⟨50423771599458709652833979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33615847732972473101889319 50423771599458709652833979)
    ·
      refine ⟨75635657399188064479250969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50423771599458709652833979 75635657399188064479250969)
      ·
        refine ⟨56726743049391048359438227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75635657399188064479250969 56726743049391048359438227)
        ·
          refine ⟨85090114574086572539157341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56726743049391048359438227 85090114574086572539157341)
          ·
            refine ⟨31908792965282464702184003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85090114574086572539157341 31908792965282464702184003)
            ·
              refine ⟨47863189447923697053276005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31908792965282464702184003 47863189447923697053276005)
              ·
                refine ⟨8974348021485693197489251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47863189447923697053276005 8974348021485693197489251)
                ·
                  refine ⟨13461522032228539796233877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974348021485693197489251 13461522032228539796233877)
                  ·
                    refine ⟨631008845260712802948463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13461522032228539796233877 631008845260712802948463)
                    ·
                      rfl

theorem cell22_1843328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_1843328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843328 prefixEnd_1843328 := by exact prefixLift 1843328
  have htrace : WordTrace (prefixWord ++ tailWord_1843328) baseStart_1843328 baseEnd_1843328 := by
    simpa [prefixWord, tailWord_1843328, baseEnd_1843328] using wordTrace_append hprefix tailTrace_1843328
  have hstable : (prefixWord ++ tailWord_1843328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843328).length < 2 ^ (prefixWord ++ tailWord_1843328).sum := by decide
  have hdescent : baseEnd_1843328 < baseStart_1843328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843351 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 1, 4]
def baseStart_1843351 : Nat := 118140960795 + 1843351 * 2 ^ 59
def prefixEnd_1843351 : Nat := 4983230072969 + 3 ^ 40 * 1843351 * 2
def baseEnd_1843351 : Nat := 631016718630748409623393

theorem tailTrace_1843351 : CollatzResearch.WordTrace tailWord_1843351 prefixEnd_1843351 631016718630748409623393 := by
  unfold tailWord_1843351
  simp only [CollatzResearch.WordTrace]
  refine ⟨67232534344861621131865907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44821689563241080754577271 67232534344861621131865907)
  ·
    refine ⟨100848801517292431697798861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67232534344861621131865907 100848801517292431697798861)
    ·
      refine ⟨37818300568984661886674573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100848801517292431697798861 37818300568984661886674573)
      ·
        refine ⟨14181862713369248207502965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37818300568984661886674573 14181862713369248207502965)
        ·
          refine ⟨1329549629378367019453403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14181862713369248207502965 1329549629378367019453403)
          ·
            refine ⟨1994324444067550529180105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329549629378367019453403 1994324444067550529180105)
            ·
              refine ⟨1495743333050662896885079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994324444067550529180105 1495743333050662896885079)
              ·
                refine ⟨2243614999575994345327619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495743333050662896885079 2243614999575994345327619)
                ·
                  refine ⟨3365422499363991517991429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243614999575994345327619 3365422499363991517991429)
                  ·
                    refine ⟨631016718630748409623393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365422499363991517991429 631016718630748409623393)
                    ·
                      rfl

theorem cell22_1843351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_1843351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843351 prefixEnd_1843351 := by exact prefixLift 1843351
  have htrace : WordTrace (prefixWord ++ tailWord_1843351) baseStart_1843351 baseEnd_1843351 := by
    simpa [prefixWord, tailWord_1843351, baseEnd_1843351] using wordTrace_append hprefix tailTrace_1843351
  have hstable : (prefixWord ++ tailWord_1843351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843351).length < 2 ^ (prefixWord ++ tailWord_1843351).sum := by decide
  have hdescent : baseEnd_1843351 < baseStart_1843351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843381 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1843381 : Nat := 118140960795 + 1843381 * 2 ^ 59
def prefixEnd_1843381 : Nat := 4983230072969 + 3 ^ 40 * 1843381 * 2
def baseEnd_1843381 : Nat := 631026988243838331373301

theorem tailTrace_1843381 : CollatzResearch.WordTrace tailWord_1843381 prefixEnd_1843381 631026988243838331373301 := by
  unfold tailWord_1843381
  simp only [CollatzResearch.WordTrace]
  refine ⟨67233628534752936255457997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44822419023168624170305331 67233628534752936255457997)
  ·
    refine ⟨25212610700532351095796749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67233628534752936255457997 25212610700532351095796749)
    ·
      refine ⟨9454729012699631660923781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25212610700532351095796749 9454729012699631660923781)
      ·
        refine ⟨1772761689881180936423209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9454729012699631660923781 1772761689881180936423209)
        ·
          refine ⟨1329571267410885702317407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772761689881180936423209 1329571267410885702317407)
          ·
            refine ⟨1994356901116328553476111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329571267410885702317407 1994356901116328553476111)
            ·
              refine ⟨2991535351674492830214167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994356901116328553476111 2991535351674492830214167)
              ·
                refine ⟨4487303027511739245321251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991535351674492830214167 4487303027511739245321251)
                ·
                  refine ⟨6730954541267608867981877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487303027511739245321251 6730954541267608867981877)
                  ·
                    refine ⟨631026988243838331373301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6730954541267608867981877 631026988243838331373301)
                    ·
                      rfl

theorem cell22_1843381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1843381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843381 prefixEnd_1843381 := by exact prefixLift 1843381
  have htrace : WordTrace (prefixWord ++ tailWord_1843381) baseStart_1843381 baseEnd_1843381 := by
    simpa [prefixWord, tailWord_1843381, baseEnd_1843381] using wordTrace_append hprefix tailTrace_1843381
  have hstable : (prefixWord ++ tailWord_1843381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843381).length < 2 ^ (prefixWord ++ tailWord_1843381).sum := by decide
  have hdescent : baseEnd_1843381 < baseStart_1843381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843392 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 3, 3]
def baseStart_1843392 : Nat := 118140960795 + 1843392 * 2 ^ 59
def prefixEnd_1843392 : Nat := 4983230072969 + 3 ^ 40 * 1843392 * 2
def baseEnd_1843392 : Nat := 631030753768637969348267

theorem tailTrace_1843392 : CollatzResearch.WordTrace tailWord_1843392 prefixEnd_1843392 631030753768637969348267 := by
  unfold tailWord_1843392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33617014868856542567054215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44822686491808723422738953 33617014868856542567054215)
  ·
    refine ⟨50425522303284813850581323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33617014868856542567054215 50425522303284813850581323)
    ·
      refine ⟨75638283454927220775871985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50425522303284813850581323 75638283454927220775871985)
      ·
        refine ⟨56728712591195415581903989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75638283454927220775871985 56728712591195415581903989)
        ·
          refine ⟨5318316805424570210803499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56728712591195415581903989 5318316805424570210803499)
          ·
            refine ⟨7977475208136855316205249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318316805424570210803499 7977475208136855316205249)
            ·
              refine ⟨5983106406102641487153937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977475208136855316205249 5983106406102641487153937)
              ·
                refine ⟨4487329804576981115365453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983106406102641487153937 4487329804576981115365453)
                ·
                  refine ⟨1682748676716367918262045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4487329804576981115365453 1682748676716367918262045)
                  ·
                    refine ⟨631030753768637969348267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682748676716367918262045 631030753768637969348267)
                    ·
                      rfl

theorem cell22_1843392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_1843392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843392 prefixEnd_1843392 := by exact prefixLift 1843392
  have htrace : WordTrace (prefixWord ++ tailWord_1843392) baseStart_1843392 baseEnd_1843392 := by
    simpa [prefixWord, tailWord_1843392, baseEnd_1843392] using wordTrace_append hprefix tailTrace_1843392
  have hstable : (prefixWord ++ tailWord_1843392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843392).length < 2 ^ (prefixWord ++ tailWord_1843392).sum := by decide
  have hdescent : baseEnd_1843392 < baseStart_1843392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843394 : List Nat := [3, 5, 1, 1, 1, 2, 1, 8]
def baseStart_1843394 : Nat := 118140960795 + 1843394 * 2 ^ 59
def prefixEnd_1843394 : Nat := 4983230072969 + 3 ^ 40 * 1843394 * 2
def baseEnd_1843394 : Nat := 70114604267723403422029

theorem tailTrace_1843394 : CollatzResearch.WordTrace tailWord_1843394 prefixEnd_1843394 70114604267723403422029 := by
  unfold tailWord_1843394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808525670926459868920309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44822735122470559650454157 16808525670926459868920309)
  ·
    refine ⟨1575799281649355612711279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16808525670926459868920309 1575799281649355612711279)
    ·
      refine ⟨2363698922474033419066919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575799281649355612711279 2363698922474033419066919)
      ·
        refine ⟨3545548383711050128600379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363698922474033419066919 3545548383711050128600379)
        ·
          refine ⟨5318322575566575192900569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545548383711050128600379 5318322575566575192900569)
          ·
            refine ⟨3988741931674931394675427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318322575566575192900569 3988741931674931394675427)
            ·
              refine ⟨5983112897512397092013141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988741931674931394675427 5983112897512397092013141)
              ·
                refine ⟨70114604267723403422029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5983112897512397092013141 70114604267723403422029)
                ·
                  rfl

theorem cell22_1843394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_1843394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843394 prefixEnd_1843394 := by exact prefixLift 1843394
  have htrace : WordTrace (prefixWord ++ tailWord_1843394) baseStart_1843394 baseEnd_1843394 := by
    simpa [prefixWord, tailWord_1843394, baseEnd_1843394] using wordTrace_append hprefix tailTrace_1843394
  have hstable : (prefixWord ++ tailWord_1843394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843394).length < 2 ^ (prefixWord ++ tailWord_1843394).sum := by decide
  have hdescent : baseEnd_1843394 < baseStart_1843394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843409 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_1843409 : Nat := 118140960795 + 1843409 * 2 ^ 59
def prefixEnd_1843409 : Nat := 4983230072969 + 3 ^ 40 * 1843409 * 2
def baseEnd_1843409 : Nat := 631036573216055591673215

theorem tailTrace_1843409 : CollatzResearch.WordTrace tailWord_1843409 prefixEnd_1843409 631036573216055591673215 := by
  unfold tailWord_1843409
  simp only [CollatzResearch.WordTrace]
  refine ⟨67234649778651497037477281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823099852434331358318187 67234649778651497037477281)
  ·
    refine ⟨50425987333988622778107961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67234649778651497037477281 50425987333988622778107961)
    ·
      refine ⟨37819490500491467083580971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50425987333988622778107961 37819490500491467083580971)
      ·
        refine ⟨56729235750737200625371457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37819490500491467083580971 56729235750737200625371457)
        ·
          refine ⟨42546926813052900469028593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56729235750737200625371457 42546926813052900469028593)
          ·
            refine ⟨31910195109789675351771445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42546926813052900469028593 31910195109789675351771445)
            ·
              refine ⟨2991580791542782064228573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31910195109789675351771445 2991580791542782064228573)
              ·
                refine ⟨1121842796828543274085715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2991580791542782064228573 1121842796828543274085715)
                ·
                  refine ⟨1682764195242814911128573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121842796828543274085715 1682764195242814911128573)
                  ·
                    refine ⟨631036573216055591673215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682764195242814911128573 631036573216055591673215)
                    ·
                      rfl

theorem cell22_1843409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_1843409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843409 prefixEnd_1843409 := by exact prefixLift 1843409
  have htrace : WordTrace (prefixWord ++ tailWord_1843409) baseStart_1843409 baseEnd_1843409 := by
    simpa [prefixWord, tailWord_1843409, baseEnd_1843409] using wordTrace_append hprefix tailTrace_1843409
  have hstable : (prefixWord ++ tailWord_1843409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843409).length < 2 ^ (prefixWord ++ tailWord_1843409).sum := by decide
  have hdescent : baseEnd_1843409 < baseStart_1843409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843435 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_1843435 : Nat := 118140960795 + 1843435 * 2 ^ 59
def prefixEnd_1843435 : Nat := 4983230072969 + 3 ^ 40 * 1843435 * 2
def baseEnd_1843435 : Nat := 631045473547400190523135

theorem tailTrace_1843435 : CollatzResearch.WordTrace tailWord_1843435 prefixEnd_1843435 631045473547400190523135 := by
  unfold tailWord_1843435
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235598076557303477923759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823732051038202318615839 67235598076557303477923759)
  ·
    refine ⟨100853397114835955216885639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67235598076557303477923759 100853397114835955216885639)
    ·
      refine ⟨151280095672253932825328459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100853397114835955216885639 151280095672253932825328459)
      ·
        refine ⟨226920143508380899237992689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151280095672253932825328459 226920143508380899237992689)
        ·
          refine ⟨170190107631285674428494517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226920143508380899237992689 170190107631285674428494517)
          ·
            refine ⟨15955322590433031977671361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170190107631285674428494517 15955322590433031977671361)
            ·
              refine ⟨11966491942824773983253521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15955322590433031977671361 11966491942824773983253521)
              ·
                refine ⟨8974868957118580487440141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11966491942824773983253521 8974868957118580487440141)
                ·
                  refine ⟨3365575858919467682790053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8974868957118580487440141 3365575858919467682790053)
                  ·
                    refine ⟨631045473547400190523135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365575858919467682790053 631045473547400190523135)
                    ·
                      rfl

theorem cell22_1843435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_1843435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843435 prefixEnd_1843435 := by exact prefixLift 1843435
  have htrace : WordTrace (prefixWord ++ tailWord_1843435) baseStart_1843435 baseEnd_1843435 := by
    simpa [prefixWord, tailWord_1843435, baseEnd_1843435] using wordTrace_append hprefix tailTrace_1843435
  have hstable : (prefixWord ++ tailWord_1843435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843435).length < 2 ^ (prefixWord ++ tailWord_1843435).sum := by decide
  have hdescent : baseEnd_1843435 < baseStart_1843435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843439 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 5]
def baseStart_1843439 : Nat := 118140960795 + 1843439 * 2 ^ 59
def prefixEnd_1843439 : Nat := 4983230072969 + 3 ^ 40 * 1843439 * 2
def baseEnd_1843439 : Nat := 210348947609715171141041

theorem tailTrace_1843439 : CollatzResearch.WordTrace tailWord_1843439 prefixEnd_1843439 210348947609715171141041 := by
  unfold tailWord_1843439
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235743968542812161069371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823829312361874774046247 67235743968542812161069371)
  ·
    refine ⟨100853615952814218241604057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67235743968542812161069371 100853615952814218241604057)
    ·
      refine ⟨75640211964610663681203043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100853615952814218241604057 75640211964610663681203043)
      ·
        refine ⟨113460317946915995521804565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75640211964610663681203043 113460317946915995521804565)
        ·
          refine ⟨5318452403761687290084589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113460317946915995521804565 5318452403761687290084589)
          ·
            refine ⟨1994419651410632733781721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5318452403761687290084589 1994419651410632733781721)
            ·
              refine ⟨1495814738557974550336291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994419651410632733781721 1495814738557974550336291)
              ·
                refine ⟨2243722107836961825504437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495814738557974550336291 2243722107836961825504437)
                ·
                  refine ⟨210348947609715171141041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2243722107836961825504437 210348947609715171141041)
                  ·
                    rfl

theorem cell22_1843439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 5].length) (baseStart_1843439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843439 prefixEnd_1843439 := by exact prefixLift 1843439
  have htrace : WordTrace (prefixWord ++ tailWord_1843439) baseStart_1843439 baseEnd_1843439 := by
    simpa [prefixWord, tailWord_1843439, baseEnd_1843439] using wordTrace_append hprefix tailTrace_1843439
  have hstable : (prefixWord ++ tailWord_1843439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843439).length < 2 ^ (prefixWord ++ tailWord_1843439).sum := by decide
  have hdescent : baseEnd_1843439 < baseStart_1843439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843452 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1843452 : Nat := 118140960795 + 1843452 * 2 ^ 59
def prefixEnd_1843452 : Nat := 4983230072969 + 3 ^ 40 * 1843452 * 2
def baseEnd_1843452 : Nat := 631051292994817812848083

theorem tailTrace_1843452 : CollatzResearch.WordTrace tailWord_1843452 prefixEnd_1843452 631051292994817812848083 := by
  unfold tailWord_1843452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33618109058747857690646305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44824145411663810254195073 33618109058747857690646305)
  ·
    refine ⟨25213581794060893267984729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33618109058747857690646305 25213581794060893267984729)
    ·
      refine ⟨18910186345545669950988547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25213581794060893267984729 18910186345545669950988547)
      ·
        refine ⟨28365279518318504926482821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910186345545669950988547 28365279518318504926482821)
        ·
          refine ⟨5318489909684719673715529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28365279518318504926482821 5318489909684719673715529)
          ·
            refine ⟨3988867432263539755286647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318489909684719673715529 3988867432263539755286647)
            ·
              refine ⟨5983301148395309632929971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988867432263539755286647 5983301148395309632929971)
              ·
                refine ⟨8974951722592964449394957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983301148395309632929971 8974951722592964449394957)
                ·
                  refine ⟨3365606895972361668523109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8974951722592964449394957 3365606895972361668523109)
                  ·
                    refine ⟨631051292994817812848083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365606895972361668523109 631051292994817812848083)
                    ·
                      rfl

theorem cell22_1843452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1843452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843452 prefixEnd_1843452 := by exact prefixLift 1843452
  have htrace : WordTrace (prefixWord ++ tailWord_1843452) baseStart_1843452 baseEnd_1843452 := by
    simpa [prefixWord, tailWord_1843452, baseEnd_1843452] using wordTrace_append hprefix tailTrace_1843452
  have hstable : (prefixWord ++ tailWord_1843452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843452).length < 2 ^ (prefixWord ++ tailWord_1843452).sum := by decide
  have hdescent : baseEnd_1843452 < baseStart_1843452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843465 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_1843465 : Nat := 118140960795 + 1843465 * 2 ^ 59
def prefixEnd_1843465 : Nat := 4983230072969 + 3 ^ 40 * 1843465 * 2
def baseEnd_1843465 : Nat := 631055743160490112273043

theorem tailTrace_1843465 : CollatzResearch.WordTrace tailWord_1843465 prefixEnd_1843465 631055743160490112273043 := by
  unfold tailWord_1843465
  simp only [CollatzResearch.WordTrace]
  refine ⟨67236692266448618601515849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44824461510965745734343899 67236692266448618601515849)
  ·
    refine ⟨50427519199836463951136887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67236692266448618601515849 50427519199836463951136887)
    ·
      refine ⟨75641278799754695926705331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50427519199836463951136887 75641278799754695926705331)
      ·
        refine ⟨113461918199632043890057997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75641278799754695926705331 113461918199632043890057997)
        ·
          refine ⟨42548219324862016458771749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113461918199632043890057997 42548219324862016458771749)
          ·
            refine ⟨7977791123411628086019703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42548219324862016458771749 7977791123411628086019703)
            ·
              refine ⟨11966686685117442129029555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7977791123411628086019703 11966686685117442129029555)
              ·
                refine ⟨17950030027676163193544333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11966686685117442129029555 17950030027676163193544333)
                ·
                  refine ⟨6731261260378561197579125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17950030027676163193544333 6731261260378561197579125)
                  ·
                    refine ⟨631055743160490112273043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6731261260378561197579125 631055743160490112273043)
                    ·
                      rfl

theorem cell22_1843465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_1843465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843465 prefixEnd_1843465 := by exact prefixLift 1843465
  have htrace : WordTrace (prefixWord ++ tailWord_1843465) baseStart_1843465 baseEnd_1843465 := by
    simpa [prefixWord, tailWord_1843465, baseEnd_1843465] using wordTrace_append hprefix tailTrace_1843465
  have hstable : (prefixWord ++ tailWord_1843465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843465).length < 2 ^ (prefixWord ++ tailWord_1843465).sum := by decide
  have hdescent : baseEnd_1843465 < baseStart_1843465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843467 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 4]
def baseStart_1843467 : Nat := 118140960795 + 1843467 * 2 ^ 59
def prefixEnd_1843467 : Nat := 4983230072969 + 3 ^ 40 * 1843467 * 2
def baseEnd_1843467 : Nat := 210352142600454257907679

theorem tailTrace_1843467 : CollatzResearch.WordTrace tailWord_1843467 prefixEnd_1843467 210352142600454257907679 := by
  unfold tailWord_1843467
  simp only [CollatzResearch.WordTrace]
  refine ⟨67236765212441372943088655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44824510141627581962059103 67236765212441372943088655)
  ·
    refine ⟨100855147818662059414632983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67236765212441372943088655 100855147818662059414632983)
    ·
      refine ⟨151282721727993089121949475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100855147818662059414632983 151282721727993089121949475)
      ·
        refine ⟨226924082591989633682924213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151282721727993089121949475 226924082591989633682924213)
        ·
          refine ⟨21274132742999028157774145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226924082591989633682924213 21274132742999028157774145)
          ·
            refine ⟨15955599557249271118330609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21274132742999028157774145 15955599557249271118330609)
            ·
              refine ⟨11966699667936953338747957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15955599557249271118330609 11966699667936953338747957)
              ·
                refine ⟨1121878093869089375507621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11966699667936953338747957 1121878093869089375507621)
                ·
                  refine ⟨210352142600454257907679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121878093869089375507621 210352142600454257907679)
                  ·
                    rfl

theorem cell22_1843467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 4].length) (baseStart_1843467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843467 prefixEnd_1843467 := by exact prefixLift 1843467
  have htrace : WordTrace (prefixWord ++ tailWord_1843467) baseStart_1843467 baseEnd_1843467 := by
    simpa [prefixWord, tailWord_1843467, baseEnd_1843467] using wordTrace_append hprefix tailTrace_1843467
  have hstable : (prefixWord ++ tailWord_1843467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843467).length < 2 ^ (prefixWord ++ tailWord_1843467).sum := by decide
  have hdescent : baseEnd_1843467 < baseStart_1843467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843514 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1843514 : Nat := 118140960795 + 1843514 * 2 ^ 59
def prefixEnd_1843514 : Nat := 4983230072969 + 3 ^ 40 * 1843514 * 2
def baseEnd_1843514 : Nat := 631072516861870317797893

theorem tailTrace_1843514 : CollatzResearch.WordTrace tailWord_1843514 prefixEnd_1843514 631072516861870317797893 := by
  unfold tailWord_1843514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809619860817774992512399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44825652962180733313366397 16809619860817774992512399)
  ·
    refine ⟨25214429791226662488768599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809619860817774992512399 25214429791226662488768599)
    ·
      refine ⟨37821644686839993733152899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25214429791226662488768599 37821644686839993733152899)
      ·
        refine ⟨56732467030259990599729349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37821644686839993733152899 56732467030259990599729349)
        ·
          refine ⟨10637337568173748237449253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56732467030259990599729349 10637337568173748237449253)
          ·
            refine ⟨1994500794032577794521735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10637337568173748237449253 1994500794032577794521735)
            ·
              refine ⟨2991751191048866691782603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994500794032577794521735 2991751191048866691782603)
              ·
                refine ⟨4487626786573300037673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991751191048866691782603 4487626786573300037673905)
                ·
                  refine ⟨3365720089929975028255429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487626786573300037673905 3365720089929975028255429)
                  ·
                    refine ⟨631072516861870317797893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365720089929975028255429 631072516861870317797893)
                    ·
                      rfl

theorem cell22_1843514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1843514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843514 prefixEnd_1843514 := by exact prefixLift 1843514
  have htrace : WordTrace (prefixWord ++ tailWord_1843514) baseStart_1843514 baseEnd_1843514 := by
    simpa [prefixWord, tailWord_1843514, baseEnd_1843514] using wordTrace_append hprefix tailTrace_1843514
  have hstable : (prefixWord ++ tailWord_1843514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843514).length < 2 ^ (prefixWord ++ tailWord_1843514).sum := by decide
  have hdescent : baseEnd_1843514 < baseStart_1843514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843527 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1843527 : Nat := 118140960795 + 1843527 * 2 ^ 59
def prefixEnd_1843527 : Nat := 4983230072969 + 3 ^ 40 * 1843527 * 2
def baseEnd_1843527 : Nat := 631076967027542617222853

theorem tailTrace_1843527 : CollatzResearch.WordTrace tailWord_1843527 prefixEnd_1843527 631076967027542617222853 := by
  unfold tailWord_1843527
  simp only [CollatzResearch.WordTrace]
  refine ⟨67238953592224003190272835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44825969061482668793515223 67238953592224003190272835)
  ·
    refine ⟨100858430388336004785409253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67238953592224003190272835 100858430388336004785409253)
    ·
      refine ⟨18910955697813000897264235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100858430388336004785409253 18910955697813000897264235)
      ·
        refine ⟨28366433546719501345896353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910955697813000897264235 28366433546719501345896353)
        ·
          refine ⟨21274825160039626009422265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28366433546719501345896353 21274825160039626009422265)
          ·
            refine ⟨15956118870029719507066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21274825160039626009422265 15956118870029719507066699)
            ·
              refine ⟨23934178305044579260600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15956118870029719507066699 23934178305044579260600049)
              ·
                refine ⟨17950633728783434445450037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23934178305044579260600049 17950633728783434445450037)
                ·
                  refine ⟨1682871912073446979260941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17950633728783434445450037 1682871912073446979260941)
                  ·
                    refine ⟨631076967027542617222853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1682871912073446979260941 631076967027542617222853)
                    ·
                      rfl

theorem cell22_1843527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1843527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843527 prefixEnd_1843527 := by exact prefixLift 1843527
  have htrace : WordTrace (prefixWord ++ tailWord_1843527) baseStart_1843527 baseEnd_1843527 := by
    simpa [prefixWord, tailWord_1843527, baseEnd_1843527] using wordTrace_append hprefix tailTrace_1843527
  have hstable : (prefixWord ++ tailWord_1843527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843527).length < 2 ^ (prefixWord ++ tailWord_1843527).sum := by decide
  have hdescent : baseEnd_1843527 < baseStart_1843527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843662 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1843662 : Nat := 118140960795 + 1843662 * 2 ^ 59
def prefixEnd_1843662 : Nat := 4983230072969 + 3 ^ 40 * 1843662 * 2
def baseEnd_1843662 : Nat := 631123180286447265097439

theorem tailTrace_1843662 : CollatzResearch.WordTrace tailWord_1843662 prefixEnd_1843662 631123180286447265097439 := by
  unfold tailWord_1843662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405484680841865155804655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44829251631156614164291493 8405484680841865155804655)
  ·
    refine ⟨12608227021262797733706983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405484680841865155804655 12608227021262797733706983)
    ·
      refine ⟨18912340531894196600560475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12608227021262797733706983 18912340531894196600560475)
      ·
        refine ⟨28368510797841294900840713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912340531894196600560475 28368510797841294900840713)
        ·
          refine ⟨21276383098380971175630535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28368510797841294900840713 21276383098380971175630535)
          ·
            refine ⟨31914574647571456763445803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276383098380971175630535 31914574647571456763445803)
            ·
              refine ⟨47871861971357185145168705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31914574647571456763445803 47871861971357185145168705)
              ·
                refine ⟨35903896478517888858876529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47871861971357185145168705 35903896478517888858876529)
                ·
                  refine ⟨26927922358888416644157397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35903896478517888858876529 26927922358888416644157397)
                  ·
                    refine ⟨631123180286447265097439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26927922358888416644157397 631123180286447265097439)
                    ·
                      rfl

theorem cell22_1843662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1843662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843662 prefixEnd_1843662 := by exact prefixLift 1843662
  have htrace : WordTrace (prefixWord ++ tailWord_1843662) baseStart_1843662 baseEnd_1843662 := by
    simpa [prefixWord, tailWord_1843662, baseEnd_1843662] using wordTrace_append hprefix tailTrace_1843662
  have hstable : (prefixWord ++ tailWord_1843662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843662).length < 2 ^ (prefixWord ++ tailWord_1843662).sum := by decide
  have hdescent : baseEnd_1843662 < baseStart_1843662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843679 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 5, 3]
def baseStart_1843679 : Nat := 118140960795 + 1843679 * 2 ^ 59
def prefixEnd_1843679 : Nat := 4983230072969 + 3 ^ 40 * 1843679 * 2
def baseEnd_1843679 : Nat := 631128999733864887422387

theorem tailTrace_1843679 : CollatzResearch.WordTrace tailWord_1843679 prefixEnd_1843679 631128999733864887422387 := by
  unfold tailWord_1843679
  simp only [CollatzResearch.WordTrace]
  refine ⟨67244497487673333149806091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44829664991782222099870727 67244497487673333149806091)
  ·
    refine ⟨100866746231509999724709137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67244497487673333149806091 100866746231509999724709137)
    ·
      refine ⟨75650059673632499793531853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100866746231509999724709137 75650059673632499793531853)
      ·
        refine ⟨28368772377612187422574445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75650059673632499793531853 28368772377612187422574445)
        ·
          refine ⟨10638289641604570283465417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28368772377612187422574445 10638289641604570283465417)
          ·
            refine ⟨7978717231203427712599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10638289641604570283465417 7978717231203427712599063)
            ·
              refine ⟨11968075846805141568898595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978717231203427712599063 11968075846805141568898595)
              ·
                refine ⟨17952113770207712353347893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11968075846805141568898595 17952113770207712353347893)
                ·
                  refine ⟨1683010665956973033126365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17952113770207712353347893 1683010665956973033126365)
                  ·
                    refine ⟨631128999733864887422387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683010665956973033126365 631128999733864887422387)
                    ·
                      rfl

theorem cell22_1843679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_1843679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843679 prefixEnd_1843679 := by exact prefixLift 1843679
  have htrace : WordTrace (prefixWord ++ tailWord_1843679) baseStart_1843679 baseEnd_1843679 := by
    simpa [prefixWord, tailWord_1843679, baseEnd_1843679] using wordTrace_append hprefix tailTrace_1843679
  have hstable : (prefixWord ++ tailWord_1843679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843679).length < 2 ^ (prefixWord ++ tailWord_1843679).sum := by decide
  have hdescent : baseEnd_1843679 < baseStart_1843679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843683 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 2, 4]
def baseStart_1843683 : Nat := 118140960795 + 1843683 * 2 ^ 59
def prefixEnd_1843683 : Nat := 4983230072969 + 3 ^ 40 * 1843683 * 2
def baseEnd_1843683 : Nat := 631130369015610210322375

theorem tailTrace_1843683 : CollatzResearch.WordTrace tailWord_1843683 prefixEnd_1843683 631130369015610210322375 := by
  unfold tailWord_1843683
  simp only [CollatzResearch.WordTrace]
  refine ⟨67244643379658841832951703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44829762253105894555301135 67244643379658841832951703)
  ·
    refine ⟨100866965069488262749427555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67244643379658841832951703 100866965069488262749427555)
    ·
      refine ⟨151300447604232394124141333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100866965069488262749427555 151300447604232394124141333)
      ·
        refine ⟨7092208481448393474569125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151300447604232394124141333 7092208481448393474569125)
        ·
          refine ⟨1329789090271573776481711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7092208481448393474569125 1329789090271573776481711)
          ·
            refine ⟨1994683635407360664722567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329789090271573776481711 1994683635407360664722567)
            ·
              refine ⟨2992025453111040997083851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994683635407360664722567 2992025453111040997083851)
              ·
                refine ⟨4488038179666561495625777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992025453111040997083851 4488038179666561495625777)
                ·
                  refine ⟨3366028634749921121719333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488038179666561495625777 3366028634749921121719333)
                  ·
                    refine ⟨631130369015610210322375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366028634749921121719333 631130369015610210322375)
                    ·
                      rfl

theorem cell22_1843683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 4].length) (baseStart_1843683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843683 prefixEnd_1843683 := by exact prefixLift 1843683
  have htrace : WordTrace (prefixWord ++ tailWord_1843683) baseStart_1843683 baseEnd_1843683 := by
    simpa [prefixWord, tailWord_1843683, baseEnd_1843683] using wordTrace_append hprefix tailTrace_1843683
  have hstable : (prefixWord ++ tailWord_1843683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843683).length < 2 ^ (prefixWord ++ tailWord_1843683).sum := by decide
  have hdescent : baseEnd_1843683 < baseStart_1843683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843692 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 7]
def baseStart_1843692 : Nat := 118140960795 + 1843692 * 2 ^ 59
def prefixEnd_1843692 : Nat := 4983230072969 + 3 ^ 40 * 1843692 * 2
def baseEnd_1843692 : Nat := 210377816633179062282449

theorem tailTrace_1843692 : CollatzResearch.WordTrace tailWord_1843692 prefixEnd_1843692 210377816633179062282449 := by
  unfold tailWord_1843692
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622485818313118185014665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44829981091084157580019553 33622485818313118185014665)
  ·
    refine ⟨25216864363734838638760999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33622485818313118185014665 25216864363734838638760999)
    ·
      refine ⟨37825296545602257958141499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25216864363734838638760999 37825296545602257958141499)
      ·
        refine ⟨56737944818403386937212249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37825296545602257958141499 56737944818403386937212249)
        ·
          refine ⟨42553458613802540202909187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56737944818403386937212249 42553458613802540202909187)
          ·
            refine ⟨63830187920703810304363781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42553458613802540202909187 63830187920703810304363781)
            ·
              refine ⟨11968160235131964432068209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63830187920703810304363781 11968160235131964432068209)
              ·
                refine ⟨8976120176348973324051157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11968160235131964432068209 8976120176348973324051157)
                ·
                  refine ⟨210377816633179062282449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8976120176348973324051157 210377816633179062282449)
                  ·
                    rfl

theorem cell22_1843692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_1843692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843692 prefixEnd_1843692 := by exact prefixLift 1843692
  have htrace : WordTrace (prefixWord ++ tailWord_1843692) baseStart_1843692 baseEnd_1843692 := by
    simpa [prefixWord, tailWord_1843692, baseEnd_1843692] using wordTrace_append hprefix tailTrace_1843692
  have hstable : (prefixWord ++ tailWord_1843692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843692).length < 2 ^ (prefixWord ++ tailWord_1843692).sum := by decide
  have hdescent : baseEnd_1843692 < baseStart_1843692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843713 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1843713 : Nat := 118140960795 + 1843713 * 2 ^ 59
def prefixEnd_1843713 : Nat := 4983230072969 + 3 ^ 40 * 1843713 * 2
def baseEnd_1843713 : Nat := 631140638628700132072283

theorem tailTrace_1843713 : CollatzResearch.WordTrace tailWord_1843713 prefixEnd_1843713 631140638628700132072283 := by
  unfold tailWord_1843713
  simp only [CollatzResearch.WordTrace]
  refine ⟨67245737569550156956543793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44830491713033437971029195 67245737569550156956543793)
  ·
    refine ⟨50434303177162617717407845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67245737569550156956543793 50434303177162617717407845)
    ·
      refine ⟨9456431845717990822013971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50434303177162617717407845 9456431845717990822013971)
      ·
        refine ⟨14184647768576986233020957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9456431845717990822013971 14184647768576986233020957)
        ·
          refine ⟨5319242913216369837382859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14184647768576986233020957 5319242913216369837382859)
          ·
            refine ⟨7978864369824554756074289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319242913216369837382859 7978864369824554756074289)
            ·
              refine ⟨5984148277368416067055717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7978864369824554756074289 5984148277368416067055717)
              ·
                refine ⟨1122027802006578012572947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5984148277368416067055717 1122027802006578012572947)
                ·
                  refine ⟨1683041703009867018859421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122027802006578012572947 1683041703009867018859421)
                  ·
                    refine ⟨631140638628700132072283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683041703009867018859421 631140638628700132072283)
                    ·
                      rfl

theorem cell22_1843713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1843713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843713 prefixEnd_1843713 := by exact prefixLift 1843713
  have htrace : WordTrace (prefixWord ++ tailWord_1843713) baseStart_1843713 baseEnd_1843713 := by
    simpa [prefixWord, tailWord_1843713, baseEnd_1843713] using wordTrace_append hprefix tailTrace_1843713
  have hstable : (prefixWord ++ tailWord_1843713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843713).length < 2 ^ (prefixWord ++ tailWord_1843713).sum := by decide
  have hdescent : baseEnd_1843713 < baseStart_1843713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843724 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1843724 : Nat := 118140960795 + 1843724 * 2 ^ 59
def prefixEnd_1843724 : Nat := 4983230072969 + 3 ^ 40 * 1843724 * 2
def baseEnd_1843724 : Nat := 631144404153499770047249

theorem tailTrace_1843724 : CollatzResearch.WordTrace tailWord_1843724 prefixEnd_1843724 631144404153499770047249 := by
  unfold tailWord_1843724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623069386255152917597113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44830759181673537223462817 33623069386255152917597113)
  ·
    refine ⟨25217302039691364688197835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33623069386255152917597113 25217302039691364688197835)
    ·
      refine ⟨37825953059537047032296753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25217302039691364688197835 37825953059537047032296753)
      ·
        refine ⟨28369464794652785274222565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37825953059537047032296753 28369464794652785274222565)
        ·
          refine ⟨5319274648997397238916731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28369464794652785274222565 5319274648997397238916731)
          ·
            refine ⟨7978911973496095858375097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319274648997397238916731 7978911973496095858375097)
            ·
              refine ⟨5984183980122071893781323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7978911973496095858375097 5984183980122071893781323)
              ·
                refine ⟨8976275970183107840671985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984183980122071893781323 8976275970183107840671985)
                ·
                  refine ⟨6732206977637330880503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8976275970183107840671985 6732206977637330880503989)
                  ·
                    refine ⟨631144404153499770047249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6732206977637330880503989 631144404153499770047249)
                    ·
                      rfl

theorem cell22_1843724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1843724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843724 prefixEnd_1843724 := by exact prefixLift 1843724
  have htrace : WordTrace (prefixWord ++ tailWord_1843724) baseStart_1843724 baseEnd_1843724 := by
    simpa [prefixWord, tailWord_1843724, baseEnd_1843724] using wordTrace_append hprefix tailTrace_1843724
  have hstable : (prefixWord ++ tailWord_1843724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843724).length < 2 ^ (prefixWord ++ tailWord_1843724).sum := by decide
  have hdescent : baseEnd_1843724 < baseStart_1843724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843764 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1843764 : Nat := 118140960795 + 1843764 * 2 ^ 59
def prefixEnd_1843764 : Nat := 4983230072969 + 3 ^ 40 * 1843764 * 2
def baseEnd_1843764 : Nat := 631158096970952999047127

theorem tailTrace_1843764 : CollatzResearch.WordTrace tailWord_1843764 prefixEnd_1843764 631158096970952999047127 := by
  unfold tailWord_1843764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623798846182696333325173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44831731794910261777766897 33623798846182696333325173)
  ·
    refine ⟨3152231141829627781249235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33623798846182696333325173 3152231141829627781249235)
    ·
      refine ⟨4728346712744441671873853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152231141829627781249235 4728346712744441671873853)
      ·
        refine ⟨1773130017279165626952695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4728346712744441671873853 1773130017279165626952695)
        ·
          refine ⟨2659695025918748440429043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773130017279165626952695 2659695025918748440429043)
          ·
            refine ⟨3989542538878122660643565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659695025918748440429043 3989542538878122660643565)
            ·
              refine ⟨1496078452079295997741337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3989542538878122660643565 1496078452079295997741337)
              ·
                refine ⟨1122058839059471998306003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496078452079295997741337 1122058839059471998306003)
                ·
                  refine ⟨1683088258589207997459005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122058839059471998306003 1683088258589207997459005)
                  ·
                    refine ⟨631158096970952999047127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683088258589207997459005 631158096970952999047127)
                    ·
                      rfl

theorem cell22_1843764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1843764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843764 prefixEnd_1843764 := by exact prefixLift 1843764
  have htrace : WordTrace (prefixWord ++ tailWord_1843764) baseStart_1843764 baseEnd_1843764 := by
    simpa [prefixWord, tailWord_1843764, baseEnd_1843764] using wordTrace_append hprefix tailTrace_1843764
  have hstable : (prefixWord ++ tailWord_1843764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843764).length < 2 ^ (prefixWord ++ tailWord_1843764).sum := by decide
  have hdescent : baseEnd_1843764 < baseStart_1843764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843816 : List Nat := [2, 1, 4, 3, 3, 9]
def baseStart_1843816 : Nat := 118140960795 + 1843816 * 2 ^ 59
def prefixEnd_1843816 : Nat := 4983230072969 + 3 ^ 40 * 1843816 * 2
def baseEnd_1843816 : Nat := 7792295032514101194407

theorem tailTrace_1843816 : CollatzResearch.WordTrace tailWord_1843816 prefixEnd_1843816 7792295032514101194407 := by
  unfold tailWord_1843816
  simp only [CollatzResearch.WordTrace]
  refine ⟨33624747144088502773771651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44832996192118003698362201 33624747144088502773771651)
  ·
    refine ⟨50437120716132754160657477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33624747144088502773771651 50437120716132754160657477)
    ·
      refine ⟨9456960134274891405123277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50437120716132754160657477 9456960134274891405123277)
      ·
        refine ⟨3546360050353084276921229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9456960134274891405123277 3546360050353084276921229)
        ·
          refine ⟨1329885018882406603845461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3546360050353084276921229 1329885018882406603845461)
          ·
            refine ⟨7792295032514101194407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1329885018882406603845461 7792295032514101194407)
            ·
              rfl

theorem cell22_1843816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 9].length) (baseStart_1843816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843816 prefixEnd_1843816 := by exact prefixLift 1843816
  have htrace : WordTrace (prefixWord ++ tailWord_1843816) baseStart_1843816 baseEnd_1843816 := by
    simpa [prefixWord, tailWord_1843816, baseEnd_1843816] using wordTrace_append hprefix tailTrace_1843816
  have hstable : (prefixWord ++ tailWord_1843816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843816).length < 2 ^ (prefixWord ++ tailWord_1843816).sum := by decide
  have hdescent : baseEnd_1843816 < baseStart_1843816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843882 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1843882 : Nat := 118140960795 + 1843882 * 2 ^ 59
def prefixEnd_1843882 : Nat := 4983230072969 + 3 ^ 40 * 1843882 * 2
def baseEnd_1843882 : Nat := 631198490782440024596765

theorem tailTrace_1843882 : CollatzResearch.WordTrace tailWord_1843882 prefixEnd_1843882 631198490782440024596765 := by
  unfold tailWord_1843882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16812975376484474704861475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44834601003958599212963933 16812975376484474704861475)
  ·
    refine ⟨25219463064726712057292213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16812975376484474704861475 25219463064726712057292213)
    ·
      refine ⟨2364324662318129255371145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25219463064726712057292213 2364324662318129255371145)
      ·
        refine ⟨1773243496738596941528359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364324662318129255371145 1773243496738596941528359)
        ·
          refine ⟨2659865245107895412292539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773243496738596941528359 2659865245107895412292539)
          ·
            refine ⟨3989797867661843118438809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659865245107895412292539 3989797867661843118438809)
            ·
              refine ⟨2992348400746382338829107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989797867661843118438809 2992348400746382338829107)
              ·
                refine ⟨4488522601119573508243661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992348400746382338829107 4488522601119573508243661)
                ·
                  refine ⟨1683195975419840065591373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4488522601119573508243661 1683195975419840065591373)
                  ·
                    refine ⟨631198490782440024596765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683195975419840065591373 631198490782440024596765)
                    ·
                      rfl

theorem cell22_1843882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1843882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843882 prefixEnd_1843882 := by exact prefixLift 1843882
  have htrace : WordTrace (prefixWord ++ tailWord_1843882) baseStart_1843882 baseEnd_1843882 := by
    simpa [prefixWord, tailWord_1843882, baseEnd_1843882] using wordTrace_append hprefix tailTrace_1843882
  have hstable : (prefixWord ++ tailWord_1843882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843882).length < 2 ^ (prefixWord ++ tailWord_1843882).sum := by decide
  have hdescent : baseEnd_1843882 < baseStart_1843882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843908 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1843908 : Nat := 118140960795 + 1843908 * 2 ^ 59
def prefixEnd_1843908 : Nat := 4983230072969 + 3 ^ 40 * 1843908 * 2
def baseEnd_1843908 : Nat := 631207391113784623446685

theorem tailTrace_1843908 : CollatzResearch.WordTrace tailWord_1843908 prefixEnd_1843908 631207391113784623446685 := by
  unfold tailWord_1843908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626424901921852629946189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44835233202562470173261585 33626424901921852629946189)
  ·
    refine ⟨12609909338220694736229821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33626424901921852629946189 12609909338220694736229821)
    ·
      refine ⟨4728716001832760526086183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12609909338220694736229821 4728716001832760526086183)
      ·
        refine ⟨7093074002749140789129275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728716001832760526086183 7093074002749140789129275)
        ·
          refine ⟨10639611004123711183693913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093074002749140789129275 10639611004123711183693913)
          ·
            refine ⟨7979708253092783387770435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10639611004123711183693913 7979708253092783387770435)
            ·
              refine ⟨11969562379639175081655653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979708253092783387770435 11969562379639175081655653)
              ·
                refine ⟨2244292946182345327810435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11969562379639175081655653 2244292946182345327810435)
                ·
                  refine ⟨3366439419273517991715653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244292946182345327810435 3366439419273517991715653)
                  ·
                    refine ⟨631207391113784623446685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366439419273517991715653 631207391113784623446685)
                    ·
                      rfl

theorem cell22_1843908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1843908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843908 prefixEnd_1843908 := by exact prefixLift 1843908
  have htrace : WordTrace (prefixWord ++ tailWord_1843908) baseStart_1843908 baseEnd_1843908 := by
    simpa [prefixWord, tailWord_1843908, baseEnd_1843908] using wordTrace_append hprefix tailTrace_1843908
  have hstable : (prefixWord ++ tailWord_1843908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843908).length < 2 ^ (prefixWord ++ tailWord_1843908).sum := by decide
  have hdescent : baseEnd_1843908 < baseStart_1843908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843921 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_1843921 : Nat := 118140960795 + 1843921 * 2 ^ 59
def prefixEnd_1843921 : Nat := 4983230072969 + 3 ^ 40 * 1843921 * 2
def baseEnd_1843921 : Nat := 631211841279456922871645

theorem tailTrace_1843921 : CollatzResearch.WordTrace tailWord_1843921 prefixEnd_1843921 631211841279456922871645 := by
  unfold tailWord_1843921
  simp only [CollatzResearch.WordTrace]
  refine ⟨67253323952796608480115617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44835549301864405653410411 67253323952796608480115617)
  ·
    refine ⟨50439992964597456360086713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67253323952796608480115617 50439992964597456360086713)
    ·
      refine ⟨37829994723448092270065035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50439992964597456360086713 37829994723448092270065035)
      ·
        refine ⟨56744992085172138405097553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37829994723448092270065035 56744992085172138405097553)
        ·
          refine ⟨42558744063879103803823165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56744992085172138405097553 42558744063879103803823165)
          ·
            refine ⟨15959529023954663926433687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42558744063879103803823165 15959529023954663926433687)
            ·
              refine ⟨23939293535931995889650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15959529023954663926433687 23939293535931995889650531)
              ·
                refine ⟨35908940303897993834475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23939293535931995889650531 35908940303897993834475797)
                ·
                  refine ⟨1683231576745218460991053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35908940303897993834475797 1683231576745218460991053)
                  ·
                    refine ⟨631211841279456922871645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683231576745218460991053 631211841279456922871645)
                    ·
                      rfl

theorem cell22_1843921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_1843921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843921 prefixEnd_1843921 := by exact prefixLift 1843921
  have htrace : WordTrace (prefixWord ++ tailWord_1843921) baseStart_1843921 baseEnd_1843921 := by
    simpa [prefixWord, tailWord_1843921, baseEnd_1843921] using wordTrace_append hprefix tailTrace_1843921
  have hstable : (prefixWord ++ tailWord_1843921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843921).length < 2 ^ (prefixWord ++ tailWord_1843921).sum := by decide
  have hdescent : baseEnd_1843921 < baseStart_1843921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843940 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1843940 : Nat := 118140960795 + 1843940 * 2 ^ 59
def prefixEnd_1843940 : Nat := 4983230072969 + 3 ^ 40 * 1843940 * 2
def baseEnd_1843940 : Nat := 210406115122582402215529

theorem tailTrace_1843940 : CollatzResearch.WordTrace tailWord_1843940 prefixEnd_1843940 210406115122582402215529 := by
  unfold tailWord_1843940
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627008469863887362528637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44836011293151849816704849 33627008469863887362528637)
  ·
    refine ⟨12610128176198957760948239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33627008469863887362528637 12610128176198957760948239)
    ·
      refine ⟨18915192264298436641422359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12610128176198957760948239 18915192264298436641422359)
      ·
        refine ⟨28372788396447654962133539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18915192264298436641422359 28372788396447654962133539)
        ·
          refine ⟨42559182594671482443200309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28372788396447654962133539 42559182594671482443200309)
          ·
            refine ⟨3989923368250451479050029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42559182594671482443200309 3989923368250451479050029)
            ·
              refine ⟨1496221263093919304643761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3989923368250451479050029 1496221263093919304643761)
              ·
                refine ⟨1122165947320439478482821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496221263093919304643761 1122165947320439478482821)
                ·
                  refine ⟨210406115122582402215529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122165947320439478482821 210406115122582402215529)
                  ·
                    rfl

theorem cell22_1843940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1843940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843940 prefixEnd_1843940 := by exact prefixLift 1843940
  have htrace : WordTrace (prefixWord ++ tailWord_1843940) baseStart_1843940 baseEnd_1843940 := by
    simpa [prefixWord, tailWord_1843940, baseEnd_1843940] using wordTrace_append hprefix tailTrace_1843940
  have hstable : (prefixWord ++ tailWord_1843940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843940).length < 2 ^ (prefixWord ++ tailWord_1843940).sum := by decide
  have hdescent : baseEnd_1843940 < baseStart_1843940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843951 : List Nat := [1, 1, 2, 1, 5, 3, 2, 7]
def baseStart_1843951 : Nat := 118140960795 + 1843951 * 2 ^ 59
def prefixEnd_1843951 : Nat := 4983230072969 + 3 ^ 40 * 1843951 * 2
def baseEnd_1843951 : Nat := 70135790099171871624617

theorem tailTrace_1843951 : CollatzResearch.WordTrace tailWord_1843951 prefixEnd_1843951 70135790099171871624617 := by
  unfold tailWord_1843951
  simp only [CollatzResearch.WordTrace]
  refine ⟨67254418142687923603707707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44836278761791949069138471 67254418142687923603707707)
  ·
    refine ⟨100881627214031885405561561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67254418142687923603707707 100881627214031885405561561)
    ·
      refine ⟨75661220410523914054171171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100881627214031885405561561 75661220410523914054171171)
      ·
        refine ⟨113491830615785871081256757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75661220410523914054171171 113491830615785871081256757)
        ·
          refine ⟨10639859120229925413867821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113491830615785871081256757 10639859120229925413867821)
          ·
            refine ⟨3989947170086222030200433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10639859120229925413867821 3989947170086222030200433)
            ·
              refine ⟨2992460377564666522650325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989947170086222030200433 2992460377564666522650325)
              ·
                refine ⟨70135790099171871624617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2992460377564666522650325 70135790099171871624617)
                ·
                  rfl

theorem cell22_1843951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 7].length) (baseStart_1843951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843951 prefixEnd_1843951 := by exact prefixLift 1843951
  have htrace : WordTrace (prefixWord ++ tailWord_1843951) baseStart_1843951 baseEnd_1843951 := by
    simpa [prefixWord, tailWord_1843951, baseEnd_1843951] using wordTrace_append hprefix tailTrace_1843951
  have hstable : (prefixWord ++ tailWord_1843951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843951).length < 2 ^ (prefixWord ++ tailWord_1843951).sum := by decide
  have hdescent : baseEnd_1843951 < baseStart_1843951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843970 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1843970 : Nat := 118140960795 + 1843970 * 2 ^ 59
def prefixEnd_1843970 : Nat := 4983230072969 + 3 ^ 40 * 1843970 * 2
def baseEnd_1843970 : Nat := 631228614980837128396495

theorem tailTrace_1843970 : CollatzResearch.WordTrace tailWord_1843970 prefixEnd_1843970 631228614980837128396495 := by
  unfold tailWord_1843970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813777782404772462162341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44836740753079393232432909 16813777782404772462162341)
  ·
    refine ⟨3152583334200894836655439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16813777782404772462162341 3152583334200894836655439)
    ·
      refine ⟨4728875001301342254983159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152583334200894836655439 4728875001301342254983159)
      ·
        refine ⟨7093312501952013382474739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728875001301342254983159 7093312501952013382474739)
        ·
          refine ⟨10639968752928020073712109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093312501952013382474739 10639968752928020073712109)
          ·
            refine ⟨3989988282348007527642041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10639968752928020073712109 3989988282348007527642041)
            ·
              refine ⟨2992491211761005645731531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989988282348007527642041 2992491211761005645731531)
              ·
                refine ⟨4488736817641508468597297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992491211761005645731531 4488736817641508468597297)
                ·
                  refine ⟨3366552613231131351447973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488736817641508468597297 3366552613231131351447973)
                  ·
                    refine ⟨631228614980837128396495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366552613231131351447973 631228614980837128396495)
                    ·
                      rfl

theorem cell22_1843970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1843970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1843970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1843970 prefixEnd_1843970 := by exact prefixLift 1843970
  have htrace : WordTrace (prefixWord ++ tailWord_1843970) baseStart_1843970 baseEnd_1843970 := by
    simpa [prefixWord, tailWord_1843970, baseEnd_1843970] using wordTrace_append hprefix tailTrace_1843970
  have hstable : (prefixWord ++ tailWord_1843970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843970).length < 2 ^ (prefixWord ++ tailWord_1843970).sum := by decide
  have hdescent : baseEnd_1843970 < baseStart_1843970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844056 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_1844056 : Nat := 118140960795 + 1844056 * 2 ^ 59
def prefixEnd_1844056 : Nat := 4983230072969 + 3 ^ 40 * 1844056 * 2
def baseEnd_1844056 : Nat := 631258054538361570746231

theorem tailTrace_1844056 : CollatzResearch.WordTrace tailWord_1844056 prefixEnd_1844056 631258054538361570746231 := by
  unfold tailWord_1844056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33629123903653763268140011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44838831871538351024186681 33629123903653763268140011)
  ·
    refine ⟨50443685855480644902210017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33629123903653763268140011 50443685855480644902210017)
    ·
      refine ⟨37832764391610483676657513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50443685855480644902210017 37832764391610483676657513)
      ·
        refine ⟨28374573293707862757493135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37832764391610483676657513 28374573293707862757493135)
        ·
          refine ⟨42561859940561794136239703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28374573293707862757493135 42561859940561794136239703)
          ·
            refine ⟨63842789910842691204359555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42561859940561794136239703 63842789910842691204359555)
            ·
              refine ⟨95764184866264036806539333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63842789910842691204359555 95764184866264036806539333)
              ·
                refine ⟨17955784662424506901226125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95764184866264036806539333 17955784662424506901226125)
                ·
                  refine ⟨6733419248409190087959797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17955784662424506901226125 6733419248409190087959797)
                  ·
                    refine ⟨631258054538361570746231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6733419248409190087959797 631258054538361570746231)
                    ·
                      rfl

theorem cell22_1844056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_1844056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844056 prefixEnd_1844056 := by exact prefixLift 1844056
  have htrace : WordTrace (prefixWord ++ tailWord_1844056) baseStart_1844056 baseEnd_1844056 := by
    simpa [prefixWord, tailWord_1844056, baseEnd_1844056] using wordTrace_append hprefix tailTrace_1844056
  have hstable : (prefixWord ++ tailWord_1844056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844056).length < 2 ^ (prefixWord ++ tailWord_1844056).sum := by decide
  have hdescent : baseEnd_1844056 < baseStart_1844056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844058 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_1844058 : Nat := 118140960795 + 1844058 * 2 ^ 59
def prefixEnd_1844058 : Nat := 4983230072969 + 3 ^ 40 * 1844058 * 2
def baseEnd_1844058 : Nat := 210419579726411410732075

theorem tailTrace_1844058 : CollatzResearch.WordTrace tailWord_1844058 prefixEnd_1844058 210419579726411410732075 := by
  unfold tailWord_1844058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814580188325070219463207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44838880502200187251901885 16814580188325070219463207)
  ·
    refine ⟨25221870282487605329194811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16814580188325070219463207 25221870282487605329194811)
    ·
      refine ⟨37832805423731407993792217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25221870282487605329194811 37832805423731407993792217)
      ·
        refine ⟨28374604067798555995344163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37832805423731407993792217 28374604067798555995344163)
        ·
          refine ⟨42561906101697833993016245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28374604067798555995344163 42561906101697833993016245)
          ·
            refine ⟨3990178697034171936845273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42561906101697833993016245 3990178697034171936845273)
            ·
              refine ⟨2992634022775628952633955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990178697034171936845273 2992634022775628952633955)
              ·
                refine ⟨4488951034163443428950933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992634022775628952633955 4488951034163443428950933)
                ·
                  refine ⟨210419579726411410732075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4488951034163443428950933 210419579726411410732075)
                  ·
                    rfl

theorem cell22_1844058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_1844058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844058 prefixEnd_1844058 := by exact prefixLift 1844058
  have htrace : WordTrace (prefixWord ++ tailWord_1844058) baseStart_1844058 baseEnd_1844058 := by
    simpa [prefixWord, tailWord_1844058, baseEnd_1844058] using wordTrace_append hprefix tailTrace_1844058
  have hstable : (prefixWord ++ tailWord_1844058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844058).length < 2 ^ (prefixWord ++ tailWord_1844058).sum := by decide
  have hdescent : baseEnd_1844058 < baseStart_1844058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844103 : List Nat := [1, 1, 4, 2, 3, 3, 8]
def baseStart_1844103 : Nat := 118140960795 + 1844103 * 2 ^ 59
def prefixEnd_1844103 : Nat := 4983230072969 + 3 ^ 40 * 1844103 * 2
def baseEnd_1844103 : Nat := 23380523836995152400781

theorem tailTrace_1844103 : CollatzResearch.WordTrace tailWord_1844103 prefixEnd_1844103 23380523836995152400781 := by
  unfold tailWord_1844103
  simp only [CollatzResearch.WordTrace]
  refine ⟨67259962038137253563240963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44839974692091502375493975 67259962038137253563240963)
  ·
    refine ⟨100889943057205880344861445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67259962038137253563240963 100889943057205880344861445)
    ·
      refine ⟨18916864323226102564661521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100889943057205880344861445 18916864323226102564661521)
      ·
        refine ⟨14187648242419576923496141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18916864323226102564661521 14187648242419576923496141)
        ·
          refine ⟨5320368090907341346311053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14187648242419576923496141 5320368090907341346311053)
          ·
            refine ⟨1995138034090253004866645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5320368090907341346311053 1995138034090253004866645)
            ·
              refine ⟨23380523836995152400781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1995138034090253004866645 23380523836995152400781)
              ·
                rfl

theorem cell22_1844103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 8].length) (baseStart_1844103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844103 prefixEnd_1844103 := by exact prefixLift 1844103
  have htrace : WordTrace (prefixWord ++ tailWord_1844103) baseStart_1844103 baseEnd_1844103 := by
    simpa [prefixWord, tailWord_1844103, baseEnd_1844103] using wordTrace_append hprefix tailTrace_1844103
  have hstable : (prefixWord ++ tailWord_1844103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844103).length < 2 ^ (prefixWord ++ tailWord_1844103).sum := by decide
  have hdescent : baseEnd_1844103 < baseStart_1844103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844180 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1844180 : Nat := 118140960795 + 1844180 * 2 ^ 59
def prefixEnd_1844180 : Nat := 4983230072969 + 3 ^ 40 * 1844180 * 2
def baseEnd_1844180 : Nat := 631300502272466580645851

theorem tailTrace_1844180 : CollatzResearch.WordTrace tailWord_1844180 prefixEnd_1844180 631300502272466580645851 := by
  unfold tailWord_1844180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631385229429147856896997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44841846972572197142529329 33631385229429147856896997)
  ·
    refine ⟨6305884730517965223168187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33631385229429147856896997 6305884730517965223168187)
    ·
      refine ⟨9458827095776947834752281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305884730517965223168187 9458827095776947834752281)
      ·
        refine ⟨7094120321832710876064211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458827095776947834752281 7094120321832710876064211)
        ·
          refine ⟨10641180482749066314096317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094120321832710876064211 10641180482749066314096317)
          ·
            refine ⟨3990442681030899867786119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10641180482749066314096317 3990442681030899867786119)
            ·
              refine ⟨5985664021546349801679179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990442681030899867786119 5985664021546349801679179)
              ·
                refine ⟨8978496032319524702518769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985664021546349801679179 8978496032319524702518769)
                ·
                  refine ⟨6733872024239643526889077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978496032319524702518769 6733872024239643526889077)
                  ·
                    refine ⟨631300502272466580645851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6733872024239643526889077 631300502272466580645851)
                    ·
                      rfl

theorem cell22_1844180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1844180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844180 prefixEnd_1844180 := by exact prefixLift 1844180
  have htrace : WordTrace (prefixWord ++ tailWord_1844180) baseStart_1844180 baseEnd_1844180 := by
    simpa [prefixWord, tailWord_1844180, baseEnd_1844180] using wordTrace_append hprefix tailTrace_1844180
  have hstable : (prefixWord ++ tailWord_1844180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844180).length < 2 ^ (prefixWord ++ tailWord_1844180).sum := by decide
  have hdescent : baseEnd_1844180 < baseStart_1844180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844182 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_1844182 : Nat := 118140960795 + 1844182 * 2 ^ 59
def prefixEnd_1844182 : Nat := 4983230072969 + 3 ^ 40 * 1844182 * 2
def baseEnd_1844182 : Nat := 210433728971113080698615

theorem tailTrace_1844182 : CollatzResearch.WordTrace tailWord_1844182 prefixEnd_1844182 210433728971113080698615 := by
  unfold tailWord_1844182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203927712803190628460425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44841895603234033370244533 4203927712803190628460425)
  ·
    refine ⟨3152945784602392971345319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4203927712803190628460425 3152945784602392971345319)
    ·
      refine ⟨4729418676903589457017979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152945784602392971345319 4729418676903589457017979)
      ·
        refine ⟨7094128015355384185526969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729418676903589457017979 7094128015355384185526969)
        ·
          refine ⟨5320596011516538139145227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094128015355384185526969 5320596011516538139145227)
          ·
            refine ⟨7980894017274807208717841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320596011516538139145227 7980894017274807208717841)
            ·
              refine ⟨5985670512956105406538381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980894017274807208717841 5985670512956105406538381)
              ·
                refine ⟨2244626442358539527451893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5985670512956105406538381 2244626442358539527451893)
                ·
                  refine ⟨210433728971113080698615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2244626442358539527451893 210433728971113080698615)
                  ·
                    rfl

theorem cell22_1844182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_1844182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844182 prefixEnd_1844182 := by exact prefixLift 1844182
  have htrace : WordTrace (prefixWord ++ tailWord_1844182) baseStart_1844182 baseEnd_1844182 := by
    simpa [prefixWord, tailWord_1844182, baseEnd_1844182] using wordTrace_append hprefix tailTrace_1844182
  have hstable : (prefixWord ++ tailWord_1844182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844182).length < 2 ^ (prefixWord ++ tailWord_1844182).sum := by decide
  have hdescent : baseEnd_1844182 < baseStart_1844182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844195 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 1, 4]
def baseStart_1844195 : Nat := 118140960795 + 1844195 * 2 ^ 59
def prefixEnd_1844195 : Nat := 4983230072969 + 3 ^ 40 * 1844195 * 2
def baseEnd_1844195 : Nat := 631305637079011541520805

theorem tailTrace_1844195 : CollatzResearch.WordTrace tailWord_1844195 prefixEnd_1844195 631305637079011541520805 := by
  unfold tailWord_1844195
  simp only [CollatzResearch.WordTrace]
  refine ⟨67263317553803953275590039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44842211702535968850393359 67263317553803953275590039)
  ·
    refine ⟨100894976330705929913385059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67263317553803953275590039 100894976330705929913385059)
    ·
      refine ⟨151342464496058894870077589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100894976330705929913385059 151342464496058894870077589)
      ·
        refine ⟨7094178023252760697034887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151342464496058894870077589 7094178023252760697034887)
        ·
          refine ⟨10641267034879141045552331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094178023252760697034887 10641267034879141045552331)
          ·
            refine ⟨15961900552318711568328497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641267034879141045552331 15961900552318711568328497)
            ·
              refine ⟨11971425414239033676246373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15961900552318711568328497 11971425414239033676246373)
              ·
                refine ⟨2244642265169818814296195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11971425414239033676246373 2244642265169818814296195)
                ·
                  refine ⟨3366963397754728221444293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244642265169818814296195 3366963397754728221444293)
                  ·
                    refine ⟨631305637079011541520805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366963397754728221444293 631305637079011541520805)
                    ·
                      rfl

theorem cell22_1844195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 4].length) (baseStart_1844195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844195 prefixEnd_1844195 := by exact prefixLift 1844195
  have htrace : WordTrace (prefixWord ++ tailWord_1844195) baseStart_1844195 baseEnd_1844195 := by
    simpa [prefixWord, tailWord_1844195, baseEnd_1844195] using wordTrace_append hprefix tailTrace_1844195
  have hstable : (prefixWord ++ tailWord_1844195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844195).length < 2 ^ (prefixWord ++ tailWord_1844195).sum := by decide
  have hdescent : baseEnd_1844195 < baseStart_1844195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844255 : List Nat := [1, 1, 2, 4, 1, 3, 4, 6]
def baseStart_1844255 : Nat := 118140960795 + 1844255 * 2 ^ 59
def prefixEnd_1844255 : Nat := 4983230072969 + 3 ^ 40 * 1844255 * 2
def baseEnd_1844255 : Nat := 70147352922799042780069

theorem tailTrace_1844255 : CollatzResearch.WordTrace tailWord_1844255 prefixEnd_1844255 70147352922799042780069 := by
  unfold tailWord_1844255
  simp only [CollatzResearch.WordTrace]
  refine ⟨67265505933586583522774219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44843670622391055681849479 67265505933586583522774219)
  ·
    refine ⟨100898258900379875284161329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67265505933586583522774219 100898258900379875284161329)
    ·
      refine ⟨75673694175284906463120997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100898258900379875284161329 75673694175284906463120997)
      ·
        refine ⟨14188817657865919961835187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75673694175284906463120997 14188817657865919961835187)
        ·
          refine ⟨21283226486798879942752781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14188817657865919961835187 21283226486798879942752781)
          ·
            refine ⟨7981209932549579978532293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21283226486798879942752781 7981209932549579978532293)
            ·
              refine ⟨1496476862353046245974805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7981209932549579978532293 1496476862353046245974805)
              ·
                refine ⟨70147352922799042780069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1496476862353046245974805 70147352922799042780069)
                ·
                  rfl

theorem cell22_1844255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 6].length) (baseStart_1844255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844255 prefixEnd_1844255 := by exact prefixLift 1844255
  have htrace : WordTrace (prefixWord ++ tailWord_1844255) baseStart_1844255 baseEnd_1844255 := by
    simpa [prefixWord, tailWord_1844255, baseEnd_1844255] using wordTrace_append hprefix tailTrace_1844255
  have hstable : (prefixWord ++ tailWord_1844255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844255).length < 2 ^ (prefixWord ++ tailWord_1844255).sum := by decide
  have hdescent : baseEnd_1844255 < baseStart_1844255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844465 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_1844465 : Nat := 118140960795 + 1844465 * 2 ^ 59
def prefixEnd_1844465 : Nat := 4983230072969 + 3 ^ 40 * 1844465 * 2
def baseEnd_1844465 : Nat := 631398063596820837269977

theorem tailTrace_1844465 : CollatzResearch.WordTrace tailWord_1844465 prefixEnd_1844465 631398063596820837269977 := by
  unfold tailWord_1844465
  simp only [CollatzResearch.WordTrace]
  refine ⟨67273165262825789387918849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44848776841883859591945899 67273165262825789387918849)
  ·
    refine ⟨50454873947119342040939137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67273165262825789387918849 50454873947119342040939137)
    ·
      refine ⟨37841155460339506530704353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50454873947119342040939137 37841155460339506530704353)
      ·
        refine ⟨28380866595254629898028265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37841155460339506530704353 28380866595254629898028265)
        ·
          refine ⟨21285649946440972423521199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28380866595254629898028265 21285649946440972423521199)
          ·
            refine ⟨31928474919661458635281799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21285649946440972423521199 31928474919661458635281799)
            ·
              refine ⟨47892712379492187952922699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31928474919661458635281799 47892712379492187952922699)
              ·
                refine ⟨71839068569238281929384049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47892712379492187952922699 71839068569238281929384049)
                ·
                  refine ⟨53879301426928711447038037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71839068569238281929384049 53879301426928711447038037)
                  ·
                    refine ⟨631398063596820837269977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53879301426928711447038037 631398063596820837269977)
                    ·
                      rfl

theorem cell22_1844465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_1844465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844465 prefixEnd_1844465 := by exact prefixLift 1844465
  have htrace : WordTrace (prefixWord ++ tailWord_1844465) baseStart_1844465 baseEnd_1844465 := by
    simpa [prefixWord, tailWord_1844465, baseEnd_1844465] using wordTrace_append hprefix tailTrace_1844465
  have hstable : (prefixWord ++ tailWord_1844465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844465).length < 2 ^ (prefixWord ++ tailWord_1844465).sum := by decide
  have hdescent : baseEnd_1844465 < baseStart_1844465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844480 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 8]
def baseStart_1844480 : Nat := 118140960795 + 1844480 * 2 ^ 59
def prefixEnd_1844480 : Nat := 4983230072969 + 3 ^ 40 * 1844480 * 2
def baseEnd_1844480 : Nat := 210467732801121932714977

theorem tailTrace_1844480 : CollatzResearch.WordTrace tailWord_1844480 prefixEnd_1844480 210467732801121932714977 := by
  unfold tailWord_1844480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636856178885723474857447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44849141571847631299809929 33636856178885723474857447)
  ·
    refine ⟨50455284268328585212286171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33636856178885723474857447 50455284268328585212286171)
    ·
      refine ⟨75682926402492877818429257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50455284268328585212286171 75682926402492877818429257)
      ·
        refine ⟨56762194801869658363821943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75682926402492877818429257 56762194801869658363821943)
        ·
          refine ⟨85143292202804487545732915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56762194801869658363821943 85143292202804487545732915)
          ·
            refine ⟨127714938304206731318599373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85143292202804487545732915 127714938304206731318599373)
            ·
              refine ⟨47893101864077524244474765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127714938304206731318599373 47893101864077524244474765)
              ·
                refine ⟨17959913199029071591678037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47893101864077524244474765 17959913199029071591678037)
                ·
                  refine ⟨210467732801121932714977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17959913199029071591678037 210467732801121932714977)
                  ·
                    rfl

theorem cell22_1844480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_1844480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844480 prefixEnd_1844480 := by exact prefixLift 1844480
  have htrace : WordTrace (prefixWord ++ tailWord_1844480) baseStart_1844480 baseEnd_1844480 := by
    simpa [prefixWord, tailWord_1844480, baseEnd_1844480] using wordTrace_append hprefix tailTrace_1844480
  have hstable : (prefixWord ++ tailWord_1844480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844480).length < 2 ^ (prefixWord ++ tailWord_1844480).sum := by decide
  have hdescent : baseEnd_1844480 < baseStart_1844480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844529 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1844529 : Nat := 118140960795 + 1844529 * 2 ^ 59
def prefixEnd_1844529 : Nat := 4983230072969 + 3 ^ 40 * 1844529 * 2
def baseEnd_1844529 : Nat := 631419972104746003669781

theorem tailTrace_1844529 : CollatzResearch.WordTrace tailWord_1844529 prefixEnd_1844529 631419972104746003669781 := by
  unfold tailWord_1844529
  simp only [CollatzResearch.WordTrace]
  refine ⟨67275499534593928318248641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44850333023062618878832427 67275499534593928318248641)
  ·
    refine ⟨50456624650945446238686481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67275499534593928318248641 50456624650945446238686481)
    ·
      refine ⟨37842468488209084679014861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50456624650945446238686481 37842468488209084679014861)
      ·
        refine ⟨14190925683078406754630573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37842468488209084679014861 14190925683078406754630573)
        ·
          refine ⟨5321597131154402532986465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14190925683078406754630573 5321597131154402532986465)
          ·
            refine ⟨3991197848365801899739849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321597131154402532986465 3991197848365801899739849)
            ·
              refine ⟨2993398386274351424804887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991197848365801899739849 2993398386274351424804887)
              ·
                refine ⟨4490097579411527137207331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993398386274351424804887 4490097579411527137207331)
                ·
                  refine ⟨6735146369117290705810997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490097579411527137207331 6735146369117290705810997)
                  ·
                    refine ⟨631419972104746003669781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6735146369117290705810997 631419972104746003669781)
                    ·
                      rfl

theorem cell22_1844529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1844529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844529 prefixEnd_1844529 := by exact prefixLift 1844529
  have htrace : WordTrace (prefixWord ++ tailWord_1844529) baseStart_1844529 baseEnd_1844529 := by
    simpa [prefixWord, tailWord_1844529, baseEnd_1844529] using wordTrace_append hprefix tailTrace_1844529
  have hstable : (prefixWord ++ tailWord_1844529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844529).length < 2 ^ (prefixWord ++ tailWord_1844529).sum := by decide
  have hdescent : baseEnd_1844529 < baseStart_1844529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844548 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1844548 : Nat := 118140960795 + 1844548 * 2 ^ 59
def prefixEnd_1844548 : Nat := 4983230072969 + 3 ^ 40 * 1844548 * 2
def baseEnd_1844548 : Nat := 210475492064345429148241

theorem tailTrace_1844548 : CollatzResearch.WordTrace tailWord_1844548 prefixEnd_1844548 210475492064345429148241 := by
  unfold tailWord_1844548
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638096260762547281595149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44850795014350063042126865 33638096260762547281595149)
  ·
    refine ⟨12614286097785955230598181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33638096260762547281595149 12614286097785955230598181)
    ·
      refine ⟨2365178643334866605737159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12614286097785955230598181 2365178643334866605737159)
      ·
        refine ⟨3547767965002299908605739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365178643334866605737159 3547767965002299908605739)
        ·
          refine ⟨5321651947503449862908609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547767965002299908605739 5321651947503449862908609)
          ·
            refine ⟨3991238960627587397181457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321651947503449862908609 3991238960627587397181457)
            ·
              refine ⟨2993429220470690547886093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991238960627587397181457 2993429220470690547886093)
              ·
                refine ⟨1122535957676508955457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2993429220470690547886093 1122535957676508955457285)
                ·
                  refine ⟨210475492064345429148241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122535957676508955457285 210475492064345429148241)
                  ·
                    rfl

theorem cell22_1844548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1844548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844548 prefixEnd_1844548 := by exact prefixLift 1844548
  have htrace : WordTrace (prefixWord ++ tailWord_1844548) baseStart_1844548 baseEnd_1844548 := by
    simpa [prefixWord, tailWord_1844548, baseEnd_1844548] using wordTrace_append hprefix tailTrace_1844548
  have hstable : (prefixWord ++ tailWord_1844548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844548).length < 2 ^ (prefixWord ++ tailWord_1844548).sum := by decide
  have hdescent : baseEnd_1844548 < baseStart_1844548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844550 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1844550 : Nat := 118140960795 + 1844550 * 2 ^ 59
def prefixEnd_1844550 : Nat := 4983230072969 + 3 ^ 40 * 1844550 * 2
def baseEnd_1844550 : Nat := 631427160833908948894717

theorem tailTrace_1844550 : CollatzResearch.WordTrace tailWord_1844550 prefixEnd_1844550 631427160833908948894717 := by
  unfold tailWord_1844550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102383295859932778273847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44850843645011899269842069 2102383295859932778273847)
  ·
    refine ⟨3153574943789899167410771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102383295859932778273847 3153574943789899167410771)
    ·
      refine ⟨4730362415684848751116157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153574943789899167410771 4730362415684848751116157)
      ·
        refine ⟨1773885905881818281668559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4730362415684848751116157 1773885905881818281668559)
        ·
          refine ⟨2660828858822727422502839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773885905881818281668559 2660828858822727422502839)
          ·
            refine ⟨3991243288234091133754259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660828858822727422502839 3991243288234091133754259)
            ·
              refine ⟨5986864932351136700631389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991243288234091133754259 5986864932351136700631389)
              ·
                refine ⟨2245074349631676262736771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5986864932351136700631389 2245074349631676262736771)
                ·
                  refine ⟨3367611524447514394105157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245074349631676262736771 3367611524447514394105157)
                  ·
                    refine ⟨631427160833908948894717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367611524447514394105157 631427160833908948894717)
                    ·
                      rfl

theorem cell22_1844550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1844550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844550 prefixEnd_1844550 := by exact prefixLift 1844550
  have htrace : WordTrace (prefixWord ++ tailWord_1844550) baseStart_1844550 baseEnd_1844550 := by
    simpa [prefixWord, tailWord_1844550, baseEnd_1844550] using wordTrace_append hprefix tailTrace_1844550
  have hstable : (prefixWord ++ tailWord_1844550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844550).length < 2 ^ (prefixWord ++ tailWord_1844550).sum := by decide
  have hdescent : baseEnd_1844550 < baseStart_1844550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844634 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1844634 : Nat := 118140960795 + 1844634 * 2 ^ 59
def prefixEnd_1844634 : Nat := 4983230072969 + 3 ^ 40 * 1844634 * 2
def baseEnd_1844634 : Nat := 631455915750560729794459

theorem tailTrace_1844634 : CollatzResearch.WordTrace tailWord_1844634 prefixEnd_1844634 631455915750560729794459 := by
  unfold tailWord_1844634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819832299803382812705239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44852886132809020833880637 16819832299803382812705239)
  ·
    refine ⟨25229748449705074219057859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16819832299803382812705239 25229748449705074219057859)
    ·
      refine ⟨37844622674557611328586789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25229748449705074219057859 37844622674557611328586789)
      ·
        refine ⟨7095866751479552124110023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37844622674557611328586789 7095866751479552124110023)
        ·
          refine ⟨10643800127219328186165035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095866751479552124110023 10643800127219328186165035)
          ·
            refine ⟨15965700190828992279247553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643800127219328186165035 15965700190828992279247553)
            ·
              refine ⟨11974275143121744209435665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15965700190828992279247553 11974275143121744209435665)
              ·
                refine ⟨8980706357341308157076749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11974275143121744209435665 8980706357341308157076749)
                ·
                  refine ⟨3367764884002990558903781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8980706357341308157076749 3367764884002990558903781)
                  ·
                    refine ⟨631455915750560729794459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367764884002990558903781 631455915750560729794459)
                    ·
                      rfl

theorem cell22_1844634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1844634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844634 prefixEnd_1844634 := by exact prefixLift 1844634
  have htrace : WordTrace (prefixWord ++ tailWord_1844634) baseStart_1844634 baseEnd_1844634 := by
    simpa [prefixWord, tailWord_1844634, baseEnd_1844634] using wordTrace_append hprefix tailTrace_1844634
  have hstable : (prefixWord ++ tailWord_1844634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844634).length < 2 ^ (prefixWord ++ tailWord_1844634).sum := by decide
  have hdescent : baseEnd_1844634 < baseStart_1844634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844638 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1844638 : Nat := 118140960795 + 1844638 * 2 ^ 59
def prefixEnd_1844638 : Nat := 4983230072969 + 3 ^ 40 * 1844638 * 2
def baseEnd_1844638 : Nat := 210485761677435350898149

theorem tailTrace_1844638 : CollatzResearch.WordTrace tailWord_1844638 prefixEnd_1844638 210485761677435350898149 := by
  unfold tailWord_1844638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409934386399879991745821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44852983394132693289311045 8409934386399879991745821)
  ·
    refine ⟨3153725394899954996904683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8409934386399879991745821 3153725394899954996904683)
    ·
      refine ⟨4730588092349932495357025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153725394899954996904683 4730588092349932495357025)
      ·
        refine ⟨3547941069262449371517769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4730588092349932495357025 3547941069262449371517769)
        ·
          refine ⟨2660955801946837028638327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3547941069262449371517769 2660955801946837028638327)
          ·
            refine ⟨3991433702920255542957491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660955801946837028638327 3991433702920255542957491)
            ·
              refine ⟨5987150554380383314436237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991433702920255542957491 5987150554380383314436237)
              ·
                refine ⟨2245181457892643742913589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5987150554380383314436237 2245181457892643742913589)
                ·
                  refine ⟨210485761677435350898149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245181457892643742913589 210485761677435350898149)
                  ·
                    rfl

theorem cell22_1844638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1844638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844638 prefixEnd_1844638 := by exact prefixLift 1844638
  have htrace : WordTrace (prefixWord ++ tailWord_1844638) baseStart_1844638 baseEnd_1844638 := by
    simpa [prefixWord, tailWord_1844638, baseEnd_1844638] using wordTrace_append hprefix tailTrace_1844638
  have hstable : (prefixWord ++ tailWord_1844638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844638).length < 2 ^ (prefixWord ++ tailWord_1844638).sum := by decide
  have hdescent : baseEnd_1844638 < baseStart_1844638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844664 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 6, 3]
def baseStart_1844664 : Nat := 118140960795 + 1844664 * 2 ^ 59
def prefixEnd_1844664 : Nat := 4983230072969 + 3 ^ 40 * 1844664 * 2
def baseEnd_1844664 : Nat := 631466185363650651544367

theorem tailTrace_1844664 : CollatzResearch.WordTrace tailWord_1844664 prefixEnd_1844664 631466185363650651544367 := by
  unfold tailWord_1844664
  simp only [CollatzResearch.WordTrace]
  refine ⟨33640211694552423187206523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44853615592736564249608697 33640211694552423187206523)
  ·
    refine ⟨50460317541828634780809785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33640211694552423187206523 50460317541828634780809785)
    ·
      refine ⟨37845238156371476085607339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50460317541828634780809785 37845238156371476085607339)
      ·
        refine ⟨56767857234557214128411009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37845238156371476085607339 56767857234557214128411009)
        ·
          refine ⟨42575892925917910596308257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56767857234557214128411009 42575892925917910596308257)
          ·
            refine ⟨31931919694438432947231193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42575892925917910596308257 31931919694438432947231193)
            ·
              refine ⟨23948939770828824710423395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31931919694438432947231193 23948939770828824710423395)
              ·
                refine ⟨35923409656243237065635093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23948939770828824710423395 35923409656243237065635093)
                ·
                  refine ⟨1683909827636401737451645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35923409656243237065635093 1683909827636401737451645)
                  ·
                    refine ⟨631466185363650651544367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683909827636401737451645 631466185363650651544367)
                    ·
                      rfl

theorem cell22_1844664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_1844664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844664 prefixEnd_1844664 := by exact prefixLift 1844664
  have htrace : WordTrace (prefixWord ++ tailWord_1844664) baseStart_1844664 baseEnd_1844664 := by
    simpa [prefixWord, tailWord_1844664, baseEnd_1844664] using wordTrace_append hprefix tailTrace_1844664
  have hstable : (prefixWord ++ tailWord_1844664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844664).length < 2 ^ (prefixWord ++ tailWord_1844664).sum := by decide
  have hdescent : baseEnd_1844664 < baseStart_1844664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844679 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1844679 : Nat := 118140960795 + 1844679 * 2 ^ 59
def prefixEnd_1844679 : Nat := 4983230072969 + 3 ^ 40 * 1844679 * 2
def baseEnd_1844679 : Nat := 631471320170195612419321

theorem tailTrace_1844679 : CollatzResearch.WordTrace tailWord_1844679 prefixEnd_1844679 631471320170195612419321 := by
  unfold tailWord_1844679
  simp only [CollatzResearch.WordTrace]
  refine ⟨67280970484050503936209091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44853980322700335957472727 67280970484050503936209091)
  ·
    refine ⟨100921455726075755904313637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67280970484050503936209091 100921455726075755904313637)
    ·
      refine ⟨18922772948639204232058807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100921455726075755904313637 18922772948639204232058807)
      ·
        refine ⟨28384159422958806348088211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18922772948639204232058807 28384159422958806348088211)
        ·
          refine ⟨42576239134438209522132317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28384159422958806348088211 42576239134438209522132317)
          ·
            refine ⟨15966089675414328570799619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42576239134438209522132317 15966089675414328570799619)
            ·
              refine ⟨23949134513121492856199429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966089675414328570799619 23949134513121492856199429)
              ·
                refine ⟨4490462721210279910537393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23949134513121492856199429 4490462721210279910537393)
                ·
                  refine ⟨3367847040907709932903045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490462721210279910537393 3367847040907709932903045)
                  ·
                    refine ⟨631471320170195612419321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367847040907709932903045 631471320170195612419321)
                    ·
                      rfl

theorem cell22_1844679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1844679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844679 prefixEnd_1844679 := by exact prefixLift 1844679
  have htrace : WordTrace (prefixWord ++ tailWord_1844679) baseStart_1844679 baseEnd_1844679 := by
    simpa [prefixWord, tailWord_1844679, baseEnd_1844679] using wordTrace_append hprefix tailTrace_1844679
  have hstable : (prefixWord ++ tailWord_1844679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844679).length < 2 ^ (prefixWord ++ tailWord_1844679).sum := by decide
  have hdescent : baseEnd_1844679 < baseStart_1844679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844711 : List Nat := [1, 1, 5, 2, 1, 3, 3, 6]
def baseStart_1844711 : Nat := 118140960795 + 1844711 * 2 ^ 59
def prefixEnd_1844711 : Nat := 4983230072969 + 3 ^ 40 * 1844711 * 2
def baseEnd_1844711 : Nat := 70164697158239799513247

theorem tailTrace_1844711 : CollatzResearch.WordTrace tailWord_1844711 prefixEnd_1844711 70164697158239799513247 := by
  unfold tailWord_1844711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67282137619934573401373987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44854758413289715600915991 67282137619934573401373987)
  ·
    refine ⟨100923206429901860102060981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67282137619934573401373987 100923206429901860102060981)
    ·
      refine ⟨9461550602803299384568217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100923206429901860102060981 9461550602803299384568217)
      ·
        refine ⟨7096162952102474538426163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9461550602803299384568217 7096162952102474538426163)
        ·
          refine ⟨10644244428153711807639245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096162952102474538426163 10644244428153711807639245)
          ·
            refine ⟨3991591660557641927864717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10644244428153711807639245 3991591660557641927864717)
            ·
              refine ⟨1496846872709115722949269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3991591660557641927864717 1496846872709115722949269)
              ·
                refine ⟨70164697158239799513247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1496846872709115722949269 70164697158239799513247)
                ·
                  rfl

theorem cell22_1844711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 6].length) (baseStart_1844711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844711 prefixEnd_1844711 := by exact prefixLift 1844711
  have htrace : WordTrace (prefixWord ++ tailWord_1844711) baseStart_1844711 baseEnd_1844711 := by
    simpa [prefixWord, tailWord_1844711, baseEnd_1844711] using wordTrace_append hprefix tailTrace_1844711
  have hstable : (prefixWord ++ tailWord_1844711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844711).length < 2 ^ (prefixWord ++ tailWord_1844711).sum := by decide
  have hdescent : baseEnd_1844711 < baseStart_1844711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844739 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 5]
def baseStart_1844739 : Nat := 118140960795 + 1844739 * 2 ^ 59
def prefixEnd_1844739 : Nat := 4983230072969 + 3 ^ 40 * 1844739 * 2
def baseEnd_1844739 : Nat := 210497286465458485306379

theorem tailTrace_1844739 : CollatzResearch.WordTrace tailWord_1844739 prefixEnd_1844739 210497286465458485306379 := by
  unfold tailWord_1844739
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283158863833134183393271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855439242555422788928847 67283158863833134183393271)
  ·
    refine ⟨100924738295749701275089907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67283158863833134183393271 100924738295749701275089907)
    ·
      refine ⟨151387107443624551912634861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100924738295749701275089907 151387107443624551912634861)
      ·
        refine ⟨56770165291359206967238073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151387107443624551912634861 56770165291359206967238073)
        ·
          refine ⟨42577623968519405225428555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56770165291359206967238073 42577623968519405225428555)
          ·
            refine ⟨63866435952779107838142833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42577623968519405225428555 63866435952779107838142833)
            ·
              refine ⟨47899826964584330878607125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63866435952779107838142833 47899826964584330878607125)
              ·
                refine ⟨2245304388964890509934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47899826964584330878607125 2245304388964890509934709)
                ·
                  refine ⟨210497286465458485306379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245304388964890509934709 210497286465458485306379)
                  ·
                    rfl

theorem cell22_1844739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 5].length) (baseStart_1844739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844739 prefixEnd_1844739 := by exact prefixLift 1844739
  have htrace : WordTrace (prefixWord ++ tailWord_1844739) baseStart_1844739 baseEnd_1844739 := by
    simpa [prefixWord, tailWord_1844739, baseEnd_1844739] using wordTrace_append hprefix tailTrace_1844739
  have hstable : (prefixWord ++ tailWord_1844739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844739).length < 2 ^ (prefixWord ++ tailWord_1844739).sum := by decide
  have hdescent : baseEnd_1844739 < baseStart_1844739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844743 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1844743 : Nat := 118140960795 + 1844743 * 2 ^ 59
def prefixEnd_1844743 : Nat := 4983230072969 + 3 ^ 40 * 1844743 * 2
def baseEnd_1844743 : Nat := 631493228678120778819125

theorem tailTrace_1844743 : CollatzResearch.WordTrace tailWord_1844743 prefixEnd_1844743 631493228678120778819125 := by
  unfold tailWord_1844743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283304755818642866538883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855536503879095244359255 67283304755818642866538883)
  ·
    refine ⟨100924957133727964299808325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67283304755818642866538883 100924957133727964299808325)
    ·
      refine ⟨18923429462573993306214061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100924957133727964299808325 18923429462573993306214061)
      ·
        refine ⟨7096286048465247489830273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18923429462573993306214061 7096286048465247489830273)
        ·
          refine ⟨5322214536348935617372705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096286048465247489830273 5322214536348935617372705)
          ·
            refine ⟨3991660902261701713029529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322214536348935617372705 3991660902261701713029529)
            ·
              refine ⟨2993745676696276284772147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991660902261701713029529 2993745676696276284772147)
              ·
                refine ⟨4490618515044414427158221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993745676696276284772147 4490618515044414427158221)
                ·
                  refine ⟨1683981943141655410184333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4490618515044414427158221 1683981943141655410184333)
                  ·
                    refine ⟨631493228678120778819125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683981943141655410184333 631493228678120778819125)
                    ·
                      rfl

theorem cell22_1844743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1844743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844743 prefixEnd_1844743 := by exact prefixLift 1844743
  have htrace : WordTrace (prefixWord ++ tailWord_1844743) baseStart_1844743 baseEnd_1844743 := by
    simpa [prefixWord, tailWord_1844743, baseEnd_1844743] using wordTrace_append hprefix tailTrace_1844743
  have hstable : (prefixWord ++ tailWord_1844743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844743).length < 2 ^ (prefixWord ++ tailWord_1844743).sum := by decide
  have hdescent : baseEnd_1844743 < baseStart_1844743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844749 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1844749 : Nat := 118140960795 + 1844749 * 2 ^ 59
def prefixEnd_1844749 : Nat := 4983230072969 + 3 ^ 40 * 1844749 * 2
def baseEnd_1844749 : Nat := 631495282600738763169107

theorem tailTrace_1844749 : CollatzResearch.WordTrace tailWord_1844749 prefixEnd_1844749 631495282600738763169107 := by
  unfold tailWord_1844749
  simp only [CollatzResearch.WordTrace]
  refine ⟨67283523593796905891257301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44855682395864603927504867 67283523593796905891257301)
  ·
    refine ⟨1576957584229614981826343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67283523593796905891257301 1576957584229614981826343)
    ·
      refine ⟨2365436376344422472739515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576957584229614981826343 2365436376344422472739515)
      ·
        refine ⟨3548154564516633709109273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365436376344422472739515 3548154564516633709109273)
        ·
          refine ⟨2661115923387475281831955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548154564516633709109273 2661115923387475281831955)
          ·
            refine ⟨3991673885081212922747933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661115923387475281831955 3991673885081212922747933)
            ·
              refine ⟨1496877706905454846030475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3991673885081212922747933 1496877706905454846030475)
              ·
                refine ⟨2245316560358182269045713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496877706905454846030475 2245316560358182269045713)
                ·
                  refine ⟨1683987420268636701784285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245316560358182269045713 1683987420268636701784285)
                  ·
                    refine ⟨631495282600738763169107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683987420268636701784285 631495282600738763169107)
                    ·
                      rfl

theorem cell22_1844749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1844749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844749 prefixEnd_1844749 := by exact prefixLift 1844749
  have htrace : WordTrace (prefixWord ++ tailWord_1844749) baseStart_1844749 baseEnd_1844749 := by
    simpa [prefixWord, tailWord_1844749, baseEnd_1844749] using wordTrace_append hprefix tailTrace_1844749
  have hstable : (prefixWord ++ tailWord_1844749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844749).length < 2 ^ (prefixWord ++ tailWord_1844749).sum := by decide
  have hdescent : baseEnd_1844749 < baseStart_1844749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844846 : List Nat := [4, 1, 2, 2, 3, 10]
def baseStart_1844846 : Nat := 118140960795 + 1844846 * 2 ^ 59
def prefixEnd_1844846 : Nat := 4983230072969 + 3 ^ 40 * 1844846 * 2
def baseEnd_1844846 : Nat := 7796647996087195598689

theorem tailTrace_1844846 : CollatzResearch.WordTrace tailWord_1844846 prefixEnd_1844846 7796647996087195598689 := by
  unfold tailWord_1844846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410882684305686432192299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44858040982963660971692261 8410882684305686432192299)
  ·
    refine ⟨12616324026458529648288449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410882684305686432192299 12616324026458529648288449)
    ·
      refine ⟨9462243019843897236216337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12616324026458529648288449 9462243019843897236216337)
      ·
        refine ⟨7096682264882922927162253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9462243019843897236216337 7096682264882922927162253)
        ·
          refine ⟨2661255849331096097685845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7096682264882922927162253 2661255849331096097685845)
          ·
            refine ⟨7796647996087195598689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2661255849331096097685845 7796647996087195598689)
            ·
              rfl

theorem cell22_1844846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 10].length) (baseStart_1844846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844846 prefixEnd_1844846 := by exact prefixLift 1844846
  have htrace : WordTrace (prefixWord ++ tailWord_1844846) baseStart_1844846 baseEnd_1844846 := by
    simpa [prefixWord, tailWord_1844846, baseEnd_1844846] using wordTrace_append hprefix tailTrace_1844846
  have hstable : (prefixWord ++ tailWord_1844846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844846).length < 2 ^ (prefixWord ++ tailWord_1844846).sum := by decide
  have hdescent : baseEnd_1844846 < baseStart_1844846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844850 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1844850 : Nat := 118140960795 + 1844850 * 2 ^ 59
def prefixEnd_1844850 : Nat := 4983230072969 + 3 ^ 40 * 1844850 * 2
def baseEnd_1844850 : Nat := 631529856964808166393797

theorem tailTrace_1844850 : CollatzResearch.WordTrace tailWord_1844850 prefixEnd_1844850 631529856964808166393797 := by
  unfold tailWord_1844850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821801841607750035171001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44858138244287333427122669 16821801841607750035171001)
  ·
    refine ⟨12616351381205812526378251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16821801841607750035171001 12616351381205812526378251)
    ·
      refine ⟨18924527071808718789567377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12616351381205812526378251 18924527071808718789567377)
      ·
        refine ⟨14193395303856539092175533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18924527071808718789567377 14193395303856539092175533)
        ·
          refine ⟨5322523238946202159565825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14193395303856539092175533 5322523238946202159565825)
          ·
            refine ⟨3991892429209651619674369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322523238946202159565825 3991892429209651619674369)
            ·
              refine ⟨2993919321907238714755777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991892429209651619674369 2993919321907238714755777)
              ·
                refine ⟨2245439491430429036066833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993919321907238714755777 2245439491430429036066833)
                ·
                  refine ⟨1684079618572821777050125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245439491430429036066833 1684079618572821777050125)
                  ·
                    refine ⟨631529856964808166393797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684079618572821777050125 631529856964808166393797)
                    ·
                      rfl

theorem cell22_1844850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1844850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844850 prefixEnd_1844850 := by exact prefixLift 1844850
  have htrace : WordTrace (prefixWord ++ tailWord_1844850) baseStart_1844850 baseEnd_1844850 := by
    simpa [prefixWord, tailWord_1844850, baseEnd_1844850] using wordTrace_append hprefix tailTrace_1844850
  have hstable : (prefixWord ++ tailWord_1844850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844850).length < 2 ^ (prefixWord ++ tailWord_1844850).sum := by decide
  have hdescent : baseEnd_1844850 < baseStart_1844850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844859 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 8]
def baseStart_1844859 : Nat := 118140960795 + 1844859 * 2 ^ 59
def prefixEnd_1844859 : Nat := 4983230072969 + 3 ^ 40 * 1844859 * 2
def baseEnd_1844859 : Nat := 631532937848735142918769

theorem tailTrace_1844859 : CollatzResearch.WordTrace tailWord_1844859 prefixEnd_1844859 631532937848735142918769 := by
  unfold tailWord_1844859
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287535623398394677761631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44858357082265596451841087 67287535623398394677761631)
  ·
    refine ⟨100931303435097592016642447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67287535623398394677761631 100931303435097592016642447)
    ·
      refine ⟨151396955152646388024963671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100931303435097592016642447 151396955152646388024963671)
      ·
        refine ⟨227095432728969582037445507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151396955152646388024963671 227095432728969582037445507)
        ·
          refine ⟨340643149093454373056168261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227095432728969582037445507 340643149093454373056168261)
          ·
            refine ⟨63870590455022694948031549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340643149093454373056168261 63870590455022694948031549)
            ·
              refine ⟨23951471420633510605511831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63870590455022694948031549 23951471420633510605511831)
              ·
                refine ⟨35927207130950265908267747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23951471420633510605511831 35927207130950265908267747)
                ·
                  refine ⟨53890810696425398862401621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35927207130950265908267747 53890810696425398862401621)
                  ·
                    refine ⟨631532937848735142918769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53890810696425398862401621 631532937848735142918769)
                    ·
                      rfl

theorem cell22_1844859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_1844859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844859 prefixEnd_1844859 := by exact prefixLift 1844859
  have htrace : WordTrace (prefixWord ++ tailWord_1844859) baseStart_1844859 baseEnd_1844859 := by
    simpa [prefixWord, tailWord_1844859, baseEnd_1844859] using wordTrace_append hprefix tailTrace_1844859
  have hstable : (prefixWord ++ tailWord_1844859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844859).length < 2 ^ (prefixWord ++ tailWord_1844859).sum := by decide
  have hdescent : baseEnd_1844859 < baseStart_1844859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844878 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_1844878 : Nat := 118140960795 + 1844878 * 2 ^ 59
def prefixEnd_1844878 : Nat := 4983230072969 + 3 ^ 40 * 1844878 * 2
def baseEnd_1844878 : Nat := 631539441937025426693711

theorem tailTrace_1844878 : CollatzResearch.WordTrace tailWord_1844878 prefixEnd_1844878 631539441937025426693711 := by
  unfold tailWord_1844878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411028576291195115337911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44858819073553040615135525 8411028576291195115337911)
  ·
    refine ⟨12616542864436792673006867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8411028576291195115337911 12616542864436792673006867)
    ·
      refine ⟨18924814296655189009510301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12616542864436792673006867 18924814296655189009510301)
      ·
        refine ⟨7096805361245695878566363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18924814296655189009510301 7096805361245695878566363)
        ·
          refine ⟨10645208041868543817849545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096805361245695878566363 10645208041868543817849545)
          ·
            refine ⟨7983906031401407863387159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10645208041868543817849545 7983906031401407863387159)
            ·
              refine ⟨11975859047102111795080739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983906031401407863387159 11975859047102111795080739)
              ·
                refine ⟨17963788570653167692621109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975859047102111795080739 17963788570653167692621109)
                ·
                  refine ⟨1684105178498734471183229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17963788570653167692621109 1684105178498734471183229)
                  ·
                    refine ⟨631539441937025426693711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684105178498734471183229 631539441937025426693711)
                    ·
                      rfl

theorem cell22_1844878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_1844878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844878 prefixEnd_1844878 := by exact prefixLift 1844878
  have htrace : WordTrace (prefixWord ++ tailWord_1844878) baseStart_1844878 baseEnd_1844878 := by
    simpa [prefixWord, tailWord_1844878, baseEnd_1844878] using wordTrace_append hprefix tailTrace_1844878
  have hstable : (prefixWord ++ tailWord_1844878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844878).length < 2 ^ (prefixWord ++ tailWord_1844878).sum := by decide
  have hdescent : baseEnd_1844878 < baseStart_1844878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844882 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1844882 : Nat := 118140960795 + 1844882 * 2 ^ 59
def prefixEnd_1844882 : Nat := 4983230072969 + 3 ^ 40 * 1844882 * 2
def baseEnd_1844882 : Nat := 631540811218770749593699

theorem tailTrace_1844882 : CollatzResearch.WordTrace tailWord_1844882 prefixEnd_1844882 631540811218770749593699 := by
  unfold tailWord_1844882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822093625578767401462225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44858916334876713070565933 16822093625578767401462225)
  ·
    refine ⟨12616570219184075551096669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16822093625578767401462225 12616570219184075551096669)
    ·
      refine ⟨4731213832194028331661251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12616570219184075551096669 4731213832194028331661251)
      ·
        refine ⟨7096820748291042497491877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731213832194028331661251 7096820748291042497491877)
        ·
          refine ⟨1330653890304570468279727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7096820748291042497491877 1330653890304570468279727)
          ·
            refine ⟨1995980835456855702419591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330653890304570468279727 1995980835456855702419591)
            ·
              refine ⟨2993971253185283553629387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995980835456855702419591 2993971253185283553629387)
              ·
                refine ⟨4490956879777925330444081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993971253185283553629387 4490956879777925330444081)
                ·
                  refine ⟨3368217659833443997833061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490956879777925330444081 3368217659833443997833061)
                  ·
                    refine ⟨631540811218770749593699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368217659833443997833061 631540811218770749593699)
                    ·
                      rfl

theorem cell22_1844882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1844882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844882 prefixEnd_1844882 := by exact prefixLift 1844882
  have htrace : WordTrace (prefixWord ++ tailWord_1844882) baseStart_1844882 baseEnd_1844882 := by
    simpa [prefixWord, tailWord_1844882, baseEnd_1844882] using wordTrace_append hprefix tailTrace_1844882
  have hstable : (prefixWord ++ tailWord_1844882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844882).length < 2 ^ (prefixWord ++ tailWord_1844882).sum := by decide
  have hdescent : baseEnd_1844882 < baseStart_1844882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844921 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_1844921 : Nat := 118140960795 + 1844921 * 2 ^ 59
def prefixEnd_1844921 : Nat := 4983230072969 + 3 ^ 40 * 1844921 * 2
def baseEnd_1844921 : Nat := 631554161715787647868579

theorem tailTrace_1844921 : CollatzResearch.WordTrace tailWord_1844921 prefixEnd_1844921 631554161715787647868579 := by
  unfold tailWord_1844921
  simp only [CollatzResearch.WordTrace]
  refine ⟨67289796949173779266518617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44859864632782519511012411 67289796949173779266518617)
  ·
    refine ⟨50467347711880334449888963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67289796949173779266518617 50467347711880334449888963)
    ·
      refine ⟨75701021567820501674833445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50467347711880334449888963 75701021567820501674833445)
      ·
        refine ⟨14193941543966344064031271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75701021567820501674833445 14193941543966344064031271)
        ·
          refine ⟨21290912315949516096046907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14193941543966344064031271 21290912315949516096046907)
          ·
            refine ⟨31936368473924274144070361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21290912315949516096046907 31936368473924274144070361)
            ·
              refine ⟨23952276355443205608052771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31936368473924274144070361 23952276355443205608052771)
              ·
                refine ⟨35928414533164808412079157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23952276355443205608052771 35928414533164808412079157)
                ·
                  refine ⟨3368288862484200788632421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35928414533164808412079157 3368288862484200788632421)
                  ·
                    refine ⟨631554161715787647868579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368288862484200788632421 631554161715787647868579)
                    ·
                      rfl

theorem cell22_1844921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_1844921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844921 prefixEnd_1844921 := by exact prefixLift 1844921
  have htrace : WordTrace (prefixWord ++ tailWord_1844921) baseStart_1844921 baseEnd_1844921 := by
    simpa [prefixWord, tailWord_1844921, baseEnd_1844921] using wordTrace_append hprefix tailTrace_1844921
  have hstable : (prefixWord ++ tailWord_1844921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844921).length < 2 ^ (prefixWord ++ tailWord_1844921).sum := by decide
  have hdescent : baseEnd_1844921 < baseStart_1844921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844936 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 6]
def baseStart_1844936 : Nat := 118140960795 + 1844936 * 2 ^ 59
def prefixEnd_1844936 : Nat := 4983230072969 + 3 ^ 40 * 1844936 * 2
def baseEnd_1844936 : Nat := 210519765507444202914511

theorem tailTrace_1844936 : CollatzResearch.WordTrace tailWord_1844936 prefixEnd_1844936 210519765507444202914511 := by
  unfold tailWord_1844936
  simp only [CollatzResearch.WordTrace]
  refine ⟨33645172022059718414157331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44860229362746291218876441 33645172022059718414157331)
  ·
    refine ⟨50467758033089577621235997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33645172022059718414157331 50467758033089577621235997)
    ·
      refine ⟨18925409262408591607963499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50467758033089577621235997 18925409262408591607963499)
      ·
        refine ⟨28388113893612887411945249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18925409262408591607963499 28388113893612887411945249)
        ·
          refine ⟨21291085420209665558958937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28388113893612887411945249 21291085420209665558958937)
          ·
            refine ⟨15968314065157249169219203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21291085420209665558958937 15968314065157249169219203)
            ·
              refine ⟨23952471097735873753828805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15968314065157249169219203 23952471097735873753828805)
              ·
                refine ⟨4491088330825476328842901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23952471097735873753828805 4491088330825476328842901)
                ·
                  refine ⟨210519765507444202914511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4491088330825476328842901 210519765507444202914511)
                  ·
                    rfl

theorem cell22_1844936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_1844936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844936 prefixEnd_1844936 := by exact prefixLift 1844936
  have htrace : WordTrace (prefixWord ++ tailWord_1844936) baseStart_1844936 baseEnd_1844936 := by
    simpa [prefixWord, tailWord_1844936, baseEnd_1844936] using wordTrace_append hprefix tailTrace_1844936
  have hstable : (prefixWord ++ tailWord_1844936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844936).length < 2 ^ (prefixWord ++ tailWord_1844936).sum := by decide
  have hdescent : baseEnd_1844936 < baseStart_1844936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844951 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1844951 : Nat := 118140960795 + 1844951 * 2 ^ 59
def prefixEnd_1844951 : Nat := 4983230072969 + 3 ^ 40 * 1844951 * 2
def baseEnd_1844951 : Nat := 631564431328877569618487

theorem tailTrace_1844951 : CollatzResearch.WordTrace tailWord_1844951 prefixEnd_1844951 631564431328877569618487 := by
  unfold tailWord_1844951
  simp only [CollatzResearch.WordTrace]
  refine ⟨67290891139065094390110707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44860594092710062926740471 67290891139065094390110707)
  ·
    refine ⟨100936336708597641585166061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67290891139065094390110707 100936336708597641585166061)
    ·
      refine ⟨37851126265724115594437273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100936336708597641585166061 37851126265724115594437273)
      ·
        refine ⟨28388344699293086695827955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37851126265724115594437273 28388344699293086695827955)
        ·
          refine ⟨42582517048939630043741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28388344699293086695827955 42582517048939630043741933)
          ·
            refine ⟨15968443893352361266403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42582517048939630043741933 15968443893352361266403225)
            ·
              refine ⟨11976332920014270949802419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15968443893352361266403225 11976332920014270949802419)
              ·
                refine ⟨17964499380021406424703629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976332920014270949802419 17964499380021406424703629)
                ·
                  refine ⟨6736687267508027409263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17964499380021406424703629 6736687267508027409263861)
                  ·
                    refine ⟨631564431328877569618487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6736687267508027409263861 631564431328877569618487)
                    ·
                      rfl

theorem cell22_1844951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1844951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1844951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1844951 prefixEnd_1844951 := by exact prefixLift 1844951
  have htrace : WordTrace (prefixWord ++ tailWord_1844951) baseStart_1844951 baseEnd_1844951 := by
    simpa [prefixWord, tailWord_1844951, baseEnd_1844951] using wordTrace_append hprefix tailTrace_1844951
  have hstable : (prefixWord ++ tailWord_1844951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844951).length < 2 ^ (prefixWord ++ tailWord_1844951).sum := by decide
  have hdescent : baseEnd_1844951 < baseStart_1844951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845028 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1845028 : Nat := 118140960795 + 1845028 * 2 ^ 59
def prefixEnd_1845028 : Nat := 4983230072969 + 3 ^ 40 * 1845028 * 2
def baseEnd_1845028 : Nat := 631590790002475035443251

theorem tailTrace_1845028 : CollatzResearch.WordTrace tailWord_1845028 prefixEnd_1845028 631590790002475035443251 := by
  unfold tailWord_1845028
  simp only [CollatzResearch.WordTrace]
  refine ⟨33646849779893068270331869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44862466373190757693775825 33646849779893068270331869)
  ·
    refine ⟨12617568667459900601374451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33646849779893068270331869 12617568667459900601374451)
    ·
      refine ⟨18926353001189850902061677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12617568667459900601374451 18926353001189850902061677)
      ·
        refine ⟨7097382375446194088273129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18926353001189850902061677 7097382375446194088273129)
        ·
          refine ⟨5323036781584645566204847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7097382375446194088273129 5323036781584645566204847)
          ·
            refine ⟨7984555172376968349307271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323036781584645566204847 7984555172376968349307271)
            ·
              refine ⟨11976832758565452523960907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984555172376968349307271 11976832758565452523960907)
              ·
                refine ⟨17965249137848178785941361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976832758565452523960907 17965249137848178785941361)
                ·
                  refine ⟨13473936853386134089456021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17965249137848178785941361 13473936853386134089456021)
                  ·
                    refine ⟨631590790002475035443251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13473936853386134089456021 631590790002475035443251)
                    ·
                      rfl

theorem cell22_1845028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1845028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845028 prefixEnd_1845028 := by exact prefixLift 1845028
  have htrace : WordTrace (prefixWord ++ tailWord_1845028) baseStart_1845028 baseEnd_1845028 := by
    simpa [prefixWord, tailWord_1845028, baseEnd_1845028] using wordTrace_append hprefix tailTrace_1845028
  have hstable : (prefixWord ++ tailWord_1845028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845028).length < 2 ^ (prefixWord ++ tailWord_1845028).sum := by decide
  have hdescent : baseEnd_1845028 < baseStart_1845028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845088 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 6]
def baseStart_1845088 : Nat := 118140960795 + 1845088 * 2 ^ 59
def prefixEnd_1845088 : Nat := 4983230072969 + 3 ^ 40 * 1845088 * 2
def baseEnd_1845088 : Nat := 210537109742884959647689

theorem tailTrace_1845088 : CollatzResearch.WordTrace tailWord_1845088 prefixEnd_1845088 210537109742884959647689 := by
  unfold tailWord_1845088
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647943969784383393923959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44863925293045844525231945 33647943969784383393923959)
  ·
    refine ⟨50471915954676575090885939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33647943969784383393923959 50471915954676575090885939)
    ·
      refine ⟨75707873932014862636328909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50471915954676575090885939 75707873932014862636328909)
      ·
        refine ⟨28390452724505573488623341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75707873932014862636328909 28390452724505573488623341)
        ·
          refine ⟨10646419771689590058233753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28390452724505573488623341 10646419771689590058233753)
          ·
            refine ⟨7984814828767192543675315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10646419771689590058233753 7984814828767192543675315)
            ·
              refine ⟨11977222243150788815512973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984814828767192543675315 11977222243150788815512973)
              ·
                refine ⟨4491458341181545805817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11977222243150788815512973 4491458341181545805817365)
                ·
                  refine ⟨210537109742884959647689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4491458341181545805817365 210537109742884959647689)
                  ·
                    rfl

theorem cell22_1845088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_1845088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845088 prefixEnd_1845088 := by exact prefixLift 1845088
  have htrace : WordTrace (prefixWord ++ tailWord_1845088) baseStart_1845088 baseEnd_1845088 := by
    simpa [prefixWord, tailWord_1845088, baseEnd_1845088] using wordTrace_append hprefix tailTrace_1845088
  have hstable : (prefixWord ++ tailWord_1845088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845088).length < 2 ^ (prefixWord ++ tailWord_1845088).sum := by decide
  have hdescent : baseEnd_1845088 < baseStart_1845088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845154 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1845154 : Nat := 118140960795 + 1845154 * 2 ^ 59
def prefixEnd_1845154 : Nat := 4983230072969 + 3 ^ 40 * 1845154 * 2
def baseEnd_1845154 : Nat := 631633922377452706792865

theorem tailTrace_1845154 : CollatzResearch.WordTrace tailWord_1845154 prefixEnd_1845154 631633922377452706792865 := by
  unfold tailWord_1845154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824573789332415014937629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44865530104886440039833677 16824573789332415014937629)
  ·
    refine ⟨6309215170999655630601611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16824573789332415014937629 6309215170999655630601611)
    ·
      refine ⟨9463822756499483445902417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309215170999655630601611 9463822756499483445902417)
      ·
        refine ⟨7097867067374612584426813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9463822756499483445902417 7097867067374612584426813)
        ·
          refine ⟨2661700150265479719160055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7097867067374612584426813 2661700150265479719160055)
          ·
            refine ⟨3992550225398219578740083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661700150265479719160055 3992550225398219578740083)
            ·
              refine ⟨5988825338097329368110125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992550225398219578740083 5988825338097329368110125)
              ·
                refine ⟨2245809501786498513041297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988825338097329368110125 2245809501786498513041297)
                ·
                  refine ⟨1684357126339873884780973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245809501786498513041297 1684357126339873884780973)
                  ·
                    refine ⟨631633922377452706792865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684357126339873884780973 631633922377452706792865)
                    ·
                      rfl

theorem cell22_1845154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1845154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845154 prefixEnd_1845154 := by exact prefixLift 1845154
  have htrace : WordTrace (prefixWord ++ tailWord_1845154) baseStart_1845154 baseEnd_1845154 := by
    simpa [prefixWord, tailWord_1845154, baseEnd_1845154] using wordTrace_append hprefix tailTrace_1845154
  have hstable : (prefixWord ++ tailWord_1845154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845154).length < 2 ^ (prefixWord ++ tailWord_1845154).sum := by decide
  have hdescent : baseEnd_1845154 < baseStart_1845154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845178 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_1845178 : Nat := 118140960795 + 1845178 * 2 ^ 59
def prefixEnd_1845178 : Nat := 4983230072969 + 3 ^ 40 * 1845178 * 2
def baseEnd_1845178 : Nat := 210547379355974881397597

theorem tailTrace_1845178 : CollatzResearch.WordTrace tailWord_1845178 prefixEnd_1845178 210547379355974881397597 := by
  unfold tailWord_1845178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824792627310678039656047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44866113672828474772416125 16824792627310678039656047)
  ·
    refine ⟨25237188940966017059484071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824792627310678039656047 25237188940966017059484071)
    ·
      refine ⟨37855783411449025589226107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25237188940966017059484071 37855783411449025589226107)
      ·
        refine ⟨56783675117173538383839161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37855783411449025589226107 56783675117173538383839161)
        ·
          refine ⟨42587756337880153787879371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56783675117173538383839161 42587756337880153787879371)
          ·
            refine ⟨63881634506820230681819057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42587756337880153787879371 63881634506820230681819057)
            ·
              refine ⟨47911225880115173011364293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63881634506820230681819057 47911225880115173011364293)
              ·
                refine ⟨8983354852521594939630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47911225880115173011364293 8983354852521594939630805)
                ·
                  refine ⟨210547379355974881397597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8983354852521594939630805 210547379355974881397597)
                  ·
                    rfl

theorem cell22_1845178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_1845178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845178 prefixEnd_1845178 := by exact prefixLift 1845178
  have htrace : WordTrace (prefixWord ++ tailWord_1845178) baseStart_1845178 baseEnd_1845178 := by
    simpa [prefixWord, tailWord_1845178, baseEnd_1845178] using wordTrace_append hprefix tailTrace_1845178
  have hstable : (prefixWord ++ tailWord_1845178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845178).length < 2 ^ (prefixWord ++ tailWord_1845178).sum := by decide
  have hdescent : baseEnd_1845178 < baseStart_1845178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845193 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_1845193 : Nat := 118140960795 + 1845193 * 2 ^ 59
def prefixEnd_1845193 : Nat := 4983230072969 + 3 ^ 40 * 1845193 * 2
def baseEnd_1845193 : Nat := 631647272874469605067745

theorem tailTrace_1845193 : CollatzResearch.WordTrace tailWord_1845193 prefixEnd_1845193 631647272874469605067745 := by
  unfold tailWord_1845193
  simp only [CollatzResearch.WordTrace]
  refine ⟨67299717604188369720420233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44866478402792246480280155 67299717604188369720420233)
  ·
    refine ⟨50474788203141277290315175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67299717604188369720420233 50474788203141277290315175)
    ·
      refine ⟨75712182304711915935472763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474788203141277290315175 75712182304711915935472763)
      ·
        refine ⟨113568273457067873903209145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75712182304711915935472763 113568273457067873903209145)
        ·
          refine ⟨85176205092800905427406859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113568273457067873903209145 85176205092800905427406859)
          ·
            refine ⟨127764307639201358141110289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85176205092800905427406859 127764307639201358141110289)
            ·
              refine ⟨95823230729401018605832717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127764307639201358141110289 95823230729401018605832717)
              ·
                refine ⟨35933711523525381977187269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95823230729401018605832717 35933711523525381977187269)
                ·
                  refine ⟨6737570910661009120722613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35933711523525381977187269 6737570910661009120722613)
                  ·
                    refine ⟨631647272874469605067745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6737570910661009120722613 631647272874469605067745)
                    ·
                      rfl

theorem cell22_1845193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_1845193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845193 prefixEnd_1845193 := by exact prefixLift 1845193
  have htrace : WordTrace (prefixWord ++ tailWord_1845193) baseStart_1845193 baseEnd_1845193 := by
    simpa [prefixWord, tailWord_1845193, baseEnd_1845193] using wordTrace_append hprefix tailTrace_1845193
  have hstable : (prefixWord ++ tailWord_1845193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845193).length < 2 ^ (prefixWord ++ tailWord_1845193).sum := by decide
  have hdescent : baseEnd_1845193 < baseStart_1845193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845195 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 5]
def baseStart_1845195 : Nat := 118140960795 + 1845195 * 2 ^ 59
def prefixEnd_1845195 : Nat := 4983230072969 + 3 ^ 40 * 1845195 * 2
def baseEnd_1845195 : Nat := 210549319171780755505913

theorem tailTrace_1845195 : CollatzResearch.WordTrace tailWord_1845195 prefixEnd_1845195 210549319171780755505913 := by
  unfold tailWord_1845195
  simp only [CollatzResearch.WordTrace]
  refine ⟨67299790550181124061993039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44866527033454082707995359 67299790550181124061993039)
  ·
    refine ⟨100949685825271686092989559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67299790550181124061993039 100949685825271686092989559)
    ·
      refine ⟨151424528737907529139484339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100949685825271686092989559 151424528737907529139484339)
      ·
        refine ⟨227136793106861293709226509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151424528737907529139484339 227136793106861293709226509)
        ·
          refine ⟨85176297415072985140959941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227136793106861293709226509 85176297415072985140959941)
          ·
            refine ⟨15970555765326184713929989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85176297415072985140959941 15970555765326184713929989)
            ·
              refine ⟨2994479205998659633861873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15970555765326184713929989 2994479205998659633861873)
              ·
                refine ⟨2245859404498994725396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994479205998659633861873 2245859404498994725396405)
                ·
                  refine ⟨210549319171780755505913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245859404498994725396405 210549319171780755505913)
                  ·
                    rfl

theorem cell22_1845195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 5].length) (baseStart_1845195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1845195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1845195 prefixEnd_1845195 := by exact prefixLift 1845195
  have htrace : WordTrace (prefixWord ++ tailWord_1845195) baseStart_1845195 baseEnd_1845195 := by
    simpa [prefixWord, tailWord_1845195, baseEnd_1845195] using wordTrace_append hprefix tailTrace_1845195
  have hstable : (prefixWord ++ tailWord_1845195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845195).length < 2 ^ (prefixWord ++ tailWord_1845195).sum := by decide
  have hdescent : baseEnd_1845195 < baseStart_1845195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
