import V185TrunkScan22Chunk442

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3949932 : List Nat := [2, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_3949932 : Nat := 118140960795 + 3949932 * 2 ^ 59
def prefixEnd_3949932 : Nat := 4983230072969 + 3 ^ 40 * 3949932 * 2
def baseEnd_3949932 : Nat := 450714148572254468129911

theorem tailTrace_3949932 : CollatzResearch.WordTrace tailWord_3949932 prefixEnd_3949932 450714148572254468129911 := by
  unfold tailWord_3949932
  simp only [CollatzResearch.WordTrace]
  refine ⟨72032927763039216761742025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96043903684052289015656033 72032927763039216761742025)
  ·
    refine ⟨54024695822279412571306519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72032927763039216761742025 54024695822279412571306519)
    ·
      refine ⟨81037043733419118856959779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54024695822279412571306519 81037043733419118856959779)
      ·
        refine ⟨121555565600128678285439669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81037043733419118856959779 121555565600128678285439669)
        ·
          refine ⟨11395834275012063589259969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121555565600128678285439669 11395834275012063589259969)
          ·
            refine ⟨8546875706259047691944977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11395834275012063589259969 8546875706259047691944977)
            ·
              refine ⟨6410156779694285768958733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8546875706259047691944977 6410156779694285768958733)
              ·
                refine ⟨2403808792385357163359525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6410156779694285768958733 2403808792385357163359525)
                ·
                  refine ⟨450714148572254468129911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403808792385357163359525 450714148572254468129911)
                  ·
                    rfl

theorem cell22_3949932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_3949932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949932 prefixEnd_3949932 := by exact prefixLift 3949932
  have htrace : WordTrace (prefixWord ++ tailWord_3949932) baseStart_3949932 baseEnd_3949932 := by
    simpa [prefixWord, tailWord_3949932, baseEnd_3949932] using wordTrace_append hprefix tailTrace_3949932
  have hstable : (prefixWord ++ tailWord_3949932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949932).length < 2 ^ (prefixWord ++ tailWord_3949932).sum := by decide
  have hdescent : baseEnd_3949932 < baseStart_3949932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949934 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_3949934 : Nat := 118140960795 + 3949934 * 2 ^ 59
def prefixEnd_3949934 : Nat := 4983230072969 + 3 ^ 40 * 3949934 * 2
def baseEnd_3949934 : Nat := 1352143130357636065839727

theorem tailTrace_3949934 : CollatzResearch.WordTrace tailWord_3949934 prefixEnd_3949934 1352143130357636065839727 := by
  unfold tailWord_3949934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008241059008898483132107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96043952314714125243371237 18008241059008898483132107)
  ·
    refine ⟨27012361588513347724698161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008241059008898483132107 27012361588513347724698161)
    ·
      refine ⟨20259271191385010793523621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27012361588513347724698161 20259271191385010793523621)
      ·
        refine ⟨3798613348384689523785679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20259271191385010793523621 3798613348384689523785679)
        ·
          refine ⟨5697920022577034285678519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798613348384689523785679 5697920022577034285678519)
          ·
            refine ⟨8546880033865551428517779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697920022577034285678519 8546880033865551428517779)
            ·
              refine ⟨12820320050798327142776669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546880033865551428517779 12820320050798327142776669)
              ·
                refine ⟨4807620019049372678541251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12820320050798327142776669 4807620019049372678541251)
                ·
                  refine ⟨7211430028574059017811877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807620019049372678541251 7211430028574059017811877)
                  ·
                    refine ⟨1352143130357636065839727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7211430028574059017811877 1352143130357636065839727)
                    ·
                      rfl

theorem cell22_3949934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_3949934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949934 prefixEnd_3949934 := by exact prefixLift 3949934
  have htrace : WordTrace (prefixWord ++ tailWord_3949934) baseStart_3949934 baseEnd_3949934 := by
    simpa [prefixWord, tailWord_3949934, baseEnd_3949934] using wordTrace_append hprefix tailTrace_3949934
  have hstable : (prefixWord ++ tailWord_3949934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949934).length < 2 ^ (prefixWord ++ tailWord_3949934).sum := by decide
  have hdescent : baseEnd_3949934 < baseStart_3949934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3949973 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3949973 : Nat := 118140960795 + 3949973 * 2 ^ 59
def prefixEnd_3949973 : Nat := 4983230072969 + 3 ^ 40 * 3949973 * 2
def baseEnd_3949973 : Nat := 1352156480854652964114607

theorem tailTrace_3949973 : CollatzResearch.WordTrace tailWord_3949973 prefixEnd_3949973 1352156480854652964114607 := by
  unfold tailWord_3949973
  simp only [CollatzResearch.WordTrace]
  refine ⟨144067350918929897525726573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96044900612619931683817715 144067350918929897525726573)
  ·
    refine ⟨54025256594598711572147465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144067350918929897525726573 54025256594598711572147465)
    ·
      refine ⟨40518942445949033679110599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54025256594598711572147465 40518942445949033679110599)
      ·
        refine ⟨60778413668923550518665899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40518942445949033679110599 60778413668923550518665899)
        ·
          refine ⟨91167620503385325777998849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60778413668923550518665899 91167620503385325777998849)
          ·
            refine ⟨68375715377538994333499137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91167620503385325777998849 68375715377538994333499137)
            ·
              refine ⟨51281786533154245750124353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68375715377538994333499137 51281786533154245750124353)
              ·
                refine ⟨38461339899865684312593265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51281786533154245750124353 38461339899865684312593265)
                ·
                  refine ⟨28846004924899263234444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38461339899865684312593265 28846004924899263234444949)
                  ·
                    refine ⟨1352156480854652964114607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28846004924899263234444949 1352156480854652964114607)
                    ·
                      rfl

theorem cell22_3949973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3949973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3949973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3949973 prefixEnd_3949973 := by exact prefixLift 3949973
  have htrace : WordTrace (prefixWord ++ tailWord_3949973) baseStart_3949973 baseEnd_3949973 := by
    simpa [prefixWord, tailWord_3949973, baseEnd_3949973] using wordTrace_append hprefix tailTrace_3949973
  have hstable : (prefixWord ++ tailWord_3949973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3949973).length < 2 ^ (prefixWord ++ tailWord_3949973).sum := by decide
  have hdescent : baseEnd_3949973 < baseStart_3949973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3949973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950003 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_3950003 : Nat := 118140960795 + 3950003 * 2 ^ 59
def prefixEnd_3950003 : Nat := 4983230072969 + 3 ^ 40 * 3950003 * 2
def baseEnd_3950003 : Nat := 1352166750467742885864515

theorem tailTrace_3950003 : CollatzResearch.WordTrace tailWord_3950003 prefixEnd_3950003 1352166750467742885864515 := by
  unfold tailWord_3950003
  simp only [CollatzResearch.WordTrace]
  refine ⟨144068445108821212649318663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96045630072547475099545775 144068445108821212649318663)
  ·
    refine ⟨216102667663231818973977995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144068445108821212649318663 216102667663231818973977995)
    ·
      refine ⟨324154001494847728460966993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216102667663231818973977995 324154001494847728460966993)
      ·
        refine ⟨243115501121135796345725245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324154001494847728460966993 243115501121135796345725245)
        ·
          refine ⟨91168312920425923629646967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243115501121135796345725245 91168312920425923629646967)
          ·
            refine ⟨136752469380638885444470451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91168312920425923629646967 136752469380638885444470451)
            ·
              refine ⟨205128704070958328166705677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136752469380638885444470451 205128704070958328166705677)
              ·
                refine ⟨76923264026609373062514629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205128704070958328166705677 76923264026609373062514629)
                ·
                  refine ⟨14423112004989257449221493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76923264026609373062514629 14423112004989257449221493)
                  ·
                    refine ⟨1352166750467742885864515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14423112004989257449221493 1352166750467742885864515)
                    ·
                      rfl

theorem cell22_3950003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_3950003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950003 prefixEnd_3950003 := by exact prefixLift 3950003
  have htrace : WordTrace (prefixWord ++ tailWord_3950003) baseStart_3950003 baseEnd_3950003 := by
    simpa [prefixWord, tailWord_3950003, baseEnd_3950003] using wordTrace_append hprefix tailTrace_3950003
  have hstable : (prefixWord ++ tailWord_3950003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950003).length < 2 ^ (prefixWord ++ tailWord_3950003).sum := by decide
  have hdescent : baseEnd_3950003 < baseStart_3950003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950005 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 7]
def baseStart_3950005 : Nat := 118140960795 + 3950005 * 2 ^ 59
def prefixEnd_3950005 : Nat := 4983230072969 + 3 ^ 40 * 3950005 * 2
def baseEnd_3950005 : Nat := 450722478369538515771503

theorem tailTrace_3950005 : CollatzResearch.WordTrace tailWord_3950005 prefixEnd_3950005 450722478369538515771503 := by
  unfold tailWord_3950005
  simp only [CollatzResearch.WordTrace]
  refine ⟨144068518054813966990891469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96045678703209311327260979 144068518054813966990891469)
  ·
    refine ⟨54025694270555237621584301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144068518054813966990891469 54025694270555237621584301)
    ·
      refine ⟨20259635351458214108094113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54025694270555237621584301 20259635351458214108094113)
      ·
        refine ⟨15194726513593660581070585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20259635351458214108094113 15194726513593660581070585)
        ·
          refine ⟨11396044885195245435802939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15194726513593660581070585 11396044885195245435802939)
          ·
            refine ⟨17094067327792868153704409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396044885195245435802939 17094067327792868153704409)
            ·
              refine ⟨12820550495844651115278307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17094067327792868153704409 12820550495844651115278307)
              ·
                refine ⟨19230825743766976672917461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12820550495844651115278307 19230825743766976672917461)
                ·
                  refine ⟨450722478369538515771503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19230825743766976672917461 450722478369538515771503)
                  ·
                    rfl

theorem cell22_3950005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_3950005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950005 prefixEnd_3950005 := by exact prefixLift 3950005
  have htrace : WordTrace (prefixWord ++ tailWord_3950005) baseStart_3950005 baseEnd_3950005 := by
    simpa [prefixWord, tailWord_3950005, baseEnd_3950005] using wordTrace_append hprefix tailTrace_3950005
  have hstable : (prefixWord ++ tailWord_3950005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950005).length < 2 ^ (prefixWord ++ tailWord_3950005).sum := by decide
  have hdescent : baseEnd_3950005 < baseStart_3950005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950009 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_3950009 : Nat := 118140960795 + 3950009 * 2 ^ 59
def prefixEnd_3950009 : Nat := 4983230072969 + 3 ^ 40 * 3950009 * 2
def baseEnd_3950009 : Nat := 1352168804390360870214497

theorem tailTrace_3950009 : CollatzResearch.WordTrace tailWord_3950009 prefixEnd_3950009 1352168804390360870214497 := by
  unfold tailWord_3950009
  simp only [CollatzResearch.WordTrace]
  refine ⟨144068663946799475674037081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96045775964532983782691387 144068663946799475674037081)
  ·
    refine ⟨108051497960099606755527811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144068663946799475674037081 108051497960099606755527811)
    ·
      refine ⟨162077246940149410133291717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108051497960099606755527811 162077246940149410133291717)
      ·
        refine ⟨30389483801278014399992197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162077246940149410133291717 30389483801278014399992197)
        ·
          refine ⟨5698028212739627699998537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30389483801278014399992197 5698028212739627699998537)
          ·
            refine ⟨4273521159554720774998903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5698028212739627699998537 4273521159554720774998903)
            ·
              refine ⟨6410281739332081162498355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273521159554720774998903 6410281739332081162498355)
              ·
                refine ⟨9615422608998121743747533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410281739332081162498355 9615422608998121743747533)
                ·
                  refine ⟨3605783478374295653905325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9615422608998121743747533 3605783478374295653905325)
                  ·
                    refine ⟨1352168804390360870214497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605783478374295653905325 1352168804390360870214497)
                    ·
                      rfl

theorem cell22_3950009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_3950009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950009 prefixEnd_3950009 := by exact prefixLift 3950009
  have htrace : WordTrace (prefixWord ++ tailWord_3950009) baseStart_3950009 baseEnd_3950009 := by
    simpa [prefixWord, tailWord_3950009, baseEnd_3950009] using wordTrace_append hprefix tailTrace_3950009
  have hstable : (prefixWord ++ tailWord_3950009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950009).length < 2 ^ (prefixWord ++ tailWord_3950009).sum := by decide
  have hdescent : baseEnd_3950009 < baseStart_3950009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950217 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_3950217 : Nat := 118140960795 + 3950217 * 2 ^ 59
def prefixEnd_3950217 : Nat := 4983230072969 + 3 ^ 40 * 3950217 * 2
def baseEnd_3950217 : Nat := 1352240007041117661013859

theorem tailTrace_3950217 : CollatzResearch.WordTrace tailWord_3950217 prefixEnd_3950217 1352240007041117661013859 := by
  unfold tailWord_3950217
  simp only [CollatzResearch.WordTrace]
  refine ⟨144076250330045927197608905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96050833553363951465072603 144076250330045927197608905)
  ·
    refine ⟨108057187747534445398206679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144076250330045927197608905 108057187747534445398206679)
    ·
      refine ⟨162085781621301668097310019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108057187747534445398206679 162085781621301668097310019)
      ·
        refine ⟨243128672431952502145965029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162085781621301668097310019 243128672431952502145965029)
        ·
          refine ⟨45586626080991094152368443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243128672431952502145965029 45586626080991094152368443)
          ·
            refine ⟨68379939121486641228552665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45586626080991094152368443 68379939121486641228552665)
            ·
              refine ⟨51284954341114980921414499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68379939121486641228552665 51284954341114980921414499)
              ·
                refine ⟨76927431511672471382121749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51284954341114980921414499 76927431511672471382121749)
                ·
                  refine ⟨3605973352109647096036957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76927431511672471382121749 3605973352109647096036957)
                  ·
                    refine ⟨1352240007041117661013859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3605973352109647096036957 1352240007041117661013859)
                    ·
                      rfl

theorem cell22_3950217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_3950217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950217 prefixEnd_3950217 := by exact prefixLift 3950217
  have htrace : WordTrace (prefixWord ++ tailWord_3950217) baseStart_3950217 baseEnd_3950217 := by
    simpa [prefixWord, tailWord_3950217, baseEnd_3950217] using wordTrace_append hprefix tailTrace_3950217
  have hstable : (prefixWord ++ tailWord_3950217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950217).length < 2 ^ (prefixWord ++ tailWord_3950217).sum := by decide
  have hdescent : baseEnd_3950217 < baseStart_3950217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950236 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_3950236 : Nat := 118140960795 + 3950236 * 2 ^ 59
def prefixEnd_3950236 : Nat := 4983230072969 + 3 ^ 40 * 3950236 * 2
def baseEnd_3950236 : Nat := 450748837043135981596267

theorem tailTrace_3950236 : CollatzResearch.WordTrace tailWord_3950236 prefixEnd_3950236 450748837043135981596267 := by
  unfold tailWord_3950236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72038471658488546721275281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96051295544651395628367041 72038471658488546721275281)
  ·
    refine ⟨54028853743866410040956461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72038471658488546721275281 54028853743866410040956461)
    ·
      refine ⟨20260820153949903765358673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54028853743866410040956461 20260820153949903765358673)
      ·
        refine ⟨15195615115462427824019005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20260820153949903765358673 15195615115462427824019005)
        ·
          refine ⟨5698355668298410434007127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15195615115462427824019005 5698355668298410434007127)
          ·
            refine ⟨8547533502447615651010691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698355668298410434007127 8547533502447615651010691)
            ·
              refine ⟨12821300253671423476516037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547533502447615651010691 12821300253671423476516037)
              ·
                refine ⟨2403993797563391901846757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12821300253671423476516037 2403993797563391901846757)
                ·
                  refine ⟨450748837043135981596267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403993797563391901846757 450748837043135981596267)
                  ·
                    rfl

theorem cell22_3950236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_3950236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950236 prefixEnd_3950236 := by exact prefixLift 3950236
  have htrace : WordTrace (prefixWord ++ tailWord_3950236) baseStart_3950236 baseEnd_3950236 := by
    simpa [prefixWord, tailWord_3950236, baseEnd_3950236] using wordTrace_append hprefix tailTrace_3950236
  have hstable : (prefixWord ++ tailWord_3950236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950236).length < 2 ^ (prefixWord ++ tailWord_3950236).sum := by decide
  have hdescent : baseEnd_3950236 < baseStart_3950236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950285 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3950285 : Nat := 118140960795 + 3950285 * 2 ^ 59
def prefixEnd_3950285 : Nat := 4983230072969 + 3 ^ 40 * 3950285 * 2
def baseEnd_3950285 : Nat := 1352263284830788150313651

theorem tailTrace_3950285 : CollatzResearch.WordTrace tailWord_3950285 prefixEnd_3950285 1352263284830788150313651 := by
  unfold tailWord_3950285
  simp only [CollatzResearch.WordTrace]
  refine ⟨144078730493799574811084309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96052486995866383207389539 144078730493799574811084309)
  ·
    refine ⟨6753690491896855069269577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144078730493799574811084309 6753690491896855069269577)
    ·
      refine ⟨5065267868922641301952183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6753690491896855069269577 5065267868922641301952183)
      ·
        refine ⟨7597901803383961952928275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065267868922641301952183 7597901803383961952928275)
        ·
          refine ⟨11396852705075942929392413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597901803383961952928275 11396852705075942929392413)
          ·
            refine ⟨4273819764403478598522155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11396852705075942929392413 4273819764403478598522155)
            ·
              refine ⟨6410729646605217897783233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273819764403478598522155 6410729646605217897783233)
              ·
                refine ⟨4808047234953913423337425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6410729646605217897783233 4808047234953913423337425)
                ·
                  refine ⟨3606035426215435067503069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808047234953913423337425 3606035426215435067503069)
                  ·
                    refine ⟨1352263284830788150313651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606035426215435067503069 1352263284830788150313651)
                    ·
                      rfl

theorem cell22_3950285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3950285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950285 prefixEnd_3950285 := by exact prefixLift 3950285
  have htrace : WordTrace (prefixWord ++ tailWord_3950285) baseStart_3950285 baseEnd_3950285 := by
    simpa [prefixWord, tailWord_3950285, baseEnd_3950285] using wordTrace_append hprefix tailTrace_3950285
  have hstable : (prefixWord ++ tailWord_3950285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950285).length < 2 ^ (prefixWord ++ tailWord_3950285).sum := by decide
  have hdescent : baseEnd_3950285 < baseStart_3950285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950296 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_3950296 : Nat := 118140960795 + 3950296 * 2 ^ 59
def prefixEnd_3950296 : Nat := 4983230072969 + 3 ^ 40 * 3950296 * 2
def baseEnd_3950296 : Nat := 1352267050355587788288617

theorem tailTrace_3950296 : CollatzResearch.WordTrace tailWord_3950296 prefixEnd_3950296 1352267050355587788288617 := by
  unfold tailWord_3950296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72039565848379861844867371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96052754464506482459823161 72039565848379861844867371)
  ·
    refine ⟨108059348772569792767301057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72039565848379861844867371 108059348772569792767301057)
    ·
      refine ⟨81044511579427344575475793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108059348772569792767301057 81044511579427344575475793)
      ·
        refine ⟨60783383684570508431606845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81044511579427344575475793 60783383684570508431606845)
        ·
          refine ⟨22793768881713940661852567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60783383684570508431606845 22793768881713940661852567)
          ·
            refine ⟨34190653322570910992778851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22793768881713940661852567 34190653322570910992778851)
            ·
              refine ⟨51285979983856366489168277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34190653322570910992778851 51285979983856366489168277)
              ·
                refine ⟨2404030311743267179179763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51285979983856366489168277 2404030311743267179179763)
                ·
                  refine ⟨3606045467614900768769645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404030311743267179179763 3606045467614900768769645)
                  ·
                    refine ⟨1352267050355587788288617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606045467614900768769645 1352267050355587788288617)
                    ·
                      rfl

theorem cell22_3950296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_3950296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950296 prefixEnd_3950296 := by exact prefixLift 3950296
  have htrace : WordTrace (prefixWord ++ tailWord_3950296) baseStart_3950296 baseEnd_3950296 := by
    simpa [prefixWord, tailWord_3950296, baseEnd_3950296] using wordTrace_append hprefix tailTrace_3950296
  have hstable : (prefixWord ++ tailWord_3950296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950296).length < 2 ^ (prefixWord ++ tailWord_3950296).sum := by decide
  have hdescent : baseEnd_3950296 < baseStart_3950296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950337 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 8]
def baseStart_3950337 : Nat := 118140960795 + 3950337 * 2 ^ 59
def prefixEnd_3950337 : Nat := 4983230072969 + 3 ^ 40 * 3950337 * 2
def baseEnd_3950337 : Nat := 450760361831159116004497

theorem tailTrace_3950337 : CollatzResearch.WordTrace tailWord_3950337 prefixEnd_3950337 450760361831159116004497 := by
  unfold tailWord_3950337
  simp only [CollatzResearch.WordTrace]
  refine ⟨144080627089611187691977265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96053751393074125127984843 144080627089611187691977265)
  ·
    refine ⟨108060470317208390768982949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144080627089611187691977265 108060470317208390768982949)
    ·
      refine ⟨20261338184476573269184303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108060470317208390768982949 20261338184476573269184303)
      ·
        refine ⟨30392007276714859903776455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20261338184476573269184303 30392007276714859903776455)
        ·
          refine ⟨45588010915072289855664683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30392007276714859903776455 45588010915072289855664683)
          ·
            refine ⟨68382016372608434783497025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45588010915072289855664683 68382016372608434783497025)
            ·
              refine ⟨51286512279456326087622769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68382016372608434783497025 51286512279456326087622769)
              ·
                refine ⟨38464884209592244565717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51286512279456326087622769 38464884209592244565717077)
                ·
                  refine ⟨450760361831159116004497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38464884209592244565717077 450760361831159116004497)
                  ·
                    rfl

theorem cell22_3950337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_3950337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950337 prefixEnd_3950337 := by exact prefixLift 3950337
  have htrace : WordTrace (prefixWord ++ tailWord_3950337) baseStart_3950337 baseEnd_3950337 := by
    simpa [prefixWord, tailWord_3950337, baseEnd_3950337] using wordTrace_append hprefix tailTrace_3950337
  have hstable : (prefixWord ++ tailWord_3950337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950337).length < 2 ^ (prefixWord ++ tailWord_3950337).sum := by decide
  have hdescent : baseEnd_3950337 < baseStart_3950337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950339 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 1, 4]
def baseStart_3950339 : Nat := 118140960795 + 3950339 * 2 ^ 59
def prefixEnd_3950339 : Nat := 4983230072969 + 3 ^ 40 * 3950339 * 2
def baseEnd_3950339 : Nat := 1352281770134350009463485

theorem tailTrace_3950339 : CollatzResearch.WordTrace tailWord_3950339 prefixEnd_3950339 1352281770134350009463485 := by
  unfold tailWord_3950339
  simp only [CollatzResearch.WordTrace]
  refine ⟨144080700035603942033550071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96053800023735961355700047 144080700035603942033550071)
  ·
    refine ⟨216121050053405913050325107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144080700035603942033550071 216121050053405913050325107)
    ·
      refine ⟨324181575080108869575487661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216121050053405913050325107 324181575080108869575487661)
      ·
        refine ⟨121568090655040826090807873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324181575080108869575487661 121568090655040826090807873)
        ·
          refine ⟨91176067991280619568105905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121568090655040826090807873 91176067991280619568105905)
          ·
            refine ⟨68382050993460464676079429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91176067991280619568105905 68382050993460464676079429)
            ·
              refine ⟨12821634561273837126764893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68382050993460464676079429 12821634561273837126764893)
              ·
                refine ⟨4808112960477688922536835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12821634561273837126764893 4808112960477688922536835)
                ·
                  refine ⟨7212169440716533383805253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808112960477688922536835 7212169440716533383805253)
                  ·
                    refine ⟨1352281770134350009463485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212169440716533383805253 1352281770134350009463485)
                    ·
                      rfl

theorem cell22_3950339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 4].length) (baseStart_3950339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950339 prefixEnd_3950339 := by exact prefixLift 3950339
  have htrace : WordTrace (prefixWord ++ tailWord_3950339) baseStart_3950339 baseEnd_3950339 := by
    simpa [prefixWord, tailWord_3950339, baseEnd_3950339] using wordTrace_append hprefix tailTrace_3950339
  have hstable : (prefixWord ++ tailWord_3950339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950339).length < 2 ^ (prefixWord ++ tailWord_3950339).sum := by decide
  have hdescent : baseEnd_3950339 < baseStart_3950339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950390 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_3950390 : Nat := 118140960795 + 3950390 * 2 ^ 59
def prefixEnd_3950390 : Nat := 4983230072969 + 3 ^ 40 * 3950390 * 2
def baseEnd_3950390 : Nat := 1352299228476602876438329

theorem tailTrace_3950390 : CollatzResearch.WordTrace tailWord_3950390 prefixEnd_3950390 1352299228476602876438329 := by
  unfold tailWord_3950390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005160009901198608978539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96055040105612785162437749 9005160009901198608978539)
  ·
    refine ⟨13507740014851797913467809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005160009901198608978539 13507740014851797913467809)
    ·
      refine ⟨10130805011138848435100857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13507740014851797913467809 10130805011138848435100857)
      ·
        refine ⟨7598103758354136326325643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10130805011138848435100857 7598103758354136326325643)
        ·
          refine ⟨11397155637531204489488465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598103758354136326325643 11397155637531204489488465)
          ·
            refine ⟨8547866728148403367116349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11397155637531204489488465 8547866728148403367116349)
            ·
              refine ⟨3205450023055651262668631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8547866728148403367116349 3205450023055651262668631)
              ·
                refine ⟨4808175034583476894002947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205450023055651262668631 4808175034583476894002947)
                ·
                  refine ⟨7212262551875215341004421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808175034583476894002947 7212262551875215341004421)
                  ·
                    refine ⟨1352299228476602876438329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212262551875215341004421 1352299228476602876438329)
                    ·
                      rfl

theorem cell22_3950390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_3950390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950390 prefixEnd_3950390 := by exact prefixLift 3950390
  have htrace : WordTrace (prefixWord ++ tailWord_3950390) baseStart_3950390 baseEnd_3950390 := by
    simpa [prefixWord, tailWord_3950390, baseEnd_3950390] using wordTrace_append hprefix tailTrace_3950390
  have hstable : (prefixWord ++ tailWord_3950390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950390).length < 2 ^ (prefixWord ++ tailWord_3950390).sum := by decide
  have hdescent : baseEnd_3950390 < baseStart_3950390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950399 : List Nat := [1, 1, 2, 2, 7, 9]
def baseStart_3950399 : Nat := 118140960795 + 3950399 * 2 ^ 59
def prefixEnd_3950399 : Nat := 4983230072969 + 3 ^ 40 * 3950399 * 2
def baseEnd_3950399 : Nat := 16695090239018887073621

theorem tailTrace_3950399 : CollatzResearch.WordTrace tailWord_3950399 prefixEnd_3950399 16695090239018887073621 := by
  unfold tailWord_3950399
  simp only [CollatzResearch.WordTrace]
  refine ⟨144082888415386572280734251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96055258943591048187156167 144082888415386572280734251)
  ·
    refine ⟨216124332623079858421101377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144082888415386572280734251 216124332623079858421101377)
    ·
      refine ⟨162093249467309893815826033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216124332623079858421101377 162093249467309893815826033)
      ·
        refine ⟨121569937100482420361869525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162093249467309893815826033 121569937100482420361869525)
        ·
          refine ⟨2849295400792556727231317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 121569937100482420361869525 2849295400792556727231317)
          ·
            refine ⟨16695090239018887073621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2849295400792556727231317 16695090239018887073621)
            ·
              rfl

theorem cell22_3950399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 9].length) (baseStart_3950399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950399 prefixEnd_3950399 := by exact prefixLift 3950399
  have htrace : WordTrace (prefixWord ++ tailWord_3950399) baseStart_3950399 baseEnd_3950399 := by
    simpa [prefixWord, tailWord_3950399, baseEnd_3950399] using wordTrace_append hprefix tailTrace_3950399
  have hstable : (prefixWord ++ tailWord_3950399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950399).length < 2 ^ (prefixWord ++ tailWord_3950399).sum := by decide
  have hdescent : baseEnd_3950399 < baseStart_3950399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950431 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 3, 3]
def baseStart_3950431 : Nat := 118140960795 + 3950431 * 2 ^ 59
def prefixEnd_3950431 : Nat := 4983230072969 + 3 ^ 40 * 3950431 * 2
def baseEnd_3950431 : Nat := 1352313263614492436163203

theorem tailTrace_3950431 : CollatzResearch.WordTrace tailWord_3950431 prefixEnd_3950431 1352313263614492436163203 := by
  unfold tailWord_3950431
  simp only [CollatzResearch.WordTrace]
  refine ⟨144084055551270641745899147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96056037034180427830599431 144084055551270641745899147)
  ·
    refine ⟨216126083326905962618848721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144084055551270641745899147 216126083326905962618848721)
    ·
      refine ⟨162094562495179471964136541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216126083326905962618848721 162094562495179471964136541)
      ·
        refine ⟨60785460935692301986551203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162094562495179471964136541 60785460935692301986551203)
        ·
          refine ⟨91178191403538452979826805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60785460935692301986551203 91178191403538452979826805)
          ·
            refine ⟨8547955444081729966858763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91178191403538452979826805 8547955444081729966858763)
            ·
              refine ⟨12821933166122594950288145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547955444081729966858763 12821933166122594950288145)
              ·
                refine ⟨9616449874591946212716109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12821933166122594950288145 9616449874591946212716109)
                ·
                  refine ⟨3606168702971979829768541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9616449874591946212716109 3606168702971979829768541)
                  ·
                    refine ⟨1352313263614492436163203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606168702971979829768541 1352313263614492436163203)
                    ·
                      rfl

theorem cell22_3950431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_3950431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950431 prefixEnd_3950431 := by exact prefixLift 3950431
  have htrace : WordTrace (prefixWord ++ tailWord_3950431) baseStart_3950431 baseEnd_3950431 := by
    simpa [prefixWord, tailWord_3950431, baseEnd_3950431] using wordTrace_append hprefix tailTrace_3950431
  have hstable : (prefixWord ++ tailWord_3950431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950431).length < 2 ^ (prefixWord ++ tailWord_3950431).sum := by decide
  have hdescent : baseEnd_3950431 < baseStart_3950431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950465 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3950465 : Nat := 118140960795 + 3950465 * 2 ^ 59
def prefixEnd_3950465 : Nat := 4983230072969 + 3 ^ 40 * 3950465 * 2
def baseEnd_3950465 : Nat := 1352324902509327680813099

theorem tailTrace_3950465 : CollatzResearch.WordTrace tailWord_3950465 prefixEnd_3950465 1352324902509327680813099 := by
  unfold tailWord_3950465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144085295633147465552636849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96056863755431643701757899 144085295633147465552636849)
  ·
    refine ⟨108063971724860599164477637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144085295633147465552636849 108063971724860599164477637)
    ·
      refine ⟨20261994698411362343339557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108063971724860599164477637 20261994698411362343339557)
      ·
        refine ⟨3799124005952130439376167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20261994698411362343339557 3799124005952130439376167)
        ·
          refine ⟨5698686008928195659064251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799124005952130439376167 5698686008928195659064251)
          ·
            refine ⟨8548029013392293488596377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698686008928195659064251 8548029013392293488596377)
            ·
              refine ⟨6411021760044220116447283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548029013392293488596377 6411021760044220116447283)
              ·
                refine ⟨9616532640066330174670925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411021760044220116447283 9616532640066330174670925)
                ·
                  refine ⟨3606199740024873815501597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9616532640066330174670925 3606199740024873815501597)
                  ·
                    refine ⟨1352324902509327680813099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606199740024873815501597 1352324902509327680813099)
                    ·
                      rfl

theorem cell22_3950465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3950465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950465 prefixEnd_3950465 := by exact prefixLift 3950465
  have htrace : WordTrace (prefixWord ++ tailWord_3950465) baseStart_3950465 baseEnd_3950465 := by
    simpa [prefixWord, tailWord_3950465, baseEnd_3950465] using wordTrace_append hprefix tailTrace_3950465
  have hstable : (prefixWord ++ tailWord_3950465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950465).length < 2 ^ (prefixWord ++ tailWord_3950465).sum := by decide
  have hdescent : baseEnd_3950465 < baseStart_3950465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950489 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 6]
def baseStart_3950489 : Nat := 118140960795 + 3950489 * 2 ^ 59
def prefixEnd_3950489 : Nat := 4983230072969 + 3 ^ 40 * 3950489 * 2
def baseEnd_3950489 : Nat := 450777706066599872737675

theorem tailTrace_3950489 : CollatzResearch.WordTrace tailWord_3950489 prefixEnd_3950489 450777706066599872737675 := by
  unfold tailWord_3950489
  simp only [CollatzResearch.WordTrace]
  refine ⟨144086170985060517651510521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96057447323373678434340347 144086170985060517651510521)
  ·
    refine ⟨108064628238795388238632891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144086170985060517651510521 108064628238795388238632891)
    ·
      refine ⟨162096942358193082357949337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108064628238795388238632891 162096942358193082357949337)
      ·
        refine ⟨121572706768644811768462003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162096942358193082357949337 121572706768644811768462003)
        ·
          refine ⟨182359060152967217652693005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121572706768644811768462003 182359060152967217652693005)
          ·
            refine ⟨68384647557362706619759877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182359060152967217652693005 68384647557362706619759877)
            ·
              refine ⟨12822121417005507491204977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68384647557362706619759877 12822121417005507491204977)
              ·
                refine ⟨9616591062754130618403733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12822121417005507491204977 9616591062754130618403733)
                ·
                  refine ⟨450777706066599872737675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9616591062754130618403733 450777706066599872737675)
                  ·
                    rfl

theorem cell22_3950489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_3950489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950489 prefixEnd_3950489 := by exact prefixLift 3950489
  have htrace : WordTrace (prefixWord ++ tailWord_3950489) baseStart_3950489 baseEnd_3950489 := by
    simpa [prefixWord, tailWord_3950489, baseEnd_3950489] using wordTrace_append hprefix tailTrace_3950489
  have hstable : (prefixWord ++ tailWord_3950489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950489).length < 2 ^ (prefixWord ++ tailWord_3950489).sum := by decide
  have hdescent : baseEnd_3950489 < baseStart_3950489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950521 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_3950521 : Nat := 118140960795 + 3950521 * 2 ^ 59
def prefixEnd_3950521 : Nat := 4983230072969 + 3 ^ 40 * 3950521 * 2
def baseEnd_3950521 : Nat := 1352344072453762201412927

theorem tailTrace_3950521 : CollatzResearch.WordTrace tailWord_3950521 prefixEnd_3950521 1352344072453762201412927 := by
  unfold tailWord_3950521
  simp only [CollatzResearch.WordTrace]
  refine ⟨144087338120944587116675417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96058225413963058077783611 144087338120944587116675417)
  ·
    refine ⟨108065503590708440337506563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144087338120944587116675417 108065503590708440337506563)
    ·
      refine ⟨162098255386062660506259845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108065503590708440337506563 162098255386062660506259845)
      ·
        refine ⟨30393422884886748844923721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162098255386062660506259845 30393422884886748844923721)
        ·
          refine ⟨22795067163665061633692791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30393422884886748844923721 22795067163665061633692791)
          ·
            refine ⟨34192600745497592450539187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22795067163665061633692791 34192600745497592450539187)
            ·
              refine ⟨51288901118246388675808781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34192600745497592450539187 51288901118246388675808781)
              ·
                refine ⟨19233337919342395753428293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51288901118246388675808781 19233337919342395753428293)
                ·
                  refine ⟨3606250859876699203767805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19233337919342395753428293 3606250859876699203767805)
                  ·
                    refine ⟨1352344072453762201412927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606250859876699203767805 1352344072453762201412927)
                    ·
                      rfl

theorem cell22_3950521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_3950521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950521 prefixEnd_3950521 := by exact prefixLift 3950521
  have htrace : WordTrace (prefixWord ++ tailWord_3950521) baseStart_3950521 baseEnd_3950521 := by
    simpa [prefixWord, tailWord_3950521, baseEnd_3950521] using wordTrace_append hprefix tailTrace_3950521
  have hstable : (prefixWord ++ tailWord_3950521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950521).length < 2 ^ (prefixWord ++ tailWord_3950521).sum := by decide
  have hdescent : baseEnd_3950521 < baseStart_3950521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950553 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_3950553 : Nat := 118140960795 + 3950553 * 2 ^ 59
def prefixEnd_3950553 : Nat := 4983230072969 + 3 ^ 40 * 3950553 * 2
def baseEnd_3950553 : Nat := 1352355026707724784612829

theorem tailTrace_3950553 : CollatzResearch.WordTrace tailWord_3950553 prefixEnd_3950553 1352355026707724784612829 := by
  unfold tailWord_3950553
  simp only [CollatzResearch.WordTrace]
  refine ⟨144088505256828656581840313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96059003504552437721226875 144088505256828656581840313)
  ·
    refine ⟨108066378942621492436380235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144088505256828656581840313 108066378942621492436380235)
    ·
      refine ⟨162099568413932238654570353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108066378942621492436380235 162099568413932238654570353)
      ·
        refine ⟨121574676310449178990927765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162099568413932238654570353 121574676310449178990927765)
        ·
          refine ⟨5698812952052305265199739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121574676310449178990927765 5698812952052305265199739)
          ·
            refine ⟨8548219428078457897799609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698812952052305265199739 8548219428078457897799609)
            ·
              refine ⟨6411164571058843423349707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8548219428078457897799609 6411164571058843423349707)
              ·
                refine ⟨9616746856588265135024561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6411164571058843423349707 9616746856588265135024561)
                ·
                  refine ⟨7212560142441198851268421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616746856588265135024561 7212560142441198851268421)
                  ·
                    refine ⟨1352355026707724784612829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212560142441198851268421 1352355026707724784612829)
                    ·
                      rfl

theorem cell22_3950553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_3950553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950553 prefixEnd_3950553 := by exact prefixLift 3950553
  have htrace : WordTrace (prefixWord ++ tailWord_3950553) baseStart_3950553 baseEnd_3950553 := by
    simpa [prefixWord, tailWord_3950553, baseEnd_3950553] using wordTrace_append hprefix tailTrace_3950553
  have hstable : (prefixWord ++ tailWord_3950553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950553).length < 2 ^ (prefixWord ++ tailWord_3950553).sum := by decide
  have hdescent : baseEnd_3950553 < baseStart_3950553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950579 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 7]
def baseStart_3950579 : Nat := 118140960795 + 3950579 * 2 ^ 59
def prefixEnd_3950579 : Nat := 4983230072969 + 3 ^ 40 * 3950579 * 2
def baseEnd_3950579 : Nat := 450787975679689794487583

theorem tailTrace_3950579 : CollatzResearch.WordTrace tailWord_3950579 prefixEnd_3950579 450787975679689794487583 := by
  unfold tailWord_3950579
  simp only [CollatzResearch.WordTrace]
  refine ⟨144089453554734463022286791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96059635703156308681524527 144089453554734463022286791)
  ·
    refine ⟨216134180332101694533430187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144089453554734463022286791 216134180332101694533430187)
    ·
      refine ⟨324201270498152541800145281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216134180332101694533430187 324201270498152541800145281)
      ·
        refine ⟨243150952873614406350108961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324201270498152541800145281 243150952873614406350108961)
        ·
          refine ⟨182363214655210804762581721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243150952873614406350108961 182363214655210804762581721)
          ·
            refine ⟨136772410991408103571936291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182363214655210804762581721 136772410991408103571936291)
            ·
              refine ⟨205158616487112155357904437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136772410991408103571936291 205158616487112155357904437)
              ·
                refine ⟨19233620295666764564803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205158616487112155357904437 19233620295666764564803541)
                ·
                  refine ⟨450787975679689794487583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19233620295666764564803541 450787975679689794487583)
                  ·
                    rfl

theorem cell22_3950579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_3950579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950579 prefixEnd_3950579 := by exact prefixLift 3950579
  have htrace : WordTrace (prefixWord ++ tailWord_3950579) baseStart_3950579 baseEnd_3950579 := by
    simpa [prefixWord, tailWord_3950579, baseEnd_3950579] using wordTrace_append hprefix tailTrace_3950579
  have hstable : (prefixWord ++ tailWord_3950579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950579).length < 2 ^ (prefixWord ++ tailWord_3950579).sum := by decide
  have hdescent : baseEnd_3950579 < baseStart_3950579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950641 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 6]
def baseStart_3950641 : Nat := 118140960795 + 3950641 * 2 ^ 59
def prefixEnd_3950641 : Nat := 4983230072969 + 3 ^ 40 * 3950641 * 2
def baseEnd_3950641 : Nat := 450795050302040629470853

theorem tailTrace_3950641 : CollatzResearch.WordTrace tailWord_3950641 prefixEnd_3950641 450795050302040629470853 := by
  unfold tailWord_3950641
  simp only [CollatzResearch.WordTrace]
  refine ⟨144091714880509847611043777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96061143253673231740695851 144091714880509847611043777)
  ·
    refine ⟨108068786160382385708282833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144091714880509847611043777 108068786160382385708282833)
    ·
      refine ⟨81051589620286789281212125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108068786160382385708282833 81051589620286789281212125)
      ·
        refine ⟨30394346107607545980454547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81051589620286789281212125 30394346107607545980454547)
        ·
          refine ⟨45591519161411318970681821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30394346107607545980454547 45591519161411318970681821)
          ·
            refine ⟨17096819685529244614005683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45591519161411318970681821 17096819685529244614005683)
            ·
              refine ⟨25645229528293866921008525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17096819685529244614005683 25645229528293866921008525)
              ·
                refine ⟨9616961073110200095378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25645229528293866921008525 9616961073110200095378197)
                ·
                  refine ⟨450795050302040629470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9616961073110200095378197 450795050302040629470853)
                  ·
                    rfl

theorem cell22_3950641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_3950641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950641 prefixEnd_3950641 := by exact prefixLift 3950641
  have htrace : WordTrace (prefixWord ++ tailWord_3950641) baseStart_3950641 baseEnd_3950641 := by
    simpa [prefixWord, tailWord_3950641, baseEnd_3950641] using wordTrace_append hprefix tailTrace_3950641
  have hstable : (prefixWord ++ tailWord_3950641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950641).length < 2 ^ (prefixWord ++ tailWord_3950641).sum := by decide
  have hdescent : baseEnd_3950641 < baseStart_3950641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950688 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_3950688 : Nat := 118140960795 + 3950688 * 2 ^ 59
def prefixEnd_3950688 : Nat := 4983230072969 + 3 ^ 40 * 3950688 * 2
def baseEnd_3950688 : Nat := 1352401239966629432487415

theorem tailTrace_3950688 : CollatzResearch.WordTrace tailWord_3950688 prefixEnd_3950688 1352401239966629432487415 := by
  unfold tailWord_3950688
  simp only [CollatzResearch.WordTrace]
  refine ⟨72046714555669787319002359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96062286074226383092003145 72046714555669787319002359)
  ·
    refine ⟨108070071833504680978503539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72046714555669787319002359 108070071833504680978503539)
    ·
      refine ⟨162105107750257021467755309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108070071833504680978503539 162105107750257021467755309)
      ·
        refine ⟨60789415406346383050408241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162105107750257021467755309 60789415406346383050408241)
        ·
          refine ⟨45592061554759787287806181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60789415406346383050408241 45592061554759787287806181)
          ·
            refine ⟨8548511541517460116463659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45592061554759787287806181 8548511541517460116463659)
            ·
              refine ⟨12822767312276190174695489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548511541517460116463659 12822767312276190174695489)
              ·
                refine ⟨9617075484207142631021617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12822767312276190174695489 9617075484207142631021617)
                ·
                  refine ⟨7212806613155356973266213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617075484207142631021617 7212806613155356973266213)
                  ·
                    refine ⟨1352401239966629432487415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212806613155356973266213 1352401239966629432487415)
                    ·
                      rfl

theorem cell22_3950688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_3950688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950688 prefixEnd_3950688 := by exact prefixLift 3950688
  have htrace : WordTrace (prefixWord ++ tailWord_3950688) baseStart_3950688 baseEnd_3950688 := by
    simpa [prefixWord, tailWord_3950688, baseEnd_3950688] using wordTrace_append hprefix tailTrace_3950688
  have hstable : (prefixWord ++ tailWord_3950688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950688).length < 2 ^ (prefixWord ++ tailWord_3950688).sum := by decide
  have hdescent : baseEnd_3950688 < baseStart_3950688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950752 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_3950752 : Nat := 118140960795 + 3950752 * 2 ^ 59
def prefixEnd_3950752 : Nat := 4983230072969 + 3 ^ 40 * 3950752 * 2
def baseEnd_3950752 : Nat := 1352423148474554598887219

theorem tailTrace_3950752 : CollatzResearch.WordTrace tailWord_3950752 prefixEnd_3950752 1352423148474554598887219 := by
  unfold tailWord_3950752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047881691553856784167255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96063842255405142378889673 72047881691553856784167255)
  ·
    refine ⟨108071822537330785176250883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72047881691553856784167255 108071822537330785176250883)
    ·
      refine ⟨162107733805996177764376325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108071822537330785176250883 162107733805996177764376325)
      ·
        refine ⟨30395200088624283330820561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162107733805996177764376325 30395200088624283330820561)
        ·
          refine ⟨22796400066468212498115421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30395200088624283330820561 22796400066468212498115421)
          ·
            refine ⟨8548650024925579686793283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22796400066468212498115421 8548650024925579686793283)
            ·
              refine ⟨12822975037388369530189925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548650024925579686793283 12822975037388369530189925)
              ·
                refine ⟨2404307819510319286910611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12822975037388369530189925 2404307819510319286910611)
                ·
                  refine ⟨3606461729265478930365917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404307819510319286910611 3606461729265478930365917)
                  ·
                    refine ⟨1352423148474554598887219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606461729265478930365917 1352423148474554598887219)
                    ·
                      rfl

theorem cell22_3950752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_3950752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950752 prefixEnd_3950752 := by exact prefixLift 3950752
  have htrace : WordTrace (prefixWord ++ tailWord_3950752) baseStart_3950752 baseEnd_3950752 := by
    simpa [prefixWord, tailWord_3950752, baseEnd_3950752] using wordTrace_append hprefix tailTrace_3950752
  have hstable : (prefixWord ++ tailWord_3950752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950752).length < 2 ^ (prefixWord ++ tailWord_3950752).sum := by decide
  have hdescent : baseEnd_3950752 < baseStart_3950752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950765 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3950765 : Nat := 118140960795 + 3950765 * 2 ^ 59
def prefixEnd_3950765 : Nat := 4983230072969 + 3 ^ 40 * 3950765 * 2
def baseEnd_3950765 : Nat := 450809199546742299437393

theorem tailTrace_3950765 : CollatzResearch.WordTrace tailWord_3950765 prefixEnd_3950765 450809199546742299437393 := by
  unfold tailWord_3950765
  simp only [CollatzResearch.WordTrace]
  refine ⟨144096237532060616788557749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96064158354707077859038499 144096237532060616788557749)
  ·
    refine ⟨13509022268630682823927289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144096237532060616788557749 13509022268630682823927289)
    ·
      refine ⟨10131766701473012117945467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13509022268630682823927289 10131766701473012117945467)
      ·
        refine ⟨15197650052209518176918201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131766701473012117945467 15197650052209518176918201)
        ·
          refine ⟨11398237539157138632688651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15197650052209518176918201 11398237539157138632688651)
          ·
            refine ⟨17097356308735707949032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398237539157138632688651 17097356308735707949032977)
            ·
              refine ⟨12823017231551780961774733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17097356308735707949032977 12823017231551780961774733)
              ·
                refine ⟨4808631461831917860665525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12823017231551780961774733 4808631461831917860665525)
                ·
                  refine ⟨450809199546742299437393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4808631461831917860665525 450809199546742299437393)
                  ·
                    rfl

theorem cell22_3950765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3950765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950765 prefixEnd_3950765 := by exact prefixLift 3950765
  have htrace : WordTrace (prefixWord ++ tailWord_3950765) baseStart_3950765 baseEnd_3950765 := by
    simpa [prefixWord, tailWord_3950765, baseEnd_3950765] using wordTrace_append hprefix tailTrace_3950765
  have hstable : (prefixWord ++ tailWord_3950765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950765).length < 2 ^ (prefixWord ++ tailWord_3950765).sum := by decide
  have hdescent : baseEnd_3950765 < baseStart_3950765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950778 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3950778 : Nat := 118140960795 + 3950778 * 2 ^ 59
def prefixEnd_3950778 : Nat := 4983230072969 + 3 ^ 40 * 3950778 * 2
def baseEnd_3950778 : Nat := 1352432048805899197737139

theorem tailTrace_3950778 : CollatzResearch.WordTrace tailWord_3950778 prefixEnd_3950778 1352432048805899197737139 := by
  unfold tailWord_3950778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024177920253380002195247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96064474454009013339187325 36024177920253380002195247)
  ·
    refine ⟨54036266880380070003292871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024177920253380002195247 54036266880380070003292871)
    ·
      refine ⟨81054400320570105004939307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54036266880380070003292871 81054400320570105004939307)
      ·
        refine ⟨121581600480855157507408961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81054400320570105004939307 121581600480855157507408961)
        ·
          refine ⟨91186200360641368130556721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121581600480855157507408961 91186200360641368130556721)
          ·
            refine ⟨68389650270481026097917541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91186200360641368130556721 68389650270481026097917541)
            ·
              refine ⟨12823059425715192393359539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68389650270481026097917541 12823059425715192393359539)
              ·
                refine ⟨19234589138572788590039309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12823059425715192393359539 19234589138572788590039309)
                ·
                  refine ⟨7212970926964795721264741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19234589138572788590039309 7212970926964795721264741)
                  ·
                    refine ⟨1352432048805899197737139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7212970926964795721264741 1352432048805899197737139)
                    ·
                      rfl

theorem cell22_3950778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3950778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950778 prefixEnd_3950778 := by exact prefixLift 3950778
  have htrace : WordTrace (prefixWord ++ tailWord_3950778) baseStart_3950778 baseEnd_3950778 := by
    simpa [prefixWord, tailWord_3950778, baseEnd_3950778] using wordTrace_append hprefix tailTrace_3950778
  have hstable : (prefixWord ++ tailWord_3950778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950778).length < 2 ^ (prefixWord ++ tailWord_3950778).sum := by decide
  have hdescent : baseEnd_3950778 < baseStart_3950778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950786 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3950786 : Nat := 118140960795 + 3950786 * 2 ^ 59
def prefixEnd_3950786 : Nat := 4983230072969 + 3 ^ 40 * 3950786 * 2
def baseEnd_3950786 : Nat := 1352434787369389843537115

theorem tailTrace_3950786 : CollatzResearch.WordTrace tailWord_3950786 prefixEnd_3950786 1352434787369389843537115 := by
  unfold tailWord_3950786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024250866246134343768053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96064668976656358250048141 36024250866246134343768053)
  ·
    refine ⟨3377273518710575094728255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36024250866246134343768053 3377273518710575094728255)
    ·
      refine ⟨5065910278065862642092383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377273518710575094728255 5065910278065862642092383)
      ·
        refine ⟨7598865417098793963138575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065910278065862642092383 7598865417098793963138575)
        ·
          refine ⟨11398298125648190944707863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598865417098793963138575 11398298125648190944707863)
          ·
            refine ⟨17097447188472286417061795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398298125648190944707863 17097447188472286417061795)
            ·
              refine ⟨25646170782708429625592693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17097447188472286417061795 25646170782708429625592693)
              ·
                refine ⟨2404328510878915277399315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25646170782708429625592693 2404328510878915277399315)
                ·
                  refine ⟨3606492766318372916098973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404328510878915277399315 3606492766318372916098973)
                  ·
                    refine ⟨1352434787369389843537115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606492766318372916098973 1352434787369389843537115)
                    ·
                      rfl

theorem cell22_3950786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3950786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950786 prefixEnd_3950786 := by exact prefixLift 3950786
  have htrace : WordTrace (prefixWord ++ tailWord_3950786) baseStart_3950786 baseEnd_3950786 := by
    simpa [prefixWord, tailWord_3950786, baseEnd_3950786] using wordTrace_append hprefix tailTrace_3950786
  have hstable : (prefixWord ++ tailWord_3950786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950786).length < 2 ^ (prefixWord ++ tailWord_3950786).sum := by decide
  have hdescent : baseEnd_3950786 < baseStart_3950786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950810 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_3950810 : Nat := 118140960795 + 3950810 * 2 ^ 59
def prefixEnd_3950810 : Nat := 4983230072969 + 3 ^ 40 * 3950810 * 2
def baseEnd_3950810 : Nat := 450814334353287260312347

theorem tailTrace_3950810 : CollatzResearch.WordTrace tailWord_3950810 prefixEnd_3950810 450814334353287260312347 := by
  unfold tailWord_3950810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024469704224397368486471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96065252544598392982630589 36024469704224397368486471)
  ·
    refine ⟨54036704556336596052729707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36024469704224397368486471 54036704556336596052729707)
    ·
      refine ⟨81055056834504894079094561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54036704556336596052729707 81055056834504894079094561)
      ·
        refine ⟨60791292625878670559320921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81055056834504894079094561 60791292625878670559320921)
        ·
          refine ⟨45593469469409002919490691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60791292625878670559320921 45593469469409002919490691)
          ·
            refine ⟨68390204204113504379236037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45593469469409002919490691 68390204204113504379236037)
            ·
              refine ⟨12823163288271282071106757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68390204204113504379236037 12823163288271282071106757)
              ·
                refine ⟨2404343116550865388332517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12823163288271282071106757 2404343116550865388332517)
                ·
                  refine ⟨450814334353287260312347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404343116550865388332517 450814334353287260312347)
                  ·
                    rfl

theorem cell22_3950810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_3950810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950810 prefixEnd_3950810 := by exact prefixLift 3950810
  have htrace : WordTrace (prefixWord ++ tailWord_3950810) baseStart_3950810 baseEnd_3950810 := by
    simpa [prefixWord, tailWord_3950810, baseEnd_3950810] using wordTrace_append hprefix tailTrace_3950810
  have hstable : (prefixWord ++ tailWord_3950810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950810).length < 2 ^ (prefixWord ++ tailWord_3950810).sum := by decide
  have hdescent : baseEnd_3950810 < baseStart_3950810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950930 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3950930 : Nat := 118140960795 + 3950930 * 2 ^ 59
def prefixEnd_3950930 : Nat := 4983230072969 + 3 ^ 40 * 3950930 * 2
def baseEnd_3950930 : Nat := 1352484081512221467936673

theorem tailTrace_3950930 : CollatzResearch.WordTrace tailWord_3950930 prefixEnd_3950930 1352484081512221467936673 := by
  unfold tailWord_3950930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36025563894115712492078561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96068170384308566645542829 36025563894115712492078561)
  ·
    refine ⟨27019172920586784369058921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36025563894115712492078561 27019172920586784369058921)
    ·
      refine ⟨20264379690440088276794191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27019172920586784369058921 20264379690440088276794191)
      ·
        refine ⟨30396569535660132415191287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20264379690440088276794191 30396569535660132415191287)
        ·
          refine ⟨45594854303490198622786931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30396569535660132415191287 45594854303490198622786931)
          ·
            refine ⟨68392281455235297934180397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45594854303490198622786931 68392281455235297934180397)
            ·
              refine ⟨25647105545713236725317649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68392281455235297934180397 25647105545713236725317649)
              ·
                refine ⟨19235329159284927543988237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25647105545713236725317649 19235329159284927543988237)
                ·
                  refine ⟨7213248434731847828995589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19235329159284927543988237 7213248434731847828995589)
                  ·
                    refine ⟨1352484081512221467936673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213248434731847828995589 1352484081512221467936673)
                    ·
                      rfl

theorem cell22_3950930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3950930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950930 prefixEnd_3950930 := by exact prefixLift 3950930
  have htrace : WordTrace (prefixWord ++ tailWord_3950930) baseStart_3950930 baseEnd_3950930 := by
    simpa [prefixWord, tailWord_3950930, baseEnd_3950930] using wordTrace_append hprefix tailTrace_3950930
  have hstable : (prefixWord ++ tailWord_3950930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950930).length < 2 ^ (prefixWord ++ tailWord_3950930).sum := by decide
  have hdescent : baseEnd_3950930 < baseStart_3950930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950960 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_3950960 : Nat := 118140960795 + 3950960 * 2 ^ 59
def prefixEnd_3950960 : Nat := 4983230072969 + 3 ^ 40 * 3950960 * 2
def baseEnd_3950960 : Nat := 1352494351125311389686581

theorem tailTrace_3950960 : CollatzResearch.WordTrace tailWord_3950960 prefixEnd_3950960 1352494351125311389686581 := by
  unfold tailWord_3950960
  simp only [CollatzResearch.WordTrace]
  refine ⟨72051674883177082545953167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96068899844236110061270889 72051674883177082545953167)
  ·
    refine ⟨108077512324765623818929751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72051674883177082545953167 108077512324765623818929751)
    ·
      refine ⟨162116268487148435728394627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108077512324765623818929751 162116268487148435728394627)
      ·
        refine ⟨243174402730722653592591941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162116268487148435728394627 243174402730722653592591941)
        ·
          refine ⟨45595200512010497548610989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243174402730722653592591941 45595200512010497548610989)
          ·
            refine ⟨17098200192003936580729121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45595200512010497548610989 17098200192003936580729121)
            ·
              refine ⟨12823650144002952435546841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17098200192003936580729121 12823650144002952435546841)
              ·
                refine ⟨9617737608002214326660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12823650144002952435546841 9617737608002214326660131)
                ·
                  refine ⟨14426606412003321489990197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9617737608002214326660131 14426606412003321489990197)
                  ·
                    refine ⟨1352494351125311389686581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14426606412003321489990197 1352494351125311389686581)
                    ·
                      rfl

theorem cell22_3950960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_3950960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950960 prefixEnd_3950960 := by exact prefixLift 3950960
  have htrace : WordTrace (prefixWord ++ tailWord_3950960) baseStart_3950960 baseEnd_3950960 := by
    simpa [prefixWord, tailWord_3950960, baseEnd_3950960] using wordTrace_append hprefix tailTrace_3950960
  have hstable : (prefixWord ++ tailWord_3950960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950960).length < 2 ^ (prefixWord ++ tailWord_3950960).sum := by decide
  have hdescent : baseEnd_3950960 < baseStart_3950960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3950962 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_3950962 : Nat := 118140960795 + 3950962 * 2 ^ 59
def prefixEnd_3950962 : Nat := 4983230072969 + 3 ^ 40 * 3950962 * 2
def baseEnd_3950962 : Nat := 450831678588728017045525

theorem tailTrace_3950962 : CollatzResearch.WordTrace tailWord_3950962 prefixEnd_3950962 450831678588728017045525 := by
  unfold tailWord_3950962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36025855678086729858369785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96068948474897946288986093 36025855678086729858369785)
  ·
    refine ⟨27019391758565047393777339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36025855678086729858369785 27019391758565047393777339)
    ·
      refine ⟨40529087637847571090666009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27019391758565047393777339 40529087637847571090666009)
      ·
        refine ⟨30396815728385678317999507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40529087637847571090666009 30396815728385678317999507)
        ·
          refine ⟨45595223592578517476999261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30396815728385678317999507 45595223592578517476999261)
          ·
            refine ⟨17098208847216944053874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45595223592578517476999261 17098208847216944053874723)
            ·
              refine ⟨25647313270825416080812085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17098208847216944053874723 25647313270825416080812085)
              ·
                refine ⟨2404435619139882757576133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25647313270825416080812085 2404435619139882757576133)
                ·
                  refine ⟨450831678588728017045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404435619139882757576133 450831678588728017045525)
                  ·
                    rfl

theorem cell22_3950962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_3950962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3950962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3950962 prefixEnd_3950962 := by exact prefixLift 3950962
  have htrace : WordTrace (prefixWord ++ tailWord_3950962) baseStart_3950962 baseEnd_3950962 := by
    simpa [prefixWord, tailWord_3950962, baseEnd_3950962] using wordTrace_append hprefix tailTrace_3950962
  have hstable : (prefixWord ++ tailWord_3950962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3950962).length < 2 ^ (prefixWord ++ tailWord_3950962).sum := by decide
  have hdescent : baseEnd_3950962 < baseStart_3950962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3950962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951041 : List Nat := [1, 2, 7, 1, 1, 1, 2, 7]
def baseStart_3951041 : Nat := 118140960795 + 3951041 * 2 ^ 59
def prefixEnd_3951041 : Nat := 4983230072969 + 3 ^ 40 * 3951041 * 2
def baseEnd_3951041 : Nat := 150280231008961575379037

theorem tailTrace_3951041 : CollatzResearch.WordTrace tailWord_3951041 prefixEnd_3951041 150280231008961575379037 := by
  unfold tailWord_3951041
  simp only [CollatzResearch.WordTrace]
  refine ⟨144106304079060715925604977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96070869386040477283736651 144106304079060715925604977)
  ·
    refine ⟨108079728059295536944203733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144106304079060715925604977 108079728059295536944203733)
    ·
      refine ⟨2533118626389739147129775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 108079728059295536944203733 2533118626389739147129775)
      ·
        refine ⟨3799677939584608720694663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533118626389739147129775 3799677939584608720694663)
        ·
          refine ⟨5699516909376913081041995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799677939584608720694663 5699516909376913081041995)
          ·
            refine ⟨8549275364065369621562993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699516909376913081041995 8549275364065369621562993)
            ·
              refine ⟨6411956523049027216172245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549275364065369621562993 6411956523049027216172245)
              ·
                refine ⟨150280231008961575379037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6411956523049027216172245 150280231008961575379037)
                ·
                  rfl

theorem cell22_3951041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 7].length) (baseStart_3951041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951041 prefixEnd_3951041 := by exact prefixLift 3951041
  have htrace : WordTrace (prefixWord ++ tailWord_3951041) baseStart_3951041 baseEnd_3951041 := by
    simpa [prefixWord, tailWord_3951041, baseEnd_3951041] using wordTrace_append hprefix tailTrace_3951041
  have hstable : (prefixWord ++ tailWord_3951041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951041).length < 2 ^ (prefixWord ++ tailWord_3951041).sum := by decide
  have hdescent : baseEnd_3951041 < baseStart_3951041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951050 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3951050 : Nat := 118140960795 + 3951050 * 2 ^ 59
def prefixEnd_3951050 : Nat := 4983230072969 + 3 ^ 40 * 3951050 * 2
def baseEnd_3951050 : Nat := 1352525159964581154936305

theorem tailTrace_3951050 : CollatzResearch.WordTrace tailWord_3951050 prefixEnd_3951050 1352525159964581154936305 := by
  unfold tailWord_3951050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36026658084007027615670651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96071088224018740308455069 36026658084007027615670651)
  ·
    refine ⟨54039987126010541423505977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36026658084007027615670651 54039987126010541423505977)
    ·
      refine ⟨40529990344507906067629483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54039987126010541423505977 40529990344507906067629483)
      ·
        refine ⟨60794985516761859101444225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40529990344507906067629483 60794985516761859101444225)
        ·
          refine ⟨45596239137571394326083169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60794985516761859101444225 45596239137571394326083169)
          ·
            refine ⟨34197179353178545744562377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45596239137571394326083169 34197179353178545744562377)
            ·
              refine ⟨25647884514883909308421783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34197179353178545744562377 25647884514883909308421783)
              ·
                refine ⟨38471826772325863962632675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25647884514883909308421783 38471826772325863962632675)
                ·
                  refine ⟨57707740158488795943949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38471826772325863962632675 57707740158488795943949013)
                  ·
                    refine ⟨1352525159964581154936305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57707740158488795943949013 1352525159964581154936305)
                    ·
                      rfl

theorem cell22_3951050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3951050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951050 prefixEnd_3951050 := by exact prefixLift 3951050
  have htrace : WordTrace (prefixWord ++ tailWord_3951050) baseStart_3951050 baseEnd_3951050 := by
    simpa [prefixWord, tailWord_3951050, baseEnd_3951050] using wordTrace_append hprefix tailTrace_3951050
  have hstable : (prefixWord ++ tailWord_3951050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951050).length < 2 ^ (prefixWord ++ tailWord_3951050).sum := by decide
  have hdescent : baseEnd_3951050 < baseStart_3951050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951090 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3951090 : Nat := 118140960795 + 3951090 * 2 ^ 59
def prefixEnd_3951090 : Nat := 4983230072969 + 3 ^ 40 * 3951090 * 2
def baseEnd_3951090 : Nat := 1352538852782034383936183

theorem tailTrace_3951090 : CollatzResearch.WordTrace tailWord_3951090 prefixEnd_3951090 1352538852782034383936183 := by
  unfold tailWord_3951090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36027022813970799323534681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96072060837255464862759149 36027022813970799323534681)
  ·
    refine ⟨27020267110478099492651011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36027022813970799323534681 27020267110478099492651011)
    ·
      refine ⟨40530400665717149238976517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27020267110478099492651011 40530400665717149238976517)
      ·
        refine ⟨7599450124821965482308097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40530400665717149238976517 7599450124821965482308097)
        ·
          refine ⟨5699587593616474111731073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599450124821965482308097 5699587593616474111731073)
          ·
            refine ⟨4274690695212355583798305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699587593616474111731073 4274690695212355583798305)
            ·
              refine ⟨3206018021409266687848729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274690695212355583798305 3206018021409266687848729)
              ·
                refine ⟨2404513516056950015886547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206018021409266687848729 2404513516056950015886547)
                ·
                  refine ⟨3606770274085425023829821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404513516056950015886547 3606770274085425023829821)
                  ·
                    refine ⟨1352538852782034383936183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606770274085425023829821 1352538852782034383936183)
                    ·
                      rfl

theorem cell22_3951090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3951090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951090 prefixEnd_3951090 := by exact prefixLift 3951090
  have htrace : WordTrace (prefixWord ++ tailWord_3951090) baseStart_3951090 baseEnd_3951090 := by
    simpa [prefixWord, tailWord_3951090, baseEnd_3951090] using wordTrace_append hprefix tailTrace_3951090
  have hstable : (prefixWord ++ tailWord_3951090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951090).length < 2 ^ (prefixWord ++ tailWord_3951090).sum := by decide
  have hdescent : baseEnd_3951090 < baseStart_3951090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951112 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_3951112 : Nat := 118140960795 + 3951112 * 2 ^ 59
def prefixEnd_3951112 : Nat := 4983230072969 + 3 ^ 40 * 3951112 * 2
def baseEnd_3951112 : Nat := 1352546383831633659886115

theorem tailTrace_3951112 : CollatzResearch.WordTrace tailWord_3951112 prefixEnd_3951112 1352546383831633659886115 := by
  unfold tailWord_3951112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72054446830901747525719795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96072595774535663367626393 72054446830901747525719795)
  ·
    refine ⟨108081670246352621288579693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72054446830901747525719795 108081670246352621288579693)
    ·
      refine ⟨40530626342382232983217385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108081670246352621288579693 40530626342382232983217385)
      ·
        refine ⟨30397969756786674737413039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40530626342382232983217385 30397969756786674737413039)
        ·
          refine ⟨45596954635180012106119559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30397969756786674737413039 45596954635180012106119559)
          ·
            refine ⟨68395431952770018159179339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45596954635180012106119559 68395431952770018159179339)
            ·
              refine ⟨102593147929155027238769009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68395431952770018159179339 102593147929155027238769009)
              ·
                refine ⟨76944860946866270429076757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102593147929155027238769009 76944860946866270429076757)
                ·
                  refine ⟨3606790356884356426362973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76944860946866270429076757 3606790356884356426362973)
                  ·
                    refine ⟨1352546383831633659886115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606790356884356426362973 1352546383831633659886115)
                    ·
                      rfl

theorem cell22_3951112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_3951112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951112 prefixEnd_3951112 := by exact prefixLift 3951112
  have htrace : WordTrace (prefixWord ++ tailWord_3951112) baseStart_3951112 baseEnd_3951112 := by
    simpa [prefixWord, tailWord_3951112, baseEnd_3951112] using wordTrace_append hprefix tailTrace_3951112
  have hstable : (prefixWord ++ tailWord_3951112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951112).length < 2 ^ (prefixWord ++ tailWord_3951112).sum := by decide
  have hdescent : baseEnd_3951112 < baseStart_3951112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951146 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3951146 : Nat := 118140960795 + 3951146 * 2 ^ 59
def prefixEnd_3951146 : Nat := 4983230072969 + 3 ^ 40 * 3951146 * 2
def baseEnd_3951146 : Nat := 1352558022726468904536011

theorem tailTrace_3951146 : CollatzResearch.WordTrace tailWord_3951146 prefixEnd_3951146 1352558022726468904536011 := by
  unfold tailWord_3951146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36027533435920079714544323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96073422495786879238784861 36027533435920079714544323)
  ·
    refine ⟨54041300153880119571816485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36027533435920079714544323 54041300153880119571816485)
    ·
      refine ⟨10132743778852522419715591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54041300153880119571816485 10132743778852522419715591)
      ·
        refine ⟨15199115668278783629573387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132743778852522419715591 15199115668278783629573387)
        ·
          refine ⟨22798673502418175444360081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15199115668278783629573387 22798673502418175444360081)
          ·
            refine ⟨17099005126813631583270061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22798673502418175444360081 17099005126813631583270061)
            ·
              refine ⟨6412126922555111843726273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17099005126813631583270061 6412126922555111843726273)
              ·
                refine ⟨4809095191916333882794705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412126922555111843726273 4809095191916333882794705)
                ·
                  refine ⟨3606821393937250412096029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809095191916333882794705 3606821393937250412096029)
                  ·
                    refine ⟨1352558022726468904536011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606821393937250412096029 1352558022726468904536011)
                    ·
                      rfl

theorem cell22_3951146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3951146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951146 prefixEnd_3951146 := by exact prefixLift 3951146
  have htrace : WordTrace (prefixWord ++ tailWord_3951146) baseStart_3951146 baseEnd_3951146 := by
    simpa [prefixWord, tailWord_3951146, baseEnd_3951146] using wordTrace_append hprefix tailTrace_3951146
  have hstable : (prefixWord ++ tailWord_3951146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951146).length < 2 ^ (prefixWord ++ tailWord_3951146).sum := by decide
  have hdescent : baseEnd_3951146 < baseStart_3951146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951208 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3951208 : Nat := 118140960795 + 3951208 * 2 ^ 59
def prefixEnd_3951208 : Nat := 4983230072969 + 3 ^ 40 * 3951208 * 2
def baseEnd_3951208 : Nat := 1352579246593521409485821

theorem tailTrace_3951208 : CollatzResearch.WordTrace tailWord_3951208 prefixEnd_3951208 1352579246593521409485821 := by
  unfold tailWord_3951208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72056197534727851723467139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96074930046303802297956185 72056197534727851723467139)
  ·
    refine ⟨108084296302091777585200709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72056197534727851723467139 108084296302091777585200709)
    ·
      refine ⟨20265805556642208297225133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108084296302091777585200709 20265805556642208297225133)
      ·
        refine ⟨7599677083740828111459425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20265805556642208297225133 7599677083740828111459425)
        ·
          refine ⟨5699757812805621083594569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599677083740828111459425 5699757812805621083594569)
          ·
            refine ⟨4274818359604215812695927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699757812805621083594569 4274818359604215812695927)
            ·
              refine ⟨6412227539406323719043891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274818359604215812695927 6412227539406323719043891)
              ·
                refine ⟨9618341309109485578565837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412227539406323719043891 9618341309109485578565837)
                ·
                  refine ⟨3606877990916057091962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9618341309109485578565837 3606877990916057091962189)
                  ·
                    refine ⟨1352579246593521409485821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3606877990916057091962189 1352579246593521409485821)
                    ·
                      rfl

theorem cell22_3951208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3951208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951208 prefixEnd_3951208 := by exact prefixLift 3951208
  have htrace : WordTrace (prefixWord ++ tailWord_3951208) baseStart_3951208 baseEnd_3951208 := by
    simpa [prefixWord, tailWord_3951208, baseEnd_3951208] using wordTrace_append hprefix tailTrace_3951208
  have hstable : (prefixWord ++ tailWord_3951208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951208).length < 2 ^ (prefixWord ++ tailWord_3951208).sum := by decide
  have hdescent : baseEnd_3951208 < baseStart_3951208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951221 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 5]
def baseStart_3951221 : Nat := 118140960795 + 3951221 * 2 ^ 59
def prefixEnd_3951221 : Nat := 4983230072969 + 3 ^ 40 * 3951221 * 2
def baseEnd_3951221 : Nat := 450861232253064569636927

theorem tailTrace_3951221 : CollatzResearch.WordTrace tailWord_3951221 prefixEnd_3951221 450861232253064569636927 := by
  unfold tailWord_3951221
  simp only [CollatzResearch.WordTrace]
  refine ⟨144112869218408606667157517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96075246145605737778105011 144112869218408606667157517)
  ·
    refine ⟨54042325956903227500184069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144112869218408606667157517 54042325956903227500184069)
    ·
      refine ⟨10132936116919355156284513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54042325956903227500184069 10132936116919355156284513)
      ·
        refine ⟨7599702087689516367213385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10132936116919355156284513 7599702087689516367213385)
        ·
          refine ⟨5699776565767137275410039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599702087689516367213385 5699776565767137275410039)
          ·
            refine ⟨8549664848650705913115059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699776565767137275410039 8549664848650705913115059)
            ·
              refine ⟨12824497272976058869672589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549664848650705913115059 12824497272976058869672589)
              ·
                refine ⟨4809186477366022076127221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12824497272976058869672589 4809186477366022076127221)
                ·
                  refine ⟨450861232253064569636927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809186477366022076127221 450861232253064569636927)
                  ·
                    rfl

theorem cell22_3951221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_3951221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951221 prefixEnd_3951221 := by exact prefixLift 3951221
  have htrace : WordTrace (prefixWord ++ tailWord_3951221) baseStart_3951221 baseEnd_3951221 := by
    simpa [prefixWord, tailWord_3951221, baseEnd_3951221] using wordTrace_append hprefix tailTrace_3951221
  have hstable : (prefixWord ++ tailWord_3951221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951221).length < 2 ^ (prefixWord ++ tailWord_3951221).sum := by decide
  have hdescent : baseEnd_3951221 < baseStart_3951221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951247 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_3951247 : Nat := 118140960795 + 3951247 * 2 ^ 59
def prefixEnd_3951247 : Nat := 4983230072969 + 3 ^ 40 * 3951247 * 2
def baseEnd_3951247 : Nat := 1352592597090538307760701

theorem tailTrace_3951247 : CollatzResearch.WordTrace tailWord_3951247 prefixEnd_3951247 1352592597090538307760701 := by
  unfold tailWord_3951247
  simp only [CollatzResearch.WordTrace]
  refine ⟨144113817516314413107603995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96075878344209608738402663 144113817516314413107603995)
  ·
    refine ⟨216170726274471619661405993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144113817516314413107603995 216170726274471619661405993)
    ·
      refine ⟨162128044705853714746054495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216170726274471619661405993 162128044705853714746054495)
      ·
        refine ⟨243192067058780572119081743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162128044705853714746054495 243192067058780572119081743)
        ·
          refine ⟨364788100588170858178622615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243192067058780572119081743 364788100588170858178622615)
          ·
            refine ⟨547182150882256287267933923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364788100588170858178622615 547182150882256287267933923)
            ·
              refine ⟨820773226323384430901900885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547182150882256287267933923 820773226323384430901900885)
              ·
                refine ⟨9618436245977161299631651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 820773226323384430901900885 9618436245977161299631651)
                ·
                  refine ⟨14427654368965741949447477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9618436245977161299631651 14427654368965741949447477)
                  ·
                    refine ⟨1352592597090538307760701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14427654368965741949447477 1352592597090538307760701)
                    ·
                      rfl

theorem cell22_3951247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_3951247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951247 prefixEnd_3951247 := by exact prefixLift 3951247
  have htrace : WordTrace (prefixWord ++ tailWord_3951247) baseStart_3951247 baseEnd_3951247 := by
    simpa [prefixWord, tailWord_3951247, baseEnd_3951247] using wordTrace_append hprefix tailTrace_3951247
  have hstable : (prefixWord ++ tailWord_3951247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951247).length < 2 ^ (prefixWord ++ tailWord_3951247).sum := by decide
  have hdescent : baseEnd_3951247 < baseStart_3951247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951296 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_3951296 : Nat := 118140960795 + 3951296 * 2 ^ 59
def prefixEnd_3951296 : Nat := 4983230072969 + 3 ^ 40 * 3951296 * 2
def baseEnd_3951296 : Nat := 1352609370791918513285551

theorem tailTrace_3951296 : CollatzResearch.WordTrace tailWord_3951296 prefixEnd_3951296 1352609370791918513285551 := by
  unfold tailWord_3951296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72057802346568447238068871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96077069795424596317425161 72057802346568447238068871)
  ·
    refine ⟨108086703519852670857103307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72057802346568447238068871 108086703519852670857103307)
    ·
      refine ⟨162130055279779006285654961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108086703519852670857103307 162130055279779006285654961)
      ·
        refine ⟨121597541459834254714241221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162130055279779006285654961 121597541459834254714241221)
        ·
          refine ⟨22799539023718922758920229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121597541459834254714241221 22799539023718922758920229)
          ·
            refine ⟨4274913566947298017297543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22799539023718922758920229 4274913566947298017297543)
            ·
              refine ⟨6412370350420947025946315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274913566947298017297543 6412370350420947025946315)
              ·
                refine ⟨9618555525631420538919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6412370350420947025946315 9618555525631420538919473)
                ·
                  refine ⟨7213916644223565404189605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9618555525631420538919473 7213916644223565404189605)
                  ·
                    refine ⟨1352609370791918513285551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213916644223565404189605 1352609370791918513285551)
                    ·
                      rfl

theorem cell22_3951296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_3951296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951296 prefixEnd_3951296 := by exact prefixLift 3951296
  have htrace : WordTrace (prefixWord ++ tailWord_3951296) baseStart_3951296 baseEnd_3951296 := by
    simpa [prefixWord, tailWord_3951296, baseEnd_3951296] using wordTrace_append hprefix tailTrace_3951296
  have hstable : (prefixWord ++ tailWord_3951296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951296).length < 2 ^ (prefixWord ++ tailWord_3951296).sum := by decide
  have hdescent : baseEnd_3951296 < baseStart_3951296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951433 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_3951433 : Nat := 118140960795 + 3951433 * 2 ^ 59
def prefixEnd_3951433 : Nat := 4983230072969 + 3 ^ 40 * 3951433 * 2
def baseEnd_3951433 : Nat := 1352656268691695822610131

theorem tailTrace_3951433 : CollatzResearch.WordTrace tailWord_3951433 prefixEnd_3951433 1352656268691695822610131 := by
  unfold tailWord_3951433
  simp only [CollatzResearch.WordTrace]
  refine ⟨144120601493640566873874953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96080400995760377915916635 144120601493640566873874953)
  ·
    refine ⟨108090451120230425155406215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144120601493640566873874953 108090451120230425155406215)
    ·
      refine ⟨162135676680345637733109323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108090451120230425155406215 162135676680345637733109323)
      ·
        refine ⟨243203515020518456599663985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162135676680345637733109323 243203515020518456599663985)
        ·
          refine ⟨182402636265388842449747989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243203515020518456599663985 182402636265388842449747989)
          ·
            refine ⟨8550123574940101989831937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182402636265388842449747989 8550123574940101989831937)
            ·
              refine ⟨6412592681205076492373953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550123574940101989831937 6412592681205076492373953)
              ·
                refine ⟨4809444510903807369280465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412592681205076492373953 4809444510903807369280465)
                ·
                  refine ⟨3607083383177855526960349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809444510903807369280465 3607083383177855526960349)
                  ·
                    refine ⟨1352656268691695822610131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607083383177855526960349 1352656268691695822610131)
                    ·
                      rfl

theorem cell22_3951433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_3951433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951433 prefixEnd_3951433 := by exact prefixLift 3951433
  have htrace : WordTrace (prefixWord ++ tailWord_3951433) baseStart_3951433 baseEnd_3951433 := by
    simpa [prefixWord, tailWord_3951433, baseEnd_3951433] using wordTrace_append hprefix tailTrace_3951433
  have hstable : (prefixWord ++ tailWord_3951433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951433).length < 2 ^ (prefixWord ++ tailWord_3951433).sum := by decide
  have hdescent : baseEnd_3951433 < baseStart_3951433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951461 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_3951461 : Nat := 118140960795 + 3951461 * 2 ^ 59
def prefixEnd_3951461 : Nat := 4983230072969 + 3 ^ 40 * 3951461 * 2
def baseEnd_3951461 : Nat := 1352665853663913082910045

theorem tailTrace_3951461 : CollatzResearch.WordTrace tailWord_3951461 prefixEnd_3951461 1352665853663913082910045 := by
  unfold tailWord_3951461
  simp only [CollatzResearch.WordTrace]
  refine ⟨144121622737539127655894237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96081081825026085103929491 144121622737539127655894237)
  ·
    refine ⟨54045608526577172870960339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144121622737539127655894237 54045608526577172870960339)
    ·
      refine ⟨81068412789865759306440509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54045608526577172870960339 81068412789865759306440509)
      ·
        refine ⟨30400654796199659739915191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81068412789865759306440509 30400654796199659739915191)
        ·
          refine ⟨45600982194299489609872787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30400654796199659739915191 45600982194299489609872787)
          ·
            refine ⟨68401473291449234414809181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45600982194299489609872787 68401473291449234414809181)
            ·
              refine ⟨25650552484293462905553443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68401473291449234414809181 25650552484293462905553443)
              ·
                refine ⟨38475828726440194358330165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25650552484293462905553443 38475828726440194358330165)
                ·
                  refine ⟨3607108943103768221093453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38475828726440194358330165 3607108943103768221093453)
                  ·
                    refine ⟨1352665853663913082910045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607108943103768221093453 1352665853663913082910045)
                    ·
                      rfl

theorem cell22_3951461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_3951461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951461 prefixEnd_3951461 := by exact prefixLift 3951461
  have htrace : WordTrace (prefixWord ++ tailWord_3951461) baseStart_3951461 baseEnd_3951461 := by
    simpa [prefixWord, tailWord_3951461, baseEnd_3951461] using wordTrace_append hprefix tailTrace_3951461
  have hstable : (prefixWord ++ tailWord_3951461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951461).length < 2 ^ (prefixWord ++ tailWord_3951461).sum := by decide
  have hdescent : baseEnd_3951461 < baseStart_3951461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951495 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 1, 3]
def baseStart_3951495 : Nat := 118140960795 + 3951495 * 2 ^ 59
def prefixEnd_3951495 : Nat := 4983230072969 + 3 ^ 40 * 3951495 * 2
def baseEnd_3951495 : Nat := 1352677492558748327559941

theorem tailTrace_3951495 : CollatzResearch.WordTrace tailWord_3951495 prefixEnd_3951495 1352677492558748327559941 := by
  unfold tailWord_3951495
  simp only [CollatzResearch.WordTrace]
  refine ⟨144122862819415951462631939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96081908546277300975087959 144122862819415951462631939)
  ·
    refine ⟨216184294229123927193947909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144122862819415951462631939 216184294229123927193947909)
    ·
      refine ⟨40534555167960736348865233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216184294229123927193947909 40534555167960736348865233)
      ·
        refine ⟨30400916375970552261648925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40534555167960736348865233 30400916375970552261648925)
        ·
          refine ⟨11400343640988957098118347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30400916375970552261648925 11400343640988957098118347)
          ·
            refine ⟨17100515461483435647177521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400343640988957098118347 17100515461483435647177521)
            ·
              refine ⟨12825386596112576735383141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17100515461483435647177521 12825386596112576735383141)
              ·
                refine ⟨2404759986771108137884339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12825386596112576735383141 2404759986771108137884339)
                ·
                  refine ⟨3607139980156662206826509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404759986771108137884339 3607139980156662206826509)
                  ·
                    refine ⟨1352677492558748327559941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607139980156662206826509 1352677492558748327559941)
                    ·
                      rfl

theorem cell22_3951495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_3951495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951495 prefixEnd_3951495 := by exact prefixLift 3951495
  have htrace : WordTrace (prefixWord ++ tailWord_3951495) baseStart_3951495 baseEnd_3951495 := by
    simpa [prefixWord, tailWord_3951495, baseEnd_3951495] using wordTrace_append hprefix tailTrace_3951495
  have hstable : (prefixWord ++ tailWord_3951495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951495).length < 2 ^ (prefixWord ++ tailWord_3951495).sum := by decide
  have hdescent : baseEnd_3951495 < baseStart_3951495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951598 : List Nat := [4, 1, 2, 1, 5, 9]
def baseStart_3951598 : Nat := 118140960795 + 3951598 * 2 ^ 59
def prefixEnd_3951598 : Nat := 4983230072969 + 3 ^ 40 * 3951598 * 2
def baseEnd_3951598 : Nat := 16700157426712227064625

theorem tailTrace_3951598 : CollatzResearch.WordTrace tailWord_3951598 prefixEnd_3951598 16700157426712227064625 := by
  unfold tailWord_3951598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015827442255350006703931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96084413025361866702420965 18015827442255350006703931)
  ·
    refine ⟨27023741163383025010055897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015827442255350006703931 27023741163383025010055897)
    ·
      refine ⟨20267805872537268757541923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27023741163383025010055897 20267805872537268757541923)
      ·
        refine ⟨30401708808805903136312885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20267805872537268757541923 30401708808805903136312885)
        ·
          refine ⟨2850160200825553419029333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30401708808805903136312885 2850160200825553419029333)
          ·
            refine ⟨16700157426712227064625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2850160200825553419029333 16700157426712227064625)
            ·
              rfl

theorem cell22_3951598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 9].length) (baseStart_3951598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951598 prefixEnd_3951598 := by exact prefixLift 3951598
  have htrace : WordTrace (prefixWord ++ tailWord_3951598) baseStart_3951598 baseEnd_3951598 := by
    simpa [prefixWord, tailWord_3951598, baseEnd_3951598] using wordTrace_append hprefix tailTrace_3951598
  have hstable : (prefixWord ++ tailWord_3951598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951598).length < 2 ^ (prefixWord ++ tailWord_3951598).sum := by decide
  have hdescent : baseEnd_3951598 < baseStart_3951598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951613 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3951613 : Nat := 118140960795 + 3951613 * 2 ^ 59
def prefixEnd_3951613 : Nat := 4983230072969 + 3 ^ 40 * 3951613 * 2
def baseEnd_3951613 : Nat := 1352717886370235353109579

theorem tailTrace_3951613 : CollatzResearch.WordTrace tailWord_3951613 prefixEnd_3951613 1352717886370235353109579 := by
  unfold tailWord_3951613
  simp only [CollatzResearch.WordTrace]
  refine ⟨144127166632988457615427493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96084777755325638410284995 144127166632988457615427493)
  ·
    refine ⟨27023843743685335802892655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144127166632988457615427493 27023843743685335802892655)
    ·
      refine ⟨40535765615528003704338983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023843743685335802892655 40535765615528003704338983)
      ·
        refine ⟨60803648423292005556508475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40535765615528003704338983 60803648423292005556508475)
        ·
          refine ⟨91205472634938008334762713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60803648423292005556508475 91205472634938008334762713)
          ·
            refine ⟨68404104476203506251072035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91205472634938008334762713 68404104476203506251072035)
            ·
              refine ⟨102606156714305259376608053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68404104476203506251072035 102606156714305259376608053)
              ·
                refine ⟨9619327191966118066557005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102606156714305259376608053 9619327191966118066557005)
                ·
                  refine ⟨3607247696987294274958877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619327191966118066557005 3607247696987294274958877)
                  ·
                    refine ⟨1352717886370235353109579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607247696987294274958877 1352717886370235353109579)
                    ·
                      rfl

theorem cell22_3951613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3951613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951613 prefixEnd_3951613 := by exact prefixLift 3951613
  have htrace : WordTrace (prefixWord ++ tailWord_3951613) baseStart_3951613 baseEnd_3951613 := by
    simpa [prefixWord, tailWord_3951613, baseEnd_3951613] using wordTrace_append hprefix tailTrace_3951613
  have hstable : (prefixWord ++ tailWord_3951613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951613).length < 2 ^ (prefixWord ++ tailWord_3951613).sum := by decide
  have hdescent : baseEnd_3951613 < baseStart_3951613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951630 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_3951630 : Nat := 118140960795 + 3951630 * 2 ^ 59
def prefixEnd_3951630 : Nat := 4983230072969 + 3 ^ 40 * 3951630 * 2
def baseEnd_3951630 : Nat := 1352723705817652975434527

theorem tailTrace_3951630 : CollatzResearch.WordTrace tailWord_3951630 prefixEnd_3951630 1352723705817652975434527 := by
  unfold tailWord_3951630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015973334240858689849543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96085191115951246345864229 18015973334240858689849543)
  ·
    refine ⟨27023960001361288034774315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015973334240858689849543 27023960001361288034774315)
    ·
      refine ⟨40535940002041932052161473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023960001361288034774315 40535940002041932052161473)
      ·
        refine ⟨30401955001531449039121105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40535940002041932052161473 30401955001531449039121105)
        ·
          refine ⟨22801466251148586779340829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30401955001531449039121105 22801466251148586779340829)
          ·
            refine ⟨8550549844180720042252811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22801466251148586779340829 8550549844180720042252811)
            ·
              refine ⟨12825824766271080063379217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550549844180720042252811 12825824766271080063379217)
              ·
                refine ⟨9619368574703310047534413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12825824766271080063379217 9619368574703310047534413)
                ·
                  refine ⟨3607263215513741267825405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9619368574703310047534413 3607263215513741267825405)
                  ·
                    refine ⟨1352723705817652975434527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607263215513741267825405 1352723705817652975434527)
                    ·
                      rfl

theorem cell22_3951630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_3951630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951630 prefixEnd_3951630 := by exact prefixLift 3951630
  have htrace : WordTrace (prefixWord ++ tailWord_3951630) baseStart_3951630 baseEnd_3951630 := by
    simpa [prefixWord, tailWord_3951630, baseEnd_3951630] using wordTrace_append hprefix tailTrace_3951630
  have hstable : (prefixWord ++ tailWord_3951630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951630).length < 2 ^ (prefixWord ++ tailWord_3951630).sum := by decide
  have hdescent : baseEnd_3951630 < baseStart_3951630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951647 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 1, 3]
def baseStart_3951647 : Nat := 118140960795 + 3951647 * 2 ^ 59
def prefixEnd_3951647 : Nat := 4983230072969 + 3 ^ 40 * 3951647 * 2
def baseEnd_3951647 : Nat := 1352729525265070597759475

theorem tailTrace_3951647 : CollatzResearch.WordTrace tailWord_3951647 prefixEnd_3951647 1352729525265070597759475 := by
  unfold tailWord_3951647
  simp only [CollatzResearch.WordTrace]
  refine ⟨144128406714865281422165195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96085604476576854281443463 144128406714865281422165195)
  ·
    refine ⟨216192610072297922133247793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144128406714865281422165195 216192610072297922133247793)
    ·
      refine ⟨162144457554223441599935845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216192610072297922133247793 162144457554223441599935845)
      ·
        refine ⟨30402085791416895299987971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162144457554223441599935845 30402085791416895299987971)
        ·
          refine ⟨45603128687125342949981957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30402085791416895299987971 45603128687125342949981957)
          ·
            refine ⟨8550586628836001803121617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45603128687125342949981957 8550586628836001803121617)
            ·
              refine ⟨6412939971627001352341213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550586628836001803121617 6412939971627001352341213)
              ·
                refine ⟨2404852489360125507127955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412939971627001352341213 2404852489360125507127955)
                ·
                  refine ⟨3607278734040188260691933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404852489360125507127955 3607278734040188260691933)
                  ·
                    refine ⟨1352729525265070597759475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607278734040188260691933 1352729525265070597759475)
                    ·
                      rfl

theorem cell22_3951647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_3951647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951647 prefixEnd_3951647 := by exact prefixLift 3951647
  have htrace : WordTrace (prefixWord ++ tailWord_3951647) baseStart_3951647 baseEnd_3951647 := by
    simpa [prefixWord, tailWord_3951647, baseEnd_3951647] using wordTrace_append hprefix tailTrace_3951647
  have hstable : (prefixWord ++ tailWord_3951647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951647).length < 2 ^ (prefixWord ++ tailWord_3951647).sum := by decide
  have hdescent : baseEnd_3951647 < baseStart_3951647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951737 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_3951737 : Nat := 118140960795 + 3951737 * 2 ^ 59
def prefixEnd_3951737 : Nat := 4983230072969 + 3 ^ 40 * 3951737 * 2
def baseEnd_3951737 : Nat := 1352760334104340363009199

theorem tailTrace_3951737 : CollatzResearch.WordTrace tailWord_3951737 prefixEnd_3951737 1352760334104340363009199 := by
  unfold tailWord_3951737
  simp only [CollatzResearch.WordTrace]
  refine ⟨144131689284539226792941465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96087792856359484528627643 144131689284539226792941465)
  ·
    refine ⟨108098766963404420094706099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144131689284539226792941465 108098766963404420094706099)
    ·
      refine ⟨162148150445106630142059149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108098766963404420094706099 162148150445106630142059149)
      ·
        refine ⟨60805556416914986303272181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162148150445106630142059149 60805556416914986303272181)
        ·
          refine ⟨5700520914085779965931767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60805556416914986303272181 5700520914085779965931767)
          ·
            refine ⟨8550781371128669948897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700520914085779965931767 8550781371128669948897651)
            ·
              refine ⟨12826172056693004923346477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550781371128669948897651 12826172056693004923346477)
              ·
                refine ⟨4809814521259876846254929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12826172056693004923346477 4809814521259876846254929)
                ·
                  refine ⟨3607360890944907634691197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809814521259876846254929 3607360890944907634691197)
                  ·
                    refine ⟨1352760334104340363009199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607360890944907634691197 1352760334104340363009199)
                    ·
                      rfl

theorem cell22_3951737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_3951737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951737 prefixEnd_3951737 := by exact prefixLift 3951737
  have htrace : WordTrace (prefixWord ++ tailWord_3951737) baseStart_3951737 baseEnd_3951737 := by
    simpa [prefixWord, tailWord_3951737, baseEnd_3951737] using wordTrace_append hprefix tailTrace_3951737
  have hstable : (prefixWord ++ tailWord_3951737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951737).length < 2 ^ (prefixWord ++ tailWord_3951737).sum := by decide
  have hdescent : baseEnd_3951737 < baseStart_3951737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951752 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3951752 : Nat := 118140960795 + 3951752 * 2 ^ 59
def prefixEnd_3951752 : Nat := 4983230072969 + 3 ^ 40 * 3951752 * 2
def baseEnd_3951752 : Nat := 1352765468910885323884153

theorem tailTrace_3951752 : CollatzResearch.WordTrace tailWord_3951752 prefixEnd_3951752 1352765468910885323884153 := by
  unfold tailWord_3951752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72066118189742442177368755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96088157586323256236491673 72066118189742442177368755)
  ·
    refine ⟨108099177284613663266053133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72066118189742442177368755 108099177284613663266053133)
    ·
      refine ⟨40537191481730123724769925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108099177284613663266053133 40537191481730123724769925)
      ·
        refine ⟨7600723402824398198394361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40537191481730123724769925 7600723402824398198394361)
        ·
          refine ⟨5700542552118298648795771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600723402824398198394361 5700542552118298648795771)
          ·
            refine ⟨8550813828177447973193657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700542552118298648795771 8550813828177447973193657)
            ·
              refine ⟨6413110371133085979895243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8550813828177447973193657 6413110371133085979895243)
              ·
                refine ⟨9619665556699628969842865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413110371133085979895243 9619665556699628969842865)
                ·
                  refine ⟨7214749167524721727382149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9619665556699628969842865 7214749167524721727382149)
                  ·
                    refine ⟨1352765468910885323884153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7214749167524721727382149 1352765468910885323884153)
                    ·
                      rfl

theorem cell22_3951752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3951752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951752 prefixEnd_3951752 := by exact prefixLift 3951752
  have htrace : WordTrace (prefixWord ++ tailWord_3951752) baseStart_3951752 baseEnd_3951752 := by
    simpa [prefixWord, tailWord_3951752, baseEnd_3951752] using wordTrace_append hprefix tailTrace_3951752
  have hstable : (prefixWord ++ tailWord_3951752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951752).length < 2 ^ (prefixWord ++ tailWord_3951752).sum := by decide
  have hdescent : baseEnd_3951752 < baseStart_3951752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951840 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_3951840 : Nat := 118140960795 + 3951840 * 2 ^ 59
def prefixEnd_3951840 : Nat := 4983230072969 + 3 ^ 40 * 3951840 * 2
def baseEnd_3951840 : Nat := 450931864369760809227961

theorem tailTrace_3951840 : CollatzResearch.WordTrace tailWord_3951840 prefixEnd_3951840 450931864369760809227961 := by
  unfold tailWord_3951840
  simp only [CollatzResearch.WordTrace]
  refine ⟨72067723001583037691970487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96090297335444050255960649 72067723001583037691970487)
  ·
    refine ⟨108101584502374556537955731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72067723001583037691970487 108101584502374556537955731)
    ·
      refine ⟨162152376753561834806933597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108101584502374556537955731 162152376753561834806933597)
      ·
        refine ⟨60807141282585688052600099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162152376753561834806933597 60807141282585688052600099)
        ·
          refine ⟨91210711923878532078900149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60807141282585688052600099 91210711923878532078900149)
          ·
            refine ⟨8551004242863612382396889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91210711923878532078900149 8551004242863612382396889)
            ·
              refine ⟨6413253182147709286797667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8551004242863612382396889 6413253182147709286797667)
              ·
                refine ⟨9619879773221563930196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413253182147709286797667 9619879773221563930196501)
                ·
                  refine ⟨450931864369760809227961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9619879773221563930196501 450931864369760809227961)
                  ·
                    rfl

theorem cell22_3951840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_3951840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951840 prefixEnd_3951840 := by exact prefixLift 3951840
  have htrace : WordTrace (prefixWord ++ tailWord_3951840) baseStart_3951840 baseEnd_3951840 := by
    simpa [prefixWord, tailWord_3951840, baseEnd_3951840] using wordTrace_append hprefix tailTrace_3951840
  have hstable : (prefixWord ++ tailWord_3951840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951840).length < 2 ^ (prefixWord ++ tailWord_3951840).sum := by decide
  have hdescent : baseEnd_3951840 < baseStart_3951840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951942 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3951942 : Nat := 118140960795 + 3951942 * 2 ^ 59
def prefixEnd_3951942 : Nat := 4983230072969 + 3 ^ 40 * 3951942 * 2
def baseEnd_3951942 : Nat := 450943503264596053877857

theorem tailTrace_3951942 : CollatzResearch.WordTrace tailWord_3951942 prefixEnd_3951942 450943503264596053877857 := by
  unfold tailWord_3951942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504348945274892087629815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96092777499197697869436053 4504348945274892087629815)
  ·
    refine ⟨6756523417912338131444723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504348945274892087629815 6756523417912338131444723)
    ·
      refine ⟨10134785126868507197167085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756523417912338131444723 10134785126868507197167085)
      ·
        refine ⟨3800544422575690198937657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10134785126868507197167085 3800544422575690198937657)
        ·
          refine ⟨2850408316931767649203243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3800544422575690198937657 2850408316931767649203243)
          ·
            refine ⟨4275612475397651473804865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850408316931767649203243 4275612475397651473804865)
            ·
              refine ⟨3206709356548238605353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275612475397651473804865 3206709356548238605353649)
              ·
                refine ⟨2405032017411178954015237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206709356548238605353649 2405032017411178954015237)
                ·
                  refine ⟨450943503264596053877857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405032017411178954015237 450943503264596053877857)
                  ·
                    rfl

theorem cell22_3951942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3951942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951942 prefixEnd_3951942 := by exact prefixLift 3951942
  have htrace : WordTrace (prefixWord ++ tailWord_3951942) baseStart_3951942 baseEnd_3951942 := by
    simpa [prefixWord, tailWord_3951942, baseEnd_3951942] using wordTrace_append hprefix tailTrace_3951942
  have hstable : (prefixWord ++ tailWord_3951942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951942).length < 2 ^ (prefixWord ++ tailWord_3951942).sum := by decide
  have hdescent : baseEnd_3951942 < baseStart_3951942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951960 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3951960 : Nat := 118140960795 + 3951960 * 2 ^ 59
def prefixEnd_3951960 : Nat := 4983230072969 + 3 ^ 40 * 3951960 * 2
def baseEnd_3951960 : Nat := 1352836671561642114683515

theorem tailTrace_3951960 : CollatzResearch.WordTrace tailWord_3951960 prefixEnd_3951960 1352836671561642114683515 := by
  unfold tailWord_3951960
  simp only [CollatzResearch.WordTrace]
  refine ⟨72069911381365667939154667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96093215175154223918872889 72069911381365667939154667)
  ·
    refine ⟨108104867072048501908732001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72069911381365667939154667 108104867072048501908732001)
    ·
      refine ⟨81078650304036376431549001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108104867072048501908732001 81078650304036376431549001)
      ·
        refine ⟨60808987728027282323661751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81078650304036376431549001 60808987728027282323661751)
        ·
          refine ⟨91213481592040923485492627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60808987728027282323661751 91213481592040923485492627)
          ·
            refine ⟨136820222388061385228238941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91213481592040923485492627 136820222388061385228238941)
            ·
              refine ⟨51307583395523019460589603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136820222388061385228238941 51307583395523019460589603)
              ·
                refine ⟨76961375093284529190884405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51307583395523019460589603 76961375093284529190884405)
                ·
                  refine ⟨7215128914995424611645413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76961375093284529190884405 7215128914995424611645413)
                  ·
                    refine ⟨1352836671561642114683515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215128914995424611645413 1352836671561642114683515)
                    ·
                      rfl

theorem cell22_3951960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3951960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951960 prefixEnd_3951960 := by exact prefixLift 3951960
  have htrace : WordTrace (prefixWord ++ tailWord_3951960) baseStart_3951960 baseEnd_3951960 := by
    simpa [prefixWord, tailWord_3951960, baseEnd_3951960] using wordTrace_append hprefix tailTrace_3951960
  have hstable : (prefixWord ++ tailWord_3951960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951960).length < 2 ^ (prefixWord ++ tailWord_3951960).sum := by decide
  have hdescent : baseEnd_3951960 < baseStart_3951960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3951998 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_3951998 : Nat := 118140960795 + 3951998 * 2 ^ 59
def prefixEnd_3951998 : Nat := 4983230072969 + 3 ^ 40 * 3951998 * 2
def baseEnd_3951998 : Nat := 450949893246074227411133

theorem tailTrace_3951998 : CollatzResearch.WordTrace tailWord_3951998 prefixEnd_3951998 450949893246074227411133 := by
  unfold tailWord_3951998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017651092074208546024081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96094139157729112245461765 18017651092074208546024081)
  ·
    refine ⟨13513238319055656409518061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017651092074208546024081 13513238319055656409518061)
    ·
      refine ⟨5067464369645871153569273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13513238319055656409518061 5067464369645871153569273)
      ·
        refine ⟨3800598277234403365176955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5067464369645871153569273 3800598277234403365176955)
        ·
          refine ⟨5700897415851605047765433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800598277234403365176955 5700897415851605047765433)
          ·
            refine ⟨4275673061888703785824075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700897415851605047765433 4275673061888703785824075)
            ·
              refine ⟨6413509592833055678736113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275673061888703785824075 6413509592833055678736113)
              ·
                refine ⟨4810132194624791759052085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413509592833055678736113 4810132194624791759052085)
                ·
                  refine ⟨450949893246074227411133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810132194624791759052085 450949893246074227411133)
                  ·
                    rfl

theorem cell22_3951998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_3951998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3951998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3951998 prefixEnd_3951998 := by exact prefixLift 3951998
  have htrace : WordTrace (prefixWord ++ tailWord_3951998) baseStart_3951998 baseEnd_3951998 := by
    simpa [prefixWord, tailWord_3951998, baseEnd_3951998] using wordTrace_append hprefix tailTrace_3951998
  have hstable : (prefixWord ++ tailWord_3951998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3951998).length < 2 ^ (prefixWord ++ tailWord_3951998).sum := by decide
  have hdescent : baseEnd_3951998 < baseStart_3951998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3951998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952035 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_3952035 : Nat := 118140960795 + 3952035 * 2 ^ 59
def prefixEnd_3952035 : Nat := 4983230072969 + 3 ^ 40 * 3952035 * 2
def baseEnd_3952035 : Nat := 1352862345594366919058285

theorem tailTrace_3952035 : CollatzResearch.WordTrace tailWord_3952035 prefixEnd_3952035 1352862345594366919058285 := by
  unfold tailWord_3952035
  simp only [CollatzResearch.WordTrace]
  refine ⟨144142558237459623687289559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96095038824973082458193039 144142558237459623687289559)
  ·
    refine ⟨216213837356189435530934339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144142558237459623687289559 216213837356189435530934339)
    ·
      refine ⟨324320756034284153296401509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216213837356189435530934339 324320756034284153296401509)
      ·
        refine ⟨60810141756428278743075283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324320756034284153296401509 60810141756428278743075283)
        ·
          refine ⟨91215212634642418114612925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60810141756428278743075283 91215212634642418114612925)
          ·
            refine ⟨34205704737990906792979847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91215212634642418114612925 34205704737990906792979847)
            ·
              refine ⟨51308557106986360189469771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34205704737990906792979847 51308557106986360189469771)
              ·
                refine ⟨76962835660479540284204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51308557106986360189469771 76962835660479540284204657)
                ·
                  refine ⟨57722126745359655213153493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76962835660479540284204657 57722126745359655213153493)
                  ·
                    refine ⟨1352862345594366919058285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57722126745359655213153493 1352862345594366919058285)
                    ·
                      rfl

theorem cell22_3952035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_3952035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952035 prefixEnd_3952035 := by exact prefixLift 3952035
  have htrace : WordTrace (prefixWord ++ tailWord_3952035) baseStart_3952035 baseEnd_3952035 := by
    simpa [prefixWord, tailWord_3952035, baseEnd_3952035] using wordTrace_append hprefix tailTrace_3952035
  have hstable : (prefixWord ++ tailWord_3952035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952035).length < 2 ^ (prefixWord ++ tailWord_3952035).sum := by decide
  have hdescent : baseEnd_3952035 < baseStart_3952035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952161 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 4]
def baseStart_3952161 : Nat := 118140960795 + 3952161 * 2 ^ 59
def prefixEnd_3952161 : Nat := 4983230072969 + 3 ^ 40 * 3952161 * 2
def baseEnd_3952161 : Nat := 450968492656448196802633

theorem tailTrace_3952161 : CollatzResearch.WordTrace tailWord_3952161 prefixEnd_3952161 450968492656448196802633 := by
  unfold tailWord_3952161
  simp only [CollatzResearch.WordTrace]
  refine ⟨144147153835003147206376337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96098102556668764804250891 144147153835003147206376337)
  ·
    refine ⟨108110365376252360404782253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144147153835003147206376337 108110365376252360404782253)
    ·
      refine ⟨40541387016094635151793345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108110365376252360404782253 40541387016094635151793345)
      ·
        refine ⟨30406040262070976363845009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40541387016094635151793345 30406040262070976363845009)
        ·
          refine ⟨22804530196553232272883757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30406040262070976363845009 22804530196553232272883757)
          ·
            refine ⟨8551698823707462102331409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22804530196553232272883757 8551698823707462102331409)
            ·
              refine ⟨6413774117780596576748557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8551698823707462102331409 6413774117780596576748557)
              ·
                refine ⟨2405165294167723716280709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6413774117780596576748557 2405165294167723716280709)
                ·
                  refine ⟨450968492656448196802633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405165294167723716280709 450968492656448196802633)
                  ·
                    rfl

theorem cell22_3952161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_3952161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952161 prefixEnd_3952161 := by exact prefixLift 3952161
  have htrace : WordTrace (prefixWord ++ tailWord_3952161) baseStart_3952161 baseEnd_3952161 := by
    simpa [prefixWord, tailWord_3952161, baseEnd_3952161] using wordTrace_append hprefix tailTrace_3952161
  have hstable : (prefixWord ++ tailWord_3952161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952161).length < 2 ^ (prefixWord ++ tailWord_3952161).sum := by decide
  have hdescent : baseEnd_3952161 < baseStart_3952161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952163 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 1, 4]
def baseStart_3952163 : Nat := 118140960795 + 3952163 * 2 ^ 59
def prefixEnd_3952163 : Nat := 4983230072969 + 3 ^ 40 * 3952163 * 2
def baseEnd_3952163 : Nat := 1352906162610217251857893

theorem tailTrace_3952163 : CollatzResearch.WordTrace tailWord_3952163 prefixEnd_3952163 1352906162610217251857893 := by
  unfold tailWord_3952163
  simp only [CollatzResearch.WordTrace]
  refine ⟨144147226780995901547949143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96098151187330601031966095 144147226780995901547949143)
  ·
    refine ⟨216220840171493852321923715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144147226780995901547949143 216220840171493852321923715)
    ·
      refine ⟨324331260257240778482885573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216220840171493852321923715 324331260257240778482885573)
      ·
        refine ⟨60812111298232645965541045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324331260257240778482885573 60812111298232645965541045)
        ·
          refine ⟨5701135434209310559269473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60812111298232645965541045 5701135434209310559269473)
          ·
            refine ⟨4275851575656982919452105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5701135434209310559269473 4275851575656982919452105)
            ·
              refine ⟨3206888681742737189589079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4275851575656982919452105 3206888681742737189589079)
              ·
                refine ⟨4810333022614105784383619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206888681742737189589079 4810333022614105784383619)
                ·
                  refine ⟨7215499533921158676575429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810333022614105784383619 7215499533921158676575429)
                  ·
                    refine ⟨1352906162610217251857893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215499533921158676575429 1352906162610217251857893)
                    ·
                      rfl

theorem cell22_3952163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 1, 4].length) (baseStart_3952163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952163 prefixEnd_3952163 := by exact prefixLift 3952163
  have htrace : WordTrace (prefixWord ++ tailWord_3952163) baseStart_3952163 baseEnd_3952163 := by
    simpa [prefixWord, tailWord_3952163, baseEnd_3952163] using wordTrace_append hprefix tailTrace_3952163
  have hstable : (prefixWord ++ tailWord_3952163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952163).length < 2 ^ (prefixWord ++ tailWord_3952163).sum := by decide
  have hdescent : baseEnd_3952163 < baseStart_3952163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952193 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3952193 : Nat := 118140960795 + 3952193 * 2 ^ 59
def prefixEnd_3952193 : Nat := 4983230072969 + 3 ^ 40 * 3952193 * 2
def baseEnd_3952193 : Nat := 1352916432223307173607801

theorem tailTrace_3952193 : CollatzResearch.WordTrace tailWord_3952193 prefixEnd_3952193 1352916432223307173607801 := by
  unfold tailWord_3952193
  simp only [CollatzResearch.WordTrace]
  refine ⟨144148320970887216671541233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96098880647258144447694155 144148320970887216671541233)
  ·
    refine ⟨108111240728165412503655925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144148320970887216671541233 108111240728165412503655925)
    ·
      refine ⟨10135428818265507422217743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108111240728165412503655925 10135428818265507422217743)
      ·
        refine ⟨15203143227398261133326615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135428818265507422217743 15203143227398261133326615)
        ·
          refine ⟨22804714841097391699989923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203143227398261133326615 22804714841097391699989923)
          ·
            refine ⟨34207072261646087549984885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22804714841097391699989923 34207072261646087549984885)
            ·
              refine ⟨3206913024529320707811083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34207072261646087549984885 3206913024529320707811083)
              ·
                refine ⟨4810369536793981061716625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206913024529320707811083 4810369536793981061716625)
                ·
                  refine ⟨3607777152595485796287469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810369536793981061716625 3607777152595485796287469)
                  ·
                    refine ⟨1352916432223307173607801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607777152595485796287469 1352916432223307173607801)
                    ·
                      rfl

theorem cell22_3952193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3952193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952193 prefixEnd_3952193 := by exact prefixLift 3952193
  have htrace : WordTrace (prefixWord ++ tailWord_3952193) baseStart_3952193 baseEnd_3952193 := by
    simpa [prefixWord, tailWord_3952193, baseEnd_3952193] using wordTrace_append hprefix tailTrace_3952193
  have hstable : (prefixWord ++ tailWord_3952193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952193).length < 2 ^ (prefixWord ++ tailWord_3952193).sum := by decide
  have hdescent : baseEnd_3952193 < baseStart_3952193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952234 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3952234 : Nat := 118140960795 + 3952234 * 2 ^ 59
def prefixEnd_3952234 : Nat := 4983230072969 + 3 ^ 40 * 3952234 * 2
def baseEnd_3952234 : Nat := 450976822453732244444225

theorem tailTrace_3952234 : CollatzResearch.WordTrace tailWord_3952234 prefixEnd_3952234 450976822453732244444225 := by
  unfold tailWord_3952234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36037454090934670168445939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96099877575825787115855837 36037454090934670168445939)
  ·
    refine ⟨54056181136402005252668909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36037454090934670168445939 54056181136402005252668909)
    ·
      refine ⟨20271067926150751969750841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54056181136402005252668909 20271067926150751969750841)
      ·
        refine ⟨15203300944613063977313131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20271067926150751969750841 15203300944613063977313131)
        ·
          refine ⟨22804951416919595965969697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203300944613063977313131 22804951416919595965969697)
          ·
            refine ⟨17103713562689696974477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22804951416919595965969697 17103713562689696974477273)
            ·
              refine ⟨12827785172017272730857955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17103713562689696974477273 12827785172017272730857955)
              ·
                refine ⟨19241677758025909096286933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12827785172017272730857955 19241677758025909096286933)
                ·
                  refine ⟨450976822453732244444225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19241677758025909096286933 450976822453732244444225)
                  ·
                    rfl

theorem cell22_3952234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3952234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952234 prefixEnd_3952234 := by exact prefixLift 3952234
  have htrace : WordTrace (prefixWord ++ tailWord_3952234) baseStart_3952234 baseEnd_3952234 := by
    simpa [prefixWord, tailWord_3952234, baseEnd_3952234] using wordTrace_append hprefix tailTrace_3952234
  have hstable : (prefixWord ++ tailWord_3952234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952234).length < 2 ^ (prefixWord ++ tailWord_3952234).sum := by decide
  have hdescent : baseEnd_3952234 < baseStart_3952234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952247 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 8]
def baseStart_3952247 : Nat := 118140960795 + 3952247 * 2 ^ 59
def prefixEnd_3952247 : Nat := 4983230072969 + 3 ^ 40 * 3952247 * 2
def baseEnd_3952247 : Nat := 1352934917526869032757635

theorem tailTrace_3952247 : CollatzResearch.WordTrace tailWord_3952247 prefixEnd_3952247 1352934917526869032757635 := by
  unfold tailWord_3952247
  simp only [CollatzResearch.WordTrace]
  refine ⟨144150290512691583894006995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96100193675127722596004663 144150290512691583894006995)
  ·
    refine ⟨216225435769037375841010493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144150290512691583894006995 216225435769037375841010493)
    ·
      refine ⟨81084538413389015940378935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216225435769037375841010493 81084538413389015940378935)
      ·
        refine ⟨121626807620083523910568403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81084538413389015940378935 121626807620083523910568403)
        ·
          refine ⟨182440211430125285865852605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121626807620083523910568403 182440211430125285865852605)
          ·
            refine ⟨68415079286296982199694727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182440211430125285865852605 68415079286296982199694727)
            ·
              refine ⟨102622618929445473299542091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68415079286296982199694727 102622618929445473299542091)
              ·
                refine ⟨153933928394168209949313137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102622618929445473299542091 153933928394168209949313137)
                ·
                  refine ⟨115450446295626157461984853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153933928394168209949313137 115450446295626157461984853)
                  ·
                    refine ⟨1352934917526869032757635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115450446295626157461984853 1352934917526869032757635)
                    ·
                      rfl

theorem cell22_3952247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_3952247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952247 prefixEnd_3952247 := by exact prefixLift 3952247
  have htrace : WordTrace (prefixWord ++ tailWord_3952247) baseStart_3952247 baseEnd_3952247 := by
    simpa [prefixWord, tailWord_3952247, baseEnd_3952247] using wordTrace_append hprefix tailTrace_3952247
  have hstable : (prefixWord ++ tailWord_3952247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952247).length < 2 ^ (prefixWord ++ tailWord_3952247).sum := by decide
  have hdescent : baseEnd_3952247 < baseStart_3952247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952311 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_3952311 : Nat := 118140960795 + 3952311 * 2 ^ 59
def prefixEnd_3952311 : Nat := 4983230072969 + 3 ^ 40 * 3952311 * 2
def baseEnd_3952311 : Nat := 1352956826034794199157439

theorem tailTrace_3952311 : CollatzResearch.WordTrace tailWord_3952311 prefixEnd_3952311 1352956826034794199157439 := by
  unfold tailWord_3952311
  simp only [CollatzResearch.WordTrace]
  refine ⟨144152624784459722824336787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96101749856306481882891191 144152624784459722824336787)
  ·
    refine ⟨216228937176689584236505181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144152624784459722824336787 216228937176689584236505181)
    ·
      refine ⟨81085851441258594088689443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216228937176689584236505181 81085851441258594088689443)
      ·
        refine ⟨121628777161887891133034165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81085851441258594088689443 121628777161887891133034165)
        ·
          refine ⟨11402697858926989793721953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121628777161887891133034165 11402697858926989793721953)
          ·
            refine ⟨8552023394195242345291465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11402697858926989793721953 8552023394195242345291465)
            ·
              refine ⟨6414017545646431758968599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8552023394195242345291465 6414017545646431758968599)
              ·
                refine ⟨9621026318469647638452899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414017545646431758968599 9621026318469647638452899)
                ·
                  refine ⟨14431539477704471457679349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9621026318469647638452899 14431539477704471457679349)
                  ·
                    refine ⟨1352956826034794199157439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14431539477704471457679349 1352956826034794199157439)
                    ·
                      rfl

theorem cell22_3952311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_3952311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952311 prefixEnd_3952311 := by exact prefixLift 3952311
  have htrace : WordTrace (prefixWord ++ tailWord_3952311) baseStart_3952311 baseEnd_3952311 := by
    simpa [prefixWord, tailWord_3952311, baseEnd_3952311] using wordTrace_append hprefix tailTrace_3952311
  have hstable : (prefixWord ++ tailWord_3952311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952311).length < 2 ^ (prefixWord ++ tailWord_3952311).sum := by decide
  have hdescent : baseEnd_3952311 < baseStart_3952311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952332 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_3952332 : Nat := 118140960795 + 3952332 * 2 ^ 59
def prefixEnd_3952332 : Nat := 4983230072969 + 3 ^ 40 * 3952332 * 2
def baseEnd_3952332 : Nat := 1352964014763957144382375

theorem tailTrace_3952332 : CollatzResearch.WordTrace tailWord_3952332 prefixEnd_3952332 1352964014763957144382375 := by
  unfold tailWord_3952332
  simp only [CollatzResearch.WordTrace]
  refine ⟨72076695358691821705425625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96102260478255762273900833 72076695358691821705425625)
  ·
    refine ⟨54057521519018866279069219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72076695358691821705425625 54057521519018866279069219)
    ·
      refine ⟨81086282278528299418603829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54057521519018866279069219 81086282278528299418603829)
      ·
        refine ⟨7601838963612028070494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81086282278528299418603829 7601838963612028070494109)
        ·
          refine ⟨2850689611354510526435291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7601838963612028070494109 2850689611354510526435291)
          ·
            refine ⟨4276034417031765789652937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850689611354510526435291 4276034417031765789652937)
            ·
              refine ⟨3207025812773824342239703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276034417031765789652937 3207025812773824342239703)
              ·
                refine ⟨4810538719160736513359555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207025812773824342239703 4810538719160736513359555)
                ·
                  refine ⟨7215808078741104770039333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810538719160736513359555 7215808078741104770039333)
                  ·
                    refine ⟨1352964014763957144382375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215808078741104770039333 1352964014763957144382375)
                    ·
                      rfl

theorem cell22_3952332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_3952332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952332 prefixEnd_3952332 := by exact prefixLift 3952332
  have htrace : WordTrace (prefixWord ++ tailWord_3952332) baseStart_3952332 baseEnd_3952332 := by
    simpa [prefixWord, tailWord_3952332, baseEnd_3952332] using wordTrace_append hprefix tailTrace_3952332
  have hstable : (prefixWord ++ tailWord_3952332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952332).length < 2 ^ (prefixWord ++ tailWord_3952332).sum := by decide
  have hdescent : baseEnd_3952332 < baseStart_3952332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952386 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3952386 : Nat := 118140960795 + 3952386 * 2 ^ 59
def prefixEnd_3952386 : Nat := 4983230072969 + 3 ^ 40 * 3952386 * 2
def baseEnd_3952386 : Nat := 450994166689173001177403

theorem tailTrace_3952386 : CollatzResearch.WordTrace tailWord_3952386 prefixEnd_3952386 450994166689173001177403 := by
  unfold tailWord_3952386
  simp only [CollatzResearch.WordTrace]
  refine ⟨36038840064797002658329253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96103573506125340422211341 36038840064797002658329253)
  ·
    refine ⟨6757282512149437998436735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36038840064797002658329253 6757282512149437998436735)
    ·
      refine ⟨10135923768224156997655103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6757282512149437998436735 10135923768224156997655103)
      ·
        refine ⟨15203885652336235496482655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135923768224156997655103 15203885652336235496482655)
        ·
          refine ⟨22805828478504353244723983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203885652336235496482655 22805828478504353244723983)
          ·
            refine ⟨34208742717756529867085975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22805828478504353244723983 34208742717756529867085975)
            ·
              refine ⟨51313114076634794800628963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34208742717756529867085975 51313114076634794800628963)
              ·
                refine ⟨76969671114952192200943445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51313114076634794800628963 76969671114952192200943445)
                ·
                  refine ⟨450994166689173001177403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76969671114952192200943445 450994166689173001177403)
                  ·
                    rfl

theorem cell22_3952386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3952386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952386 prefixEnd_3952386 := by exact prefixLift 3952386
  have htrace : WordTrace (prefixWord ++ tailWord_3952386) baseStart_3952386 baseEnd_3952386 := by
    simpa [prefixWord, tailWord_3952386, baseEnd_3952386] using wordTrace_append hprefix tailTrace_3952386
  have hstable : (prefixWord ++ tailWord_3952386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952386).length < 2 ^ (prefixWord ++ tailWord_3952386).sum := by decide
  have hdescent : baseEnd_3952386 < baseStart_3952386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952407 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 1, 3]
def baseStart_3952407 : Nat := 118140960795 + 3952407 * 2 ^ 59
def prefixEnd_3952407 : Nat := 4983230072969 + 3 ^ 40 * 3952407 * 2
def baseEnd_3952407 : Nat := 1352989688796681948757145

theorem tailTrace_3952407 : CollatzResearch.WordTrace tailWord_3952407 prefixEnd_3952407 1352989688796681948757145 := by
  unfold tailWord_3952407
  simp only [CollatzResearch.WordTrace]
  refine ⟨144156126192111931219831475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96104084128074620813220983 144156126192111931219831475)
  ·
    refine ⟨216234189288167896829747213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144156126192111931219831475 216234189288167896829747213)
    ·
      refine ⟨81087820983062961311155205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216234189288167896829747213 81087820983062961311155205)
      ·
        refine ⟨15203966434324305245841601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81087820983062961311155205 15203966434324305245841601)
        ·
          refine ⟨11402974825743228934381201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15203966434324305245841601 11402974825743228934381201)
          ·
            refine ⟨8552231119307421700785901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11402974825743228934381201 8552231119307421700785901)
            ·
              refine ⟨3207086669740283137794713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8552231119307421700785901 3207086669740283137794713)
              ·
                refine ⟨2405315002305212353346035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207086669740283137794713 2405315002305212353346035)
                ·
                  refine ⟨3607972503457818530019053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405315002305212353346035 3607972503457818530019053)
                  ·
                    refine ⟨1352989688796681948757145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607972503457818530019053 1352989688796681948757145)
                    ·
                      rfl

theorem cell22_3952407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_3952407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952407 prefixEnd_3952407 := by exact prefixLift 3952407
  have htrace : WordTrace (prefixWord ++ tailWord_3952407) baseStart_3952407 baseEnd_3952407 := by
    simpa [prefixWord, tailWord_3952407, baseEnd_3952407] using wordTrace_append hprefix tailTrace_3952407
  have hstable : (prefixWord ++ tailWord_3952407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952407).length < 2 ^ (prefixWord ++ tailWord_3952407).sum := by decide
  have hdescent : baseEnd_3952407 < baseStart_3952407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952416 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_3952416 : Nat := 118140960795 + 3952416 * 2 ^ 59
def prefixEnd_3952416 : Nat := 4983230072969 + 3 ^ 40 * 3952416 * 2
def baseEnd_3952416 : Nat := 1352992769680608925282117

theorem tailTrace_3952416 : CollatzResearch.WordTrace tailWord_3952416 prefixEnd_3952416 1352992769680608925282117 := by
  unfold tailWord_3952416
  simp only [CollatzResearch.WordTrace]
  refine ⟨72078227224539662878454551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96104302966052883837939401 72078227224539662878454551)
  ·
    refine ⟨108117340836809494317681827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72078227224539662878454551 108117340836809494317681827)
    ·
      refine ⟨162176011255214241476522741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108117340836809494317681827 162176011255214241476522741)
      ·
        refine ⟨15204001055176335138424007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162176011255214241476522741 15204001055176335138424007)
        ·
          refine ⟨22806001582764502707636011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15204001055176335138424007 22806001582764502707636011)
          ·
            refine ⟨34209002374146754061454017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806001582764502707636011 34209002374146754061454017)
            ·
              refine ⟨25656751780610065546090513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34209002374146754061454017 25656751780610065546090513)
              ·
                refine ⟨19242563835457549159567885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25656751780610065546090513 19242563835457549159567885)
                ·
                  refine ⟨7215961438296580934837957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19242563835457549159567885 7215961438296580934837957)
                  ·
                    refine ⟨1352992769680608925282117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215961438296580934837957 1352992769680608925282117)
                    ·
                      rfl

theorem cell22_3952416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_3952416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952416 prefixEnd_3952416 := by exact prefixLift 3952416
  have htrace : WordTrace (prefixWord ++ tailWord_3952416) baseStart_3952416 baseEnd_3952416 := by
    simpa [prefixWord, tailWord_3952416, baseEnd_3952416] using wordTrace_append hprefix tailTrace_3952416
  have hstable : (prefixWord ++ tailWord_3952416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952416).length < 2 ^ (prefixWord ++ tailWord_3952416).sum := by decide
  have hdescent : baseEnd_3952416 < baseStart_3952416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952420 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_3952420 : Nat := 118140960795 + 3952420 * 2 ^ 59
def prefixEnd_3952420 : Nat := 4983230072969 + 3 ^ 40 * 3952420 * 2
def baseEnd_3952420 : Nat := 450998046320784749394035

theorem tailTrace_3952420 : CollatzResearch.WordTrace tailWord_3952420 prefixEnd_3952420 450998046320784749394035 := by
  unfold tailWord_3952420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72078300170532417220027357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96104400227376556293369809 72078300170532417220027357)
  ·
    refine ⟨27029362563949656457510259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72078300170532417220027357 27029362563949656457510259)
    ·
      refine ⟨40544043845924484686265389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27029362563949656457510259 40544043845924484686265389)
      ·
        refine ⟨15204016442221681757349521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40544043845924484686265389 15204016442221681757349521)
        ·
          refine ⟨11403012331666261318012141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15204016442221681757349521 11403012331666261318012141)
          ·
            refine ⟨4276129624374847994254553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11403012331666261318012141 4276129624374847994254553)
            ·
              refine ⟨3207097218281135995690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4276129624374847994254553 3207097218281135995690915)
              ·
                refine ⟨4810645827421703993536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207097218281135995690915 4810645827421703993536373)
                ·
                  refine ⟨450998046320784749394035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810645827421703993536373 450998046320784749394035)
                  ·
                    rfl

theorem cell22_3952420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_3952420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952420 prefixEnd_3952420 := by exact prefixLift 3952420
  have htrace : WordTrace (prefixWord ++ tailWord_3952420) baseStart_3952420 baseEnd_3952420 := by
    simpa [prefixWord, tailWord_3952420, baseEnd_3952420] using wordTrace_append hprefix tailTrace_3952420
  have hstable : (prefixWord ++ tailWord_3952420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952420).length < 2 ^ (prefixWord ++ tailWord_3952420).sum := by decide
  have hdescent : baseEnd_3952420 < baseStart_3952420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952433 : List Nat := [1, 2, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_3952433 : Nat := 118140960795 + 3952433 * 2 ^ 59
def prefixEnd_3952433 : Nat := 4983230072969 + 3 ^ 40 * 3952433 * 2
def baseEnd_3952433 : Nat := 1352998589128026547607065

theorem tailTrace_3952433 : CollatzResearch.WordTrace tailWord_3952433 prefixEnd_3952433 1352998589128026547607065 := by
  unfold tailWord_3952433
  simp only [CollatzResearch.WordTrace]
  refine ⟨144157074490017737660277953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96104716326678491773518635 144157074490017737660277953)
  ·
    refine ⟨108117805867513303245208465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144157074490017737660277953 108117805867513303245208465)
    ·
      refine ⟨81088354400634977433906349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108117805867513303245208465 81088354400634977433906349)
      ·
        refine ⟨30408132900238116537714881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81088354400634977433906349 30408132900238116537714881)
        ·
          refine ⟨22806099675178587403286161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30408132900238116537714881 22806099675178587403286161)
          ·
            refine ⟨17104574756383940552464621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22806099675178587403286161 17104574756383940552464621)
            ·
              refine ⟨6414215533643977707174233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17104574756383940552464621 6414215533643977707174233)
              ·
                refine ⟨4810661650232983280380675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414215533643977707174233 4810661650232983280380675)
                ·
                  refine ⟨7215992475349474920571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810661650232983280380675 7215992475349474920571013)
                  ·
                    refine ⟨1352998589128026547607065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215992475349474920571013 1352998589128026547607065)
                    ·
                      rfl

theorem cell22_3952433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_3952433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952433 prefixEnd_3952433 := by exact prefixLift 3952433
  have htrace : WordTrace (prefixWord ++ tailWord_3952433) baseStart_3952433 baseEnd_3952433 := by
    simpa [prefixWord, tailWord_3952433, baseEnd_3952433] using wordTrace_append hprefix tailTrace_3952433
  have hstable : (prefixWord ++ tailWord_3952433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952433).length < 2 ^ (prefixWord ++ tailWord_3952433).sum := by decide
  have hdescent : baseEnd_3952433 < baseStart_3952433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952465 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 4]
def baseStart_3952465 : Nat := 118140960795 + 3952465 * 2 ^ 59
def prefixEnd_3952465 : Nat := 4983230072969 + 3 ^ 40 * 3952465 * 2
def baseEnd_3952465 : Nat := 451003181127329710268989

theorem tailTrace_3952465 : CollatzResearch.WordTrace tailWord_3952465 prefixEnd_3952465 451003181127329710268989 := by
  unfold tailWord_3952465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144158241625901807125442849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96105494417267871416961899 144158241625901807125442849)
  ·
    refine ⟨108118681219426355344082137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144158241625901807125442849 108118681219426355344082137)
    ·
      refine ⟨81089010914569766508061603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108118681219426355344082137 81089010914569766508061603)
      ·
        refine ⟨121633516371854649762092405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81089010914569766508061603 121633516371854649762092405)
        ·
          refine ⟨11403142159861373415196163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121633516371854649762092405 11403142159861373415196163)
          ·
            refine ⟨17104713239792060122794245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11403142159861373415196163 17104713239792060122794245)
            ·
              refine ⟨3207133732461011273023921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17104713239792060122794245 3207133732461011273023921)
              ·
                refine ⟨2405350299345758454767941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207133732461011273023921 2405350299345758454767941)
                ·
                  refine ⟨451003181127329710268989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405350299345758454767941 451003181127329710268989)
                  ·
                    rfl

theorem cell22_3952465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_3952465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952465 prefixEnd_3952465 := by exact prefixLift 3952465
  have htrace : WordTrace (prefixWord ++ tailWord_3952465) baseStart_3952465 baseEnd_3952465 := by
    simpa [prefixWord, tailWord_3952465, baseEnd_3952465] using wordTrace_append hprefix tailTrace_3952465
  have hstable : (prefixWord ++ tailWord_3952465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952465).length < 2 ^ (prefixWord ++ tailWord_3952465).sum := by decide
  have hdescent : baseEnd_3952465 < baseStart_3952465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952521 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 7]
def baseStart_3952521 : Nat := 118140960795 + 3952521 * 2 ^ 59
def prefixEnd_3952521 : Nat := 4983230072969 + 3 ^ 40 * 3952521 * 2
def baseEnd_3952521 : Nat := 451009571108807883802265

theorem tailTrace_3952521 : CollatzResearch.WordTrace tailWord_3952521 prefixEnd_3952521 451009571108807883802265 := by
  unfold tailWord_3952521
  simp only [CollatzResearch.WordTrace]
  refine ⟨144160284113698928689481417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96106856075799285792987611 144160284113698928689481417)
  ·
    refine ⟨108120213085274196517111063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144160284113698928689481417 108120213085274196517111063)
    ·
      refine ⟨162180319627911294775666595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108120213085274196517111063 162180319627911294775666595)
      ·
        refine ⟨243270479441866942163499893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162180319627911294775666595 243270479441866942163499893)
        ·
          refine ⟨22806607447675025827828115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243270479441866942163499893 22806607447675025827828115)
          ·
            refine ⟨34209911171512538741742173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22806607447675025827828115 34209911171512538741742173)
            ·
              refine ⟨12828716689317202028153315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34209911171512538741742173 12828716689317202028153315)
              ·
                refine ⟨19243075033975803042229973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12828716689317202028153315 19243075033975803042229973)
                ·
                  refine ⟨451009571108807883802265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19243075033975803042229973 451009571108807883802265)
                  ·
                    rfl

theorem cell22_3952521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_3952521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952521 prefixEnd_3952521 := by exact prefixLift 3952521
  have htrace : WordTrace (prefixWord ++ tailWord_3952521) baseStart_3952521 baseEnd_3952521 := by
    simpa [prefixWord, tailWord_3952521, baseEnd_3952521] using wordTrace_append hprefix tailTrace_3952521
  have hstable : (prefixWord ++ tailWord_3952521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952521).length < 2 ^ (prefixWord ++ tailWord_3952521).sum := by decide
  have hdescent : baseEnd_3952521 < baseStart_3952521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952568 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_3952568 : Nat := 118140960795 + 3952568 * 2 ^ 59
def prefixEnd_3952568 : Nat := 4983230072969 + 3 ^ 40 * 3952568 * 2
def baseEnd_3952568 : Nat := 1353044802386931195481651

theorem tailTrace_3952568 : CollatzResearch.WordTrace tailWord_3952568 prefixEnd_3952568 1353044802386931195481651 := by
  unfold tailWord_3952568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72080999172264327858221179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96107998896352437144294905 72080999172264327858221179)
  ·
    refine ⟨108121498758396491787331769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72080999172264327858221179 108121498758396491787331769)
    ·
      refine ⟨81091124068797368840498827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108121498758396491787331769 81091124068797368840498827)
      ·
        refine ⟨121636686103196053260748241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81091124068797368840498827 121636686103196053260748241)
        ·
          refine ⟨91227514577397039945561181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121636686103196053260748241 91227514577397039945561181)
          ·
            refine ⟨34210317966523889979585443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91227514577397039945561181 34210317966523889979585443)
            ·
              refine ⟨51315476949785834969378165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34210317966523889979585443 51315476949785834969378165)
              ·
                refine ⟨4810825964042422028379203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51315476949785834969378165 4810825964042422028379203)
                ·
                  refine ⟨7216238946063633042568805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810825964042422028379203 7216238946063633042568805)
                  ·
                    refine ⟨1353044802386931195481651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216238946063633042568805 1353044802386931195481651)
                    ·
                      rfl

theorem cell22_3952568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_3952568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952568 prefixEnd_3952568 := by exact prefixLift 3952568
  have htrace : WordTrace (prefixWord ++ tailWord_3952568) baseStart_3952568 baseEnd_3952568 := by
    simpa [prefixWord, tailWord_3952568, baseEnd_3952568] using wordTrace_append hprefix tailTrace_3952568
  have hstable : (prefixWord ++ tailWord_3952568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952568).length < 2 ^ (prefixWord ++ tailWord_3952568).sum := by decide
  have hdescent : baseEnd_3952568 < baseStart_3952568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952581 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3952581 : Nat := 118140960795 + 3952581 * 2 ^ 59
def prefixEnd_3952581 : Nat := 4983230072969 + 3 ^ 40 * 3952581 * 2
def baseEnd_3952581 : Nat := 1353049252552603494906611

theorem tailTrace_3952581 : CollatzResearch.WordTrace tailWord_3952581 prefixEnd_3952581 1353049252552603494906611 := by
  unfold tailWord_3952581
  simp only [CollatzResearch.WordTrace]
  refine ⟨144162472493481558936665597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96108314995654372624443731 144162472493481558936665597)
  ·
    refine ⟨54060927185055584601249599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144162472493481558936665597 54060927185055584601249599)
    ·
      refine ⟨81091390777583376901874399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54060927185055584601249599 81091390777583376901874399)
      ·
        refine ⟨121637086166375065352811599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81091390777583376901874399 121637086166375065352811599)
        ·
          refine ⟨182455629249562598029217399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121637086166375065352811599 182455629249562598029217399)
          ·
            refine ⟨273683443874343897043826099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182455629249562598029217399 273683443874343897043826099)
            ·
              refine ⟨410525165811515845565739149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273683443874343897043826099 410525165811515845565739149)
              ·
                refine ⟨153946937179318442087152181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 410525165811515845565739149 153946937179318442087152181)
                ·
                  refine ⟨14432525360561103945670517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153946937179318442087152181 14432525360561103945670517)
                  ·
                    refine ⟨1353049252552603494906611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14432525360561103945670517 1353049252552603494906611)
                    ·
                      rfl

theorem cell22_3952581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3952581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952581 prefixEnd_3952581 := by exact prefixLift 3952581
  have htrace : WordTrace (prefixWord ++ tailWord_3952581) baseStart_3952581 baseEnd_3952581 := by
    simpa [prefixWord, tailWord_3952581, baseEnd_3952581] using wordTrace_append hprefix tailTrace_3952581
  have hstable : (prefixWord ++ tailWord_3952581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952581).length < 2 ^ (prefixWord ++ tailWord_3952581).sum := by decide
  have hdescent : baseEnd_3952581 < baseStart_3952581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952602 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_3952602 : Nat := 118140960795 + 3952602 * 2 ^ 59
def prefixEnd_3952602 : Nat := 4983230072969 + 3 ^ 40 * 3952602 * 2
def baseEnd_3952602 : Nat := 1353056441281766440131547

theorem tailTrace_3952602 : CollatzResearch.WordTrace tailWord_3952602 prefixEnd_3952602 1353056441281766440131547 := by
  unfold tailWord_3952602
  simp only [CollatzResearch.WordTrace]
  refine ⟨36040809606601369880795015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96108825617603653015453373 36040809606601369880795015)
  ·
    refine ⟨54061214409902054821192523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36040809606601369880795015 54061214409902054821192523)
    ·
      refine ⟨81091821614853082231788785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54061214409902054821192523 81091821614853082231788785)
      ·
        refine ⟨60818866211139811673841589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81091821614853082231788785 60818866211139811673841589)
        ·
          refine ⟨5701768707294357344422649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60818866211139811673841589 5701768707294357344422649)
          ·
            refine ⟨4276326530470768008316987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5701768707294357344422649 4276326530470768008316987)
            ·
              refine ⟨6414489795706152012475481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276326530470768008316987 6414489795706152012475481)
              ·
                refine ⟨4810867346779614009356611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414489795706152012475481 4810867346779614009356611)
                ·
                  refine ⟨7216301020169421014034917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810867346779614009356611 7216301020169421014034917)
                  ·
                    refine ⟨1353056441281766440131547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216301020169421014034917 1353056441281766440131547)
                    ·
                      rfl

theorem cell22_3952602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_3952602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952602 prefixEnd_3952602 := by exact prefixLift 3952602
  have htrace : WordTrace (prefixWord ++ tailWord_3952602) baseStart_3952602 baseEnd_3952602 := by
    simpa [prefixWord, tailWord_3952602, baseEnd_3952602] using wordTrace_append hprefix tailTrace_3952602
  have hstable : (prefixWord ++ tailWord_3952602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952602).length < 2 ^ (prefixWord ++ tailWord_3952602).sum := by decide
  have hdescent : baseEnd_3952602 < baseStart_3952602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952615 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3952615 : Nat := 118140960795 + 3952615 * 2 ^ 59
def prefixEnd_3952615 : Nat := 4983230072969 + 3 ^ 40 * 3952615 * 2
def baseEnd_3952615 : Nat := 1353060891447438739556507

theorem tailTrace_3952615 : CollatzResearch.WordTrace tailWord_3952615 prefixEnd_3952615 1353060891447438739556507 := by
  unfold tailWord_3952615
  simp only [CollatzResearch.WordTrace]
  refine ⟨144163712575358382743403299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96109141716905588495602199 144163712575358382743403299)
  ·
    refine ⟨216245568863037574115104949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144163712575358382743403299 216245568863037574115104949)
    ·
      refine ⟨20273022080909772573291089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216245568863037574115104949 20273022080909772573291089)
      ·
        refine ⟨15204766560682329429968317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20273022080909772573291089 15204766560682329429968317)
        ·
          refine ⟨5701787460255873536238119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15204766560682329429968317 5701787460255873536238119)
          ·
            refine ⟨8552681190383810304357179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701787460255873536238119 8552681190383810304357179)
            ·
              refine ⟨12829021785575715456535769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552681190383810304357179 12829021785575715456535769)
              ·
                refine ⟨9621766339181786592401827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12829021785575715456535769 9621766339181786592401827)
                ·
                  refine ⟨14432649508772679888602741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9621766339181786592401827 14432649508772679888602741)
                  ·
                    refine ⟨1353060891447438739556507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14432649508772679888602741 1353060891447438739556507)
                    ·
                      rfl

theorem cell22_3952615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3952615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952615 prefixEnd_3952615 := by exact prefixLift 3952615
  have htrace : WordTrace (prefixWord ++ tailWord_3952615) baseStart_3952615 baseEnd_3952615 := by
    simpa [prefixWord, tailWord_3952615, baseEnd_3952615] using wordTrace_append hprefix tailTrace_3952615
  have hstable : (prefixWord ++ tailWord_3952615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952615).length < 2 ^ (prefixWord ++ tailWord_3952615).sum := by decide
  have hdescent : baseEnd_3952615 < baseStart_3952615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952643 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 7, 3]
def baseStart_3952643 : Nat := 118140960795 + 3952643 * 2 ^ 59
def prefixEnd_3952643 : Nat := 4983230072969 + 3 ^ 40 * 3952643 * 2
def baseEnd_3952643 : Nat := 1353070476419655999856421

theorem tailTrace_3952643 : CollatzResearch.WordTrace tailWord_3952643 prefixEnd_3952643 1353070476419655999856421 := by
  unfold tailWord_3952643
  simp only [CollatzResearch.WordTrace]
  refine ⟨144164733819256943525422583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96109822546171295683615055 144164733819256943525422583)
  ·
    refine ⟨216247100728885415288133875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144164733819256943525422583 216247100728885415288133875)
    ·
      refine ⟨324370651093328122932200813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216247100728885415288133875 324370651093328122932200813)
      ·
        refine ⟨121638994159998046099575305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324370651093328122932200813 121638994159998046099575305)
        ·
          refine ⟨91229245619998534574681479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121638994159998046099575305 91229245619998534574681479)
          ·
            refine ⟨136843868429997801862022219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91229245619998534574681479 136843868429997801862022219)
            ·
              refine ⟨205265802644996702793033329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136843868429997801862022219 205265802644996702793033329)
              ·
                refine ⟨153949351983747527094774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205265802644996702793033329 153949351983747527094774997)
                ·
                  refine ⟨3608187937119082666283789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 153949351983747527094774997 3608187937119082666283789)
                  ·
                    refine ⟨1353070476419655999856421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608187937119082666283789 1353070476419655999856421)
                    ·
                      rfl

theorem cell22_3952643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 3].length) (baseStart_3952643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952643 prefixEnd_3952643 := by exact prefixLift 3952643
  have htrace : WordTrace (prefixWord ++ tailWord_3952643) baseStart_3952643 baseEnd_3952643 := by
    simpa [prefixWord, tailWord_3952643, baseEnd_3952643] using wordTrace_append hprefix tailTrace_3952643
  have hstable : (prefixWord ++ tailWord_3952643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952643).length < 2 ^ (prefixWord ++ tailWord_3952643).sum := by decide
  have hdescent : baseEnd_3952643 < baseStart_3952643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952677 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_3952677 : Nat := 118140960795 + 3952677 * 2 ^ 59
def prefixEnd_3952677 : Nat := 4983230072969 + 3 ^ 40 * 3952677 * 2
def baseEnd_3952677 : Nat := 1353082115314491244506317

theorem tailTrace_3952677 : CollatzResearch.WordTrace tailWord_3952677 prefixEnd_3952677 1353082115314491244506317 := by
  unfold tailWord_3952677
  simp only [CollatzResearch.WordTrace]
  refine ⟨144165973901133767332160285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96110649267422511554773523 144165973901133767332160285)
  ·
    refine ⟨54062240212925162749560107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144165973901133767332160285 54062240212925162749560107)
    ·
      refine ⟨81093360319387744124340161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54062240212925162749560107 81093360319387744124340161)
      ·
        refine ⟨60820020239540808093255121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81093360319387744124340161 60820020239540808093255121)
        ·
          refine ⟨45615015179655606069941341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60820020239540808093255121 45615015179655606069941341)
          ·
            refine ⟨17105630692370852276228003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45615015179655606069941341 17105630692370852276228003)
            ·
              refine ⟨25658446038556278414342005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17105630692370852276228003 25658446038556278414342005)
              ·
                refine ⟨2405479316114651101344563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25658446038556278414342005 2405479316114651101344563)
                ·
                  refine ⟨3608218974171976652016845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405479316114651101344563 3608218974171976652016845)
                  ·
                    refine ⟨1353082115314491244506317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608218974171976652016845 1353082115314491244506317)
                    ·
                      rfl

theorem cell22_3952677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_3952677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952677 prefixEnd_3952677 := by exact prefixLift 3952677
  have htrace : WordTrace (prefixWord ++ tailWord_3952677) baseStart_3952677 baseEnd_3952677 := by
    simpa [prefixWord, tailWord_3952677, baseEnd_3952677] using wordTrace_append hprefix tailTrace_3952677
  have hstable : (prefixWord ++ tailWord_3952677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952677).length < 2 ^ (prefixWord ++ tailWord_3952677).sum := by decide
  have hdescent : baseEnd_3952677 < baseStart_3952677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952688 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_3952688 : Nat := 118140960795 + 3952688 * 2 ^ 59
def prefixEnd_3952688 : Nat := 4983230072969 + 3 ^ 40 * 3952688 * 2
def baseEnd_3952688 : Nat := 1353085880839290882481283

theorem tailTrace_3952688 : CollatzResearch.WordTrace tailWord_3952688 prefixEnd_3952688 1353085880839290882481283 := by
  unfold tailWord_3952688
  simp only [CollatzResearch.WordTrace]
  refine ⟨72083187552046958105405359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96110916736062610807207145 72083187552046958105405359)
  ·
    refine ⟨108124781328070437158108039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72083187552046958105405359 108124781328070437158108039)
    ·
      refine ⟨162187171992105655737162059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108124781328070437158108039 162187171992105655737162059)
      ·
        refine ⟨243280757988158483605743089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162187171992105655737162059 243280757988158483605743089)
        ·
          refine ⟨182460568491118862704307317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243280757988158483605743089 182460568491118862704307317)
          ·
            refine ⟨17105678296042393378528811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182460568491118862704307317 17105678296042393378528811)
            ·
              refine ⟨25658517444063590067793217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17105678296042393378528811 25658517444063590067793217)
              ·
                refine ⟨19243888083047692550844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25658517444063590067793217 19243888083047692550844913)
                ·
                  refine ⟨14432916062285769413133685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19243888083047692550844913 14432916062285769413133685)
                  ·
                    refine ⟨1353085880839290882481283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14432916062285769413133685 1353085880839290882481283)
                    ·
                      rfl

theorem cell22_3952688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_3952688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952688 prefixEnd_3952688 := by exact prefixLift 3952688
  have htrace : WordTrace (prefixWord ++ tailWord_3952688) baseStart_3952688 baseEnd_3952688 := by
    simpa [prefixWord, tailWord_3952688, baseEnd_3952688] using wordTrace_append hprefix tailTrace_3952688
  have hstable : (prefixWord ++ tailWord_3952688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952688).length < 2 ^ (prefixWord ++ tailWord_3952688).sum := by decide
  have hdescent : baseEnd_3952688 < baseStart_3952688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952690 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3952690 : Nat := 118140960795 + 3952690 * 2 ^ 59
def prefixEnd_3952690 : Nat := 4983230072969 + 3 ^ 40 * 3952690 * 2
def baseEnd_3952690 : Nat := 451028855160054514643759

theorem tailTrace_3952690 : CollatzResearch.WordTrace tailWord_3952690 prefixEnd_3952690 451028855160054514643759 := by
  unfold tailWord_3952690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041612012521667638095881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96110965366724447034922349 36041612012521667638095881)
  ·
    refine ⟨27031209009391250728571911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36041612012521667638095881 27031209009391250728571911)
    ·
      refine ⟨40546813514086876092857867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27031209009391250728571911 40546813514086876092857867)
      ·
        refine ⟨60820220271130314139286801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40546813514086876092857867 60820220271130314139286801)
        ·
          refine ⟨45615165203347735604465101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60820220271130314139286801 45615165203347735604465101)
          ·
            refine ⟨17105686951255400851674413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45615165203347735604465101 17105686951255400851674413)
            ·
              refine ⟨6414632606720775319377905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17105686951255400851674413 6414632606720775319377905)
              ·
                refine ⟨4810974455040581489533429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414632606720775319377905 4810974455040581489533429)
                ·
                  refine ⟨451028855160054514643759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4810974455040581489533429 451028855160054514643759)
                  ·
                    rfl

theorem cell22_3952690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3952690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952690 prefixEnd_3952690 := by exact prefixLift 3952690
  have htrace : WordTrace (prefixWord ++ tailWord_3952690) baseStart_3952690 baseEnd_3952690 := by
    simpa [prefixWord, tailWord_3952690, baseEnd_3952690] using wordTrace_append hprefix tailTrace_3952690
  have hstable : (prefixWord ++ tailWord_3952690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952690).length < 2 ^ (prefixWord ++ tailWord_3952690).sum := by decide
  have hdescent : baseEnd_3952690 < baseStart_3952690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952694 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3952694 : Nat := 118140960795 + 3952694 * 2 ^ 59
def prefixEnd_3952694 : Nat := 4983230072969 + 3 ^ 40 * 3952694 * 2
def baseEnd_3952694 : Nat := 1353087934761908866831265

theorem tailTrace_3952694 : CollatzResearch.WordTrace tailWord_3952694 prefixEnd_3952694 1353087934761908866831265 := by
  unfold tailWord_3952694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010412121379511202220571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96111062628048119490352757 9010412121379511202220571)
  ·
    refine ⟨13515618182069266803330857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9010412121379511202220571 13515618182069266803330857)
    ·
      refine ⟨10136713636551950102498143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13515618182069266803330857 10136713636551950102498143)
      ·
        refine ⟨15205070454827925153747215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136713636551950102498143 15205070454827925153747215)
        ·
          refine ⟨22807605682241887730620823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205070454827925153747215 22807605682241887730620823)
          ·
            refine ⟨34211408523362831595931235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22807605682241887730620823 34211408523362831595931235)
            ·
              refine ⟨51317112785044247393896853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34211408523362831595931235 51317112785044247393896853)
              ·
                refine ⟨2405489661798949096588915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51317112785044247393896853 2405489661798949096588915)
                ·
                  refine ⟨3608234492698423644883373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405489661798949096588915 3608234492698423644883373)
                  ·
                    refine ⟨1353087934761908866831265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608234492698423644883373 1353087934761908866831265)
                    ·
                      rfl

theorem cell22_3952694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3952694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952694 prefixEnd_3952694 := by exact prefixLift 3952694
  have htrace : WordTrace (prefixWord ++ tailWord_3952694) baseStart_3952694 baseEnd_3952694 := by
    simpa [prefixWord, tailWord_3952694, baseEnd_3952694] using wordTrace_append hprefix tailTrace_3952694
  have hstable : (prefixWord ++ tailWord_3952694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952694).length < 2 ^ (prefixWord ++ tailWord_3952694).sum := by decide
  have hdescent : baseEnd_3952694 < baseStart_3952694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952703 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 5, 4]
def baseStart_3952703 : Nat := 118140960795 + 3952703 * 2 ^ 59
def prefixEnd_3952703 : Nat := 4983230072969 + 3 ^ 40 * 3952703 * 2
def baseEnd_3952703 : Nat := 1353091015645835843356237

theorem tailTrace_3952703 : CollatzResearch.WordTrace tailWord_3952703 prefixEnd_3952703 1353091015645835843356237 := by
  unfold tailWord_3952703
  simp only [CollatzResearch.WordTrace]
  refine ⟨144166922199039573772606763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96111281466026382515071175 144166922199039573772606763)
  ·
    refine ⟨216250383298559360658910145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144166922199039573772606763 216250383298559360658910145)
    ·
      refine ⟨162187787473919520494182609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216250383298559360658910145 162187787473919520494182609)
      ·
        refine ⟨121640840605439640370636957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162187787473919520494182609 121640840605439640370636957)
        ·
          refine ⟨45615315227039865138988859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121640840605439640370636957 45615315227039865138988859)
          ·
            refine ⟨68422972840559797708483289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45615315227039865138988859 68422972840559797708483289)
            ·
              refine ⟨51317229630419848281362467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68422972840559797708483289 51317229630419848281362467)
              ·
                refine ⟨76975844445629772422043701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51317229630419848281362467 76975844445629772422043701)
                ·
                  refine ⟨7216485416777791164566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76975844445629772422043701 7216485416777791164566597)
                  ·
                    refine ⟨1353091015645835843356237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7216485416777791164566597 1353091015645835843356237)
                    ·
                      rfl

theorem cell22_3952703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_3952703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952703 prefixEnd_3952703 := by exact prefixLift 3952703
  have htrace : WordTrace (prefixWord ++ tailWord_3952703) baseStart_3952703 baseEnd_3952703 := by
    simpa [prefixWord, tailWord_3952703, baseEnd_3952703] using wordTrace_append hprefix tailTrace_3952703
  have hstable : (prefixWord ++ tailWord_3952703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952703).length < 2 ^ (prefixWord ++ tailWord_3952703).sum := by decide
  have hdescent : baseEnd_3952703 < baseStart_3952703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952705 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3952705 : Nat := 118140960795 + 3952705 * 2 ^ 59
def prefixEnd_3952705 : Nat := 4983230072969 + 3 ^ 40 * 3952705 * 2
def baseEnd_3952705 : Nat := 1353091700286708504806231

theorem tailTrace_3952705 : CollatzResearch.WordTrace tailWord_3952705 prefixEnd_3952705 1353091700286708504806231 := by
  unfold tailWord_3952705
  simp only [CollatzResearch.WordTrace]
  refine ⟨144166995145032328114179569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96111330096688218742786379 144166995145032328114179569)
  ·
    refine ⟨108125246358774246085634677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144166995145032328114179569 108125246358774246085634677)
    ·
      refine ⟨10136741846135085570528251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108125246358774246085634677 10136741846135085570528251)
      ·
        refine ⟨15205112769202628355792377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136741846135085570528251 15205112769202628355792377)
        ·
          refine ⟨11403834576901971266844283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15205112769202628355792377 11403834576901971266844283)
          ·
            refine ⟨17105751865352956900266425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11403834576901971266844283 17105751865352956900266425)
            ·
              refine ⟨12829313899014717675199819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17105751865352956900266425 12829313899014717675199819)
              ·
                refine ⟨19243970848522076512799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12829313899014717675199819 19243970848522076512799729)
                ·
                  refine ⟨14432978136391557384599797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19243970848522076512799729 14432978136391557384599797)
                  ·
                    refine ⟨1353091700286708504806231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14432978136391557384599797 1353091700286708504806231)
                    ·
                      rfl

theorem cell22_3952705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3952705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952705 prefixEnd_3952705 := by exact prefixLift 3952705
  have htrace : WordTrace (prefixWord ++ tailWord_3952705) baseStart_3952705 baseEnd_3952705 := by
    simpa [prefixWord, tailWord_3952705, baseEnd_3952705] using wordTrace_append hprefix tailTrace_3952705
  have hstable : (prefixWord ++ tailWord_3952705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952705).length < 2 ^ (prefixWord ++ tailWord_3952705).sum := by decide
  have hdescent : baseEnd_3952705 < baseStart_3952705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952735 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 4]
def baseStart_3952735 : Nat := 118140960795 + 3952735 * 2 ^ 59
def prefixEnd_3952735 : Nat := 4983230072969 + 3 ^ 40 * 3952735 * 2
def baseEnd_3952735 : Nat := 451033989966599475518713

theorem tailTrace_3952735 : CollatzResearch.WordTrace tailWord_3952735 prefixEnd_3952735 451033989966599475518713 := by
  unfold tailWord_3952735
  simp only [CollatzResearch.WordTrace]
  refine ⟨144168089334923643237771659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96112059556615762158514439 144168089334923643237771659)
  ·
    refine ⟨216252134002385464856657489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144168089334923643237771659 216252134002385464856657489)
    ·
      refine ⟨162189100501789098642493117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216252134002385464856657489 162189100501789098642493117)
      ·
        refine ⟨60820912688170911990934919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162189100501789098642493117 60820912688170911990934919)
        ·
          refine ⟨91231369032256367986402379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60820912688170911990934919 91231369032256367986402379)
          ·
            refine ⟨136847053548384551979603569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91231369032256367986402379 136847053548384551979603569)
            ·
              refine ⟨102635290161288413984702677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136847053548384551979603569 102635290161288413984702677)
              ·
                refine ⟨2405514613155197202766469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102635290161288413984702677 2405514613155197202766469)
                ·
                  refine ⟨451033989966599475518713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405514613155197202766469 451033989966599475518713)
                  ·
                    rfl

theorem cell22_3952735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 4].length) (baseStart_3952735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952735 prefixEnd_3952735 := by exact prefixLift 3952735
  have htrace : WordTrace (prefixWord ++ tailWord_3952735) baseStart_3952735 baseEnd_3952735 := by
    simpa [prefixWord, tailWord_3952735, baseEnd_3952735] using wordTrace_append hprefix tailTrace_3952735
  have hstable : (prefixWord ++ tailWord_3952735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952735).length < 2 ^ (prefixWord ++ tailWord_3952735).sum := by decide
  have hdescent : baseEnd_3952735 < baseStart_3952735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952793 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_3952793 : Nat := 118140960795 + 3952793 * 2 ^ 59
def prefixEnd_3952793 : Nat := 4983230072969 + 3 ^ 40 * 3952793 * 2
def baseEnd_3952793 : Nat := 1353121824485105608605961

theorem tailTrace_3952793 : CollatzResearch.WordTrace tailWord_3952793 prefixEnd_3952793 1353121824485105608605961 := by
  unfold tailWord_3952793
  simp only [CollatzResearch.WordTrace]
  refine ⟨144170204768713519143383033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96113469845809012762255355 144170204768713519143383033)
  ·
    refine ⟨108127653576535139357537275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144170204768713519143383033 108127653576535139357537275)
    ·
      refine ⟨162191480364802709036305913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108127653576535139357537275 162191480364802709036305913)
      ·
        refine ⟨121643610273602031777229435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162191480364802709036305913 121643610273602031777229435)
        ·
          refine ⟨182465415410403047665844153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121643610273602031777229435 182465415410403047665844153)
          ·
            refine ⟨136849061557802285749383115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182465415410403047665844153 136849061557802285749383115)
            ·
              refine ⟨205273592336703428624074673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136849061557802285749383115 205273592336703428624074673)
              ·
                refine ⟨153955194252527571468056005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205273592336703428624074673 153955194252527571468056005)
                ·
                  refine ⟨28866598922348919650260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153955194252527571468056005 28866598922348919650260501)
                  ·
                    refine ⟨1353121824485105608605961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28866598922348919650260501 1353121824485105608605961)
                    ·
                      rfl

theorem cell22_3952793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_3952793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952793 prefixEnd_3952793 := by exact prefixLift 3952793
  have htrace : WordTrace (prefixWord ++ tailWord_3952793) baseStart_3952793 baseEnd_3952793 := by
    simpa [prefixWord, tailWord_3952793, baseEnd_3952793] using wordTrace_append hprefix tailTrace_3952793
  have hstable : (prefixWord ++ tailWord_3952793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952793).length < 2 ^ (prefixWord ++ tailWord_3952793).sum := by decide
  have hdescent : baseEnd_3952793 < baseStart_3952793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952825 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 5]
def baseStart_3952825 : Nat := 118140960795 + 3952825 * 2 ^ 59
def prefixEnd_3952825 : Nat := 4983230072969 + 3 ^ 40 * 3952825 * 2
def baseEnd_3952825 : Nat := 451044259579689397268621

theorem tailTrace_3952825 : CollatzResearch.WordTrace tailWord_3952825 prefixEnd_3952825 451044259579689397268621 := by
  unfold tailWord_3952825
  simp only [CollatzResearch.WordTrace]
  refine ⟨144171371904597588608547929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96114247936398392405698619 144171371904597588608547929)
  ·
    refine ⟨108128528928448191456410947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144171371904597588608547929 108128528928448191456410947)
    ·
      refine ⟨162192793392672287184616421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108128528928448191456410947 162192793392672287184616421)
      ·
        refine ⟨30411148761126053847115579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162192793392672287184616421 30411148761126053847115579)
        ·
          refine ⟨45616723141689080770673369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30411148761126053847115579 45616723141689080770673369)
          ·
            refine ⟨34212542356266810578005027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45616723141689080770673369 34212542356266810578005027)
            ·
              refine ⟨51318813534400215867007541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34212542356266810578005027 51318813534400215867007541)
              ·
                refine ⟨4811138768850020237531957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51318813534400215867007541 4811138768850020237531957)
                ·
                  refine ⟨451044259579689397268621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811138768850020237531957 451044259579689397268621)
                  ·
                    rfl

theorem cell22_3952825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_3952825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952825 prefixEnd_3952825 := by exact prefixLift 3952825
  have htrace : WordTrace (prefixWord ++ tailWord_3952825) baseStart_3952825 baseEnd_3952825 := by
    simpa [prefixWord, tailWord_3952825, baseEnd_3952825] using wordTrace_append hprefix tailTrace_3952825
  have hstable : (prefixWord ++ tailWord_3952825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952825).length < 2 ^ (prefixWord ++ tailWord_3952825).sum := by decide
  have hdescent : baseEnd_3952825 < baseStart_3952825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952846 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3952846 : Nat := 118140960795 + 3952846 * 2 ^ 59
def prefixEnd_3952846 : Nat := 4983230072969 + 3 ^ 40 * 3952846 * 2
def baseEnd_3952846 : Nat := 1353139967468231137030799

theorem tailTrace_3952846 : CollatzResearch.WordTrace tailWord_3952846 prefixEnd_3952846 1353139967468231137030799 := by
  unfold tailWord_3952846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021517229690188649382799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96114758558347672796708261 18021517229690188649382799)
  ·
    refine ⟨27032275844535282974074199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18021517229690188649382799 27032275844535282974074199)
    ·
      refine ⟨40548413766802924461111299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27032275844535282974074199 40548413766802924461111299)
      ·
        refine ⟨60822620650204386691666949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40548413766802924461111299 60822620650204386691666949)
        ·
          refine ⟨11404241371913322504687553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60822620650204386691666949 11404241371913322504687553)
          ·
            refine ⟨8553181028934991878515665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11404241371913322504687553 8553181028934991878515665)
            ·
              refine ⟨6414885771701243908886749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553181028934991878515665 6414885771701243908886749)
              ·
                refine ⟨2405582164387966465832531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414885771701243908886749 2405582164387966465832531)
                ·
                  refine ⟨3608373246581949698748797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405582164387966465832531 3608373246581949698748797)
                  ·
                    refine ⟨1353139967468231137030799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608373246581949698748797 1353139967468231137030799)
                    ·
                      rfl

theorem cell22_3952846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3952846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952846 prefixEnd_3952846 := by exact prefixLift 3952846
  have htrace : WordTrace (prefixWord ++ tailWord_3952846) baseStart_3952846 baseEnd_3952846 := by
    simpa [prefixWord, tailWord_3952846, baseEnd_3952846] using wordTrace_append hprefix tailTrace_3952846
  have hstable : (prefixWord ++ tailWord_3952846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952846).length < 2 ^ (prefixWord ++ tailWord_3952846).sum := by decide
  have hdescent : baseEnd_3952846 < baseStart_3952846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952904 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_3952904 : Nat := 118140960795 + 3952904 * 2 ^ 59
def prefixEnd_3952904 : Nat := 4983230072969 + 3 ^ 40 * 3952904 * 2
def baseEnd_3952904 : Nat := 451053274017846106360207

theorem tailTrace_3952904 : CollatzResearch.WordTrace tailWord_3952904 prefixEnd_3952904 451053274017846106360207 := by
  unfold tailWord_3952904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72087126635655692550336883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96116168847540923400449177 72087126635655692550336883)
  ·
    refine ⟨108130689953483538825505325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72087126635655692550336883 108130689953483538825505325)
    ·
      refine ⟨40549008732556327059564497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108130689953483538825505325 40549008732556327059564497)
      ·
        refine ⟨30411756549417245294673373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40549008732556327059564497 30411756549417245294673373)
        ·
          refine ⟨11404408706031466985502515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30411756549417245294673373 11404408706031466985502515)
          ·
            refine ⟨17106613059047200478253773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404408706031466985502515 17106613059047200478253773)
            ·
              refine ⟨6414979897142700179345165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17106613059047200478253773 6414979897142700179345165)
              ·
                refine ⟨2405617461428512567254437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414979897142700179345165 2405617461428512567254437)
                ·
                  refine ⟨451053274017846106360207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405617461428512567254437 451053274017846106360207)
                  ·
                    rfl

theorem cell22_3952904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_3952904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952904 prefixEnd_3952904 := by exact prefixLift 3952904
  have htrace : WordTrace (prefixWord ++ tailWord_3952904) baseStart_3952904 baseEnd_3952904 := by
    simpa [prefixWord, tailWord_3952904, baseEnd_3952904] using wordTrace_append hprefix tailTrace_3952904
  have hstable : (prefixWord ++ tailWord_3952904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952904).length < 2 ^ (prefixWord ++ tailWord_3952904).sum := by decide
  have hdescent : baseEnd_3952904 < baseStart_3952904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952932 : List Nat := [2, 3, 1, 3, 1, 3, 2, 7]
def baseStart_3952932 : Nat := 118140960795 + 3952932 * 2 ^ 59
def prefixEnd_3952932 : Nat := 4983230072969 + 3 ^ 40 * 3952932 * 2
def baseEnd_3952932 : Nat := 150352156336195064375615

theorem tailTrace_3952932 : CollatzResearch.WordTrace tailWord_3952932 prefixEnd_3952932 150352156336195064375615 := by
  unfold tailWord_3952932
  simp only [CollatzResearch.WordTrace]
  refine ⟨72087637257604972941346525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96116849676806630588462033 72087637257604972941346525)
  ·
    refine ⟨27032863971601864853004947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72087637257604972941346525 27032863971601864853004947)
    ·
      refine ⟨40549295957402797279507421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27032863971601864853004947 40549295957402797279507421)
      ·
        refine ⟨15205985984026048979815283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40549295957402797279507421 15205985984026048979815283)
        ·
          refine ⟨22808978976039073469722925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205985984026048979815283 22808978976039073469722925)
          ·
            refine ⟨8553367116014652551146097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22808978976039073469722925 8553367116014652551146097)
            ·
              refine ⟨6415025337010989413359573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553367116014652551146097 6415025337010989413359573)
              ·
                refine ⟨150352156336195064375615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6415025337010989413359573 150352156336195064375615)
                ·
                  rfl

theorem cell22_3952932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_3952932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952932 prefixEnd_3952932 := by exact prefixLift 3952932
  have htrace : WordTrace (prefixWord ++ tailWord_3952932) baseStart_3952932 baseEnd_3952932 := by
    simpa [prefixWord, tailWord_3952932, baseEnd_3952932] using wordTrace_append hprefix tailTrace_3952932
  have hstable : (prefixWord ++ tailWord_3952932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952932).length < 2 ^ (prefixWord ++ tailWord_3952932).sum := by decide
  have hdescent : baseEnd_3952932 < baseStart_3952932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952936 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3952936 : Nat := 118140960795 + 3952936 * 2 ^ 59
def prefixEnd_3952936 : Nat := 4983230072969 + 3 ^ 40 * 3952936 * 2
def baseEnd_3952936 : Nat := 1353170776307500902280523

theorem tailTrace_3952936 : CollatzResearch.WordTrace tailWord_3952936 prefixEnd_3952936 1353170776307500902280523 := by
  unfold tailWord_3952936
  simp only [CollatzResearch.WordTrace]
  refine ⟨72087710203597727282919331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96116946938130303043892441 72087710203597727282919331)
  ·
    refine ⟨108131565305396590924378997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72087710203597727282919331 108131565305396590924378997)
    ·
      refine ⟨10137334247380930399160531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108131565305396590924378997 10137334247380930399160531)
      ·
        refine ⟨15206001371071395598740797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137334247380930399160531 15206001371071395598740797)
        ·
          refine ⟨5702250514151773349527799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15206001371071395598740797 5702250514151773349527799)
          ·
            refine ⟨8553375771227660024291699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702250514151773349527799 8553375771227660024291699)
            ·
              refine ⟨12830063656841490036437549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553375771227660024291699 12830063656841490036437549)
              ·
                refine ⟨4811273871315558763664081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12830063656841490036437549 4811273871315558763664081)
                ·
                  refine ⟨3608455403486669072748061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811273871315558763664081 3608455403486669072748061)
                  ·
                    refine ⟨1353170776307500902280523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608455403486669072748061 1353170776307500902280523)
                    ·
                      rfl

theorem cell22_3952936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3952936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952936 prefixEnd_3952936 := by exact prefixLift 3952936
  have htrace : WordTrace (prefixWord ++ tailWord_3952936) baseStart_3952936 baseEnd_3952936 := by
    simpa [prefixWord, tailWord_3952936, baseEnd_3952936] using wordTrace_append hprefix tailTrace_3952936
  have hstable : (prefixWord ++ tailWord_3952936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952936).length < 2 ^ (prefixWord ++ tailWord_3952936).sum := by decide
  have hdescent : baseEnd_3952936 < baseStart_3952936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952947 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 5, 3]
def baseStart_3952947 : Nat := 118140960795 + 3952947 * 2 ^ 59
def prefixEnd_3952947 : Nat := 4983230072969 + 3 ^ 40 * 3952947 * 2
def baseEnd_3952947 : Nat := 1353174541832300540255489

theorem tailTrace_3952947 : CollatzResearch.WordTrace tailWord_3952947 prefixEnd_3952947 1353174541832300540255489 := by
  unfold tailWord_3952947
  simp only [CollatzResearch.WordTrace]
  refine ⟨144175821610155603444489095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96117214406770402296326063 144175821610155603444489095)
  ·
    refine ⟨216263732415233405166733643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144175821610155603444489095 216263732415233405166733643)
    ·
      refine ⟨324395598622850107750100465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216263732415233405166733643 324395598622850107750100465)
      ·
        refine ⟨243296698967137580812575349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324395598622850107750100465 243296698967137580812575349)
        ·
          refine ⟨22809065528169148201178939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243296698967137580812575349 22809065528169148201178939)
          ·
            refine ⟨34213598292253722301768409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22809065528169148201178939 34213598292253722301768409)
            ·
              refine ⟨25660198719190291726326307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34213598292253722301768409 25660198719190291726326307)
              ·
                refine ⟨38490298078785437589489461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25660198719190291726326307 38490298078785437589489461)
                ·
                  refine ⟨3608465444886134774014637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38490298078785437589489461 3608465444886134774014637)
                  ·
                    refine ⟨1353174541832300540255489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608465444886134774014637 1353174541832300540255489)
                    ·
                      rfl

theorem cell22_3952947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].length) (baseStart_3952947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952947 prefixEnd_3952947 := by exact prefixLift 3952947
  have htrace : WordTrace (prefixWord ++ tailWord_3952947) baseStart_3952947 baseEnd_3952947 := by
    simpa [prefixWord, tailWord_3952947, baseEnd_3952947] using wordTrace_append hprefix tailTrace_3952947
  have hstable : (prefixWord ++ tailWord_3952947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952947).length < 2 ^ (prefixWord ++ tailWord_3952947).sum := by decide
  have hdescent : baseEnd_3952947 < baseStart_3952947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952960 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_3952960 : Nat := 118140960795 + 3952960 * 2 ^ 59
def prefixEnd_3952960 : Nat := 4983230072969 + 3 ^ 40 * 3952960 * 2
def baseEnd_3952960 : Nat := 451059663999324279893483

theorem tailTrace_3952960 : CollatzResearch.WordTrace tailWord_3952960 prefixEnd_3952960 451059663999324279893483 := by
  unfold tailWord_3952960
  simp only [CollatzResearch.WordTrace]
  refine ⟨72088147879554253332356167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96117530506072337776474889 72088147879554253332356167)
  ·
    refine ⟨108132221819331379998534251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72088147879554253332356167 108132221819331379998534251)
    ·
      refine ⟨162198332728997069997801377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108132221819331379998534251 162198332728997069997801377)
      ·
        refine ⟨121648749546747802498351033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162198332728997069997801377 121648749546747802498351033)
        ·
          refine ⟨91236562160060851873763275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121648749546747802498351033 91236562160060851873763275)
          ·
            refine ⟨136854843240091277810644913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91236562160060851873763275 136854843240091277810644913)
            ·
              refine ⟨102641132430068458357983685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136854843240091277810644913 102641132430068458357983685)
              ·
                refine ⟨19245212330637835942121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102641132430068458357983685 19245212330637835942121941)
                ·
                  refine ⟨451059663999324279893483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19245212330637835942121941 451059663999324279893483)
                  ·
                    rfl

theorem cell22_3952960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_3952960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952960 prefixEnd_3952960 := by exact prefixLift 3952960
  have htrace : WordTrace (prefixWord ++ tailWord_3952960) baseStart_3952960 baseEnd_3952960 := by
    simpa [prefixWord, tailWord_3952960, baseEnd_3952960] using wordTrace_append hprefix tailTrace_3952960
  have hstable : (prefixWord ++ tailWord_3952960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952960).length < 2 ^ (prefixWord ++ tailWord_3952960).sum := by decide
  have hdescent : baseEnd_3952960 < baseStart_3952960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952977 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 5]
def baseStart_3952977 : Nat := 118140960795 + 3952977 * 2 ^ 59
def prefixEnd_3952977 : Nat := 4983230072969 + 3 ^ 40 * 3952977 * 2
def baseEnd_3952977 : Nat := 451061603815130154001799

theorem tailTrace_3952977 : CollatzResearch.WordTrace tailWord_3952977 prefixEnd_3952977 451061603815130154001799 := by
  unfold tailWord_3952977
  simp only [CollatzResearch.WordTrace]
  refine ⟨144176915800046918568081185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96117943866697945712054123 144176915800046918568081185)
  ·
    refine ⟨108132686850035188926060889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144176915800046918568081185 108132686850035188926060889)
    ·
      refine ⟨81099515137526391694545667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108132686850035188926060889 81099515137526391694545667)
      ·
        refine ⟨121649272706289587541818501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81099515137526391694545667 121649272706289587541818501)
        ·
          refine ⟨22809238632429297664090969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121649272706289587541818501 22809238632429297664090969)
          ·
            refine ⟨17106928974321973248068227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22809238632429297664090969 17106928974321973248068227)
            ·
              refine ⟨25660393461482959872102341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17106928974321973248068227 25660393461482959872102341)
              ·
                refine ⟨4811323774028054976019189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25660393461482959872102341 4811323774028054976019189)
                ·
                  refine ⟨451061603815130154001799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811323774028054976019189 451061603815130154001799)
                  ·
                    rfl

theorem cell22_3952977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_3952977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952977 prefixEnd_3952977 := by exact prefixLift 3952977
  have htrace : WordTrace (prefixWord ++ tailWord_3952977) baseStart_3952977 baseEnd_3952977 := by
    simpa [prefixWord, tailWord_3952977, baseEnd_3952977] using wordTrace_append hprefix tailTrace_3952977
  have hstable : (prefixWord ++ tailWord_3952977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952977).length < 2 ^ (prefixWord ++ tailWord_3952977).sum := by decide
  have hdescent : baseEnd_3952977 < baseStart_3952977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3952994 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3952994 : Nat := 118140960795 + 3952994 * 2 ^ 59
def prefixEnd_3952994 : Nat := 4983230072969 + 3 ^ 40 * 3952994 * 2
def baseEnd_3952994 : Nat := 451063543630936028110115

theorem tailTrace_3952994 : CollatzResearch.WordTrace tailWord_3952994 prefixEnd_3952994 451063543630936028110115 := by
  unfold tailWord_3952994
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044383960246332617862509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96118357227323553647633357 36044383960246332617862509)
  ·
    refine ⟨13516643985092374731698441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36044383960246332617862509 13516643985092374731698441)
    ·
      refine ⟨10137482988819281048773831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13516643985092374731698441 10137482988819281048773831)
      ·
        refine ⟨15206224483228921573160747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137482988819281048773831 15206224483228921573160747)
        ·
          refine ⟨22809336724843382359741121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206224483228921573160747 22809336724843382359741121)
          ·
            refine ⟨17107002543632536769805841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22809336724843382359741121 17107002543632536769805841)
            ·
              refine ⟨12830251907724402577354381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17107002543632536769805841 12830251907724402577354381)
              ·
                refine ⟨4811344465396650966507893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12830251907724402577354381 4811344465396650966507893)
                ·
                  refine ⟨451063543630936028110115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811344465396650966507893 451063543630936028110115)
                  ·
                    rfl

theorem cell22_3952994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3952994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3952994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3952994 prefixEnd_3952994 := by exact prefixLift 3952994
  have htrace : WordTrace (prefixWord ++ tailWord_3952994) baseStart_3952994 baseEnd_3952994 := by
    simpa [prefixWord, tailWord_3952994, baseEnd_3952994] using wordTrace_append hprefix tailTrace_3952994
  have hstable : (prefixWord ++ tailWord_3952994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3952994).length < 2 ^ (prefixWord ++ tailWord_3952994).sum := by decide
  have hdescent : baseEnd_3952994 < baseStart_3952994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3952994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953084 : List Nat := [2, 2, 2, 4, 1, 3, 8]
def baseStart_3953084 : Nat := 118140960795 + 3953084 * 2 ^ 59
def prefixEnd_3953084 : Nat := 4983230072969 + 3 ^ 40 * 3953084 * 2
def baseEnd_3953084 : Nat := 50119312582669549984447

theorem tailTrace_3953084 : CollatzResearch.WordTrace tailWord_3953084 prefixEnd_3953084 50119312582669549984447 := by
  unfold tailWord_3953084
  simp only [CollatzResearch.WordTrace]
  refine ⟨72090409205329637921113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96120545607106183894817537 72090409205329637921113153)
  ·
    refine ⟨54067806903997228440834865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72090409205329637921113153 54067806903997228440834865)
    ·
      refine ⟨40550855177997921330626149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54067806903997228440834865 40550855177997921330626149)
      ·
        refine ⟨7603285345874610249492403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40550855177997921330626149 7603285345874610249492403)
        ·
          refine ⟨11404928018811915374238605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603285345874610249492403 11404928018811915374238605)
          ·
            refine ⟨4276848007054468265339477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11404928018811915374238605 4276848007054468265339477)
            ·
              refine ⟨50119312582669549984447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4276848007054468265339477 50119312582669549984447)
              ·
                rfl

theorem cell22_3953084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 8].length) (baseStart_3953084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953084 prefixEnd_3953084 := by exact prefixLift 3953084
  have htrace : WordTrace (prefixWord ++ tailWord_3953084) baseStart_3953084 baseEnd_3953084 := by
    simpa [prefixWord, tailWord_3953084, baseEnd_3953084] using wordTrace_append hprefix tailTrace_3953084
  have hstable : (prefixWord ++ tailWord_3953084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953084).length < 2 ^ (prefixWord ++ tailWord_3953084).sum := by decide
  have hdescent : baseEnd_3953084 < baseStart_3953084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953189 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3953189 : Nat := 118140960795 + 3953189 * 2 ^ 59
def prefixEnd_3953189 : Nat := 4983230072969 + 3 ^ 40 * 3953189 * 2
def baseEnd_3953189 : Nat := 1353257383377892575704747

theorem tailTrace_3953189 : CollatzResearch.WordTrace tailWord_3953189 prefixEnd_3953189 1353257383377892575704747 := by
  unfold tailWord_3953189
  simp only [CollatzResearch.WordTrace]
  refine ⟨144184648075278878774798621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96123098716852585849865747 144184648075278878774798621)
  ·
    refine ⟨54069243028229579540549483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144184648075278878774798621 54069243028229579540549483)
    ·
      refine ⟨81103864542344369310824225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54069243028229579540549483 81103864542344369310824225)
      ·
        refine ⟨60827898406758276983118169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81103864542344369310824225 60827898406758276983118169)
        ·
          refine ⟨45620923805068707737338627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60827898406758276983118169 45620923805068707737338627)
          ·
            refine ⟨68431385707603061606007941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45620923805068707737338627 68431385707603061606007941)
            ·
              refine ⟨12830884820175574051126489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68431385707603061606007941 12830884820175574051126489)
              ·
                refine ⟨9623163615131680538344867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12830884820175574051126489 9623163615131680538344867)
                ·
                  refine ⟨14434745422697520807517301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623163615131680538344867 14434745422697520807517301)
                  ·
                    refine ⟨1353257383377892575704747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14434745422697520807517301 1353257383377892575704747)
                    ·
                      rfl

theorem cell22_3953189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3953189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953189 prefixEnd_3953189 := by exact prefixLift 3953189
  have htrace : WordTrace (prefixWord ++ tailWord_3953189) baseStart_3953189 baseEnd_3953189 := by
    simpa [prefixWord, tailWord_3953189, baseEnd_3953189] using wordTrace_append hprefix tailTrace_3953189
  have hstable : (prefixWord ++ tailWord_3953189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953189).length < 2 ^ (prefixWord ++ tailWord_3953189).sum := by decide
  have hdescent : baseEnd_3953189 < baseStart_3953189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953197 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3953197 : Nat := 118140960795 + 3953197 * 2 ^ 59
def prefixEnd_3953197 : Nat := 4983230072969 + 3 ^ 40 * 3953197 * 2
def baseEnd_3953197 : Nat := 451086707313794407168241

theorem tailTrace_3953197 : CollatzResearch.WordTrace tailWord_3953197 prefixEnd_3953197 451086707313794407168241 := by
  unfold tailWord_3953197
  simp only [CollatzResearch.WordTrace]
  refine ⟨144184939859249896141089845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96123293239499930760726563 144184939859249896141089845)
  ·
    refine ⟨13517338111804677763227173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144184939859249896141089845 13517338111804677763227173)
    ·
      refine ⟨2534500895963377080605095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13517338111804677763227173 2534500895963377080605095)
      ·
        refine ⟨3801751343945065620907643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534500895963377080605095 3801751343945065620907643)
        ·
          refine ⟨5702627015917598431361465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801751343945065620907643 5702627015917598431361465)
          ·
            refine ⟨4276970261938198823521099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702627015917598431361465 4276970261938198823521099)
            ·
              refine ⟨6415455392907298235281649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276970261938198823521099 6415455392907298235281649)
              ·
                refine ⟨4811591544680473676461237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6415455392907298235281649 4811591544680473676461237)
                ·
                  refine ⟨451086707313794407168241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811591544680473676461237 451086707313794407168241)
                  ·
                    rfl

theorem cell22_3953197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3953197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953197 prefixEnd_3953197 := by exact prefixLift 3953197
  have htrace : WordTrace (prefixWord ++ tailWord_3953197) baseStart_3953197 baseEnd_3953197 := by
    simpa [prefixWord, tailWord_3953197, baseEnd_3953197] using wordTrace_append hprefix tailTrace_3953197
  have hstable : (prefixWord ++ tailWord_3953197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953197).length < 2 ^ (prefixWord ++ tailWord_3953197).sum := by decide
  have hdescent : baseEnd_3953197 < baseStart_3953197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953234 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3953234 : Nat := 118140960795 + 3953234 * 2 ^ 59
def prefixEnd_3953234 : Nat := 4983230072969 + 3 ^ 40 * 3953234 * 2
def baseEnd_3953234 : Nat := 1353272787797527458329609

theorem tailTrace_3953234 : CollatzResearch.WordTrace tailWord_3953234 prefixEnd_3953234 1353272787797527458329609 := by
  unfold tailWord_3953234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36046572340028962865046689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96124192906743900973457837 36046572340028962865046689)
  ·
    refine ⟨27034929255021722148785017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36046572340028962865046689 27034929255021722148785017)
    ·
      refine ⟨20276196941266291611588763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27034929255021722148785017 20276196941266291611588763)
      ·
        refine ⟨30414295411899437417383145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276196941266291611588763 30414295411899437417383145)
        ·
          refine ⟨22810721558924578063037359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30414295411899437417383145 22810721558924578063037359)
          ·
            refine ⟨34216082338386867094556039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810721558924578063037359 34216082338386867094556039)
            ·
              refine ⟨51324123507580300641834059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34216082338386867094556039 51324123507580300641834059)
              ·
                refine ⟨76986185261370450962751089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51324123507580300641834059 76986185261370450962751089)
                ·
                  refine ⟨57739638946027838222063317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76986185261370450962751089 57739638946027838222063317)
                  ·
                    refine ⟨1353272787797527458329609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57739638946027838222063317 1353272787797527458329609)
                    ·
                      rfl

theorem cell22_3953234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3953234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953234 prefixEnd_3953234 := by exact prefixLift 3953234
  have htrace : WordTrace (prefixWord ++ tailWord_3953234) baseStart_3953234 baseEnd_3953234 := by
    simpa [prefixWord, tailWord_3953234, baseEnd_3953234] using wordTrace_append hprefix tailTrace_3953234
  have hstable : (prefixWord ++ tailWord_3953234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953234).length < 2 ^ (prefixWord ++ tailWord_3953234).sum := by decide
  have hdescent : baseEnd_3953234 < baseStart_3953234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953236 : List Nat := [2, 4, 1, 1, 1, 3, 4, 6]
def baseStart_3953236 : Nat := 118140960795 + 3953236 * 2 ^ 59
def prefixEnd_3953236 : Nat := 4983230072969 + 3 ^ 40 * 3953236 * 2
def baseEnd_3953236 : Nat := 150363719159822235531067

theorem tailTrace_3953236 : CollatzResearch.WordTrace tailWord_3953236 prefixEnd_3953236 150363719159822235531067 := by
  unfold tailWord_3953236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72093181153054302900879781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96124241537405737201173041 72093181153054302900879781)
  ·
    refine ⟨13517471466197681793914959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72093181153054302900879781 13517471466197681793914959)
    ·
      refine ⟨20276207199296522690872439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13517471466197681793914959 20276207199296522690872439)
      ·
        refine ⟨30414310798944784036308659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276207199296522690872439 30414310798944784036308659)
        ·
          refine ⟨45621466198417176054462989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30414310798944784036308659 45621466198417176054462989)
          ·
            refine ⟨17108049824406441020423621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45621466198417176054462989 17108049824406441020423621)
            ·
              refine ⟨3207759342076207691329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17108049824406441020423621 3207759342076207691329429)
              ·
                refine ⟨150363719159822235531067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3207759342076207691329429 150363719159822235531067)
                ·
                  rfl

theorem cell22_3953236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_3953236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953236 prefixEnd_3953236 := by exact prefixLift 3953236
  have htrace : WordTrace (prefixWord ++ tailWord_3953236) baseStart_3953236 baseEnd_3953236 := by
    simpa [prefixWord, tailWord_3953236, baseEnd_3953236] using wordTrace_append hprefix tailTrace_3953236
  have hstable : (prefixWord ++ tailWord_3953236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953236).length < 2 ^ (prefixWord ++ tailWord_3953236).sum := by decide
  have hdescent : baseEnd_3953236 < baseStart_3953236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953281 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 5]
def baseStart_3953281 : Nat := 118140960795 + 3953281 * 2 ^ 59
def prefixEnd_3953281 : Nat := 4983230072969 + 3 ^ 40 * 3953281 * 2
def baseEnd_3953281 : Nat := 451096292286011667468155

theorem tailTrace_3953281 : CollatzResearch.WordTrace tailWord_3953281 prefixEnd_3953281 451096292286011667468155 := by
  unfold tailWord_3953281
  simp only [CollatzResearch.WordTrace]
  refine ⟨144188003590945578487147697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96125335727297052324765131 144188003590945578487147697)
  ·
    refine ⟨108141002693209183865360773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144188003590945578487147697 108141002693209183865360773)
    ·
      refine ⟨20276438004976721974755145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108141002693209183865360773 20276438004976721974755145)
      ·
        refine ⟨15207328503732541481066359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20276438004976721974755145 15207328503732541481066359)
        ·
          refine ⟨22810992755598812221599539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15207328503732541481066359 22810992755598812221599539)
          ·
            refine ⟨34216489133398218332399309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810992755598812221599539 34216489133398218332399309)
            ·
              refine ⟨12831183425024331874649741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34216489133398218332399309 12831183425024331874649741)
              ·
                refine ⟨4811693784384124452993653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12831183425024331874649741 4811693784384124452993653)
                ·
                  refine ⟨451096292286011667468155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4811693784384124452993653 451096292286011667468155)
                  ·
                    rfl

theorem cell22_3953281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_3953281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953281 prefixEnd_3953281 := by exact prefixLift 3953281
  have htrace : WordTrace (prefixWord ++ tailWord_3953281) baseStart_3953281 baseEnd_3953281 := by
    simpa [prefixWord, tailWord_3953281, baseEnd_3953281] using wordTrace_append hprefix tailTrace_3953281
  have hstable : (prefixWord ++ tailWord_3953281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953281).length < 2 ^ (prefixWord ++ tailWord_3953281).sum := by decide
  have hdescent : baseEnd_3953281 < baseStart_3953281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953341 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3953341 : Nat := 118140960795 + 3953341 * 2 ^ 59
def prefixEnd_3953341 : Nat := 4983230072969 + 3 ^ 40 * 3953341 * 2
def baseEnd_3953341 : Nat := 1353309416084214845904281

theorem tailTrace_3953341 : CollatzResearch.WordTrace tailWord_3953341 prefixEnd_3953341 1353309416084214845904281 := by
  unfold tailWord_3953341
  simp only [CollatzResearch.WordTrace]
  refine ⟨144190191970728208734331877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96126794647152139156221251 144190191970728208734331877)
  ·
    refine ⟨27035660994511539137687227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144190191970728208734331877 27035660994511539137687227)
    ·
      refine ⟨40553491491767308706530841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27035660994511539137687227 40553491491767308706530841)
      ·
        refine ⟨30415118618825481529898131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40553491491767308706530841 30415118618825481529898131)
        ·
          refine ⟨45622677928238222294847197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30415118618825481529898131 45622677928238222294847197)
          ·
            refine ⟨17108504223089333360567699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45622677928238222294847197 17108504223089333360567699)
            ·
              refine ⟨25662756334634000040851549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17108504223089333360567699 25662756334634000040851549)
              ·
                refine ⟨9623533625487750015319331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25662756334634000040851549 9623533625487750015319331)
                ·
                  refine ⟨14435300438231625022978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9623533625487750015319331 14435300438231625022978997)
                  ·
                    refine ⟨1353309416084214845904281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14435300438231625022978997 1353309416084214845904281)
                    ·
                      rfl

theorem cell22_3953341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3953341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953341 prefixEnd_3953341 := by exact prefixLift 3953341
  have htrace : WordTrace (prefixWord ++ tailWord_3953341) baseStart_3953341 baseEnd_3953341 := by
    simpa [prefixWord, tailWord_3953341, baseEnd_3953341] using wordTrace_append hprefix tailTrace_3953341
  have hstable : (prefixWord ++ tailWord_3953341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953341).length < 2 ^ (prefixWord ++ tailWord_3953341).sum := by decide
  have hdescent : baseEnd_3953341 < baseStart_3953341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953362 : List Nat := [3, 2, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3953362 : Nat := 118140960795 + 3953362 * 2 ^ 59
def prefixEnd_3953362 : Nat := 4983230072969 + 3 ^ 40 * 3953362 * 2
def baseEnd_3953362 : Nat := 1353316604813377791129217

theorem tailTrace_3953362 : CollatzResearch.WordTrace tailWord_3953362 prefixEnd_3953362 1353316604813377791129217 := by
  unfold tailWord_3953362
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047739475913032330211585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96127305269101419547230893 36047739475913032330211585)
  ·
    refine ⟨27035804606934774247658689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36047739475913032330211585 27035804606934774247658689)
    ·
      refine ⟨20276853455201080685744017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27035804606934774247658689 20276853455201080685744017)
      ·
        refine ⟨15207640091400810514308013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20276853455201080685744017 15207640091400810514308013)
        ·
          refine ⟨5702865034275303942865505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15207640091400810514308013 5702865034275303942865505)
          ·
            refine ⟨4277148775706477957149129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702865034275303942865505 4277148775706477957149129)
            ·
              refine ⟨3207861581779858467861847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277148775706477957149129 3207861581779858467861847)
              ·
                refine ⟨4811792372669787701792771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207861581779858467861847 4811792372669787701792771)
                ·
                  refine ⟨7217688559004681552689157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811792372669787701792771 7217688559004681552689157)
                  ·
                    refine ⟨1353316604813377791129217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217688559004681552689157 1353316604813377791129217)
                    ·
                      rfl

theorem cell22_3953362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3953362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953362 prefixEnd_3953362 := by exact prefixLift 3953362
  have htrace : WordTrace (prefixWord ++ tailWord_3953362) baseStart_3953362 baseEnd_3953362 := by
    simpa [prefixWord, tailWord_3953362, baseEnd_3953362] using wordTrace_append hprefix tailTrace_3953362
  have hstable : (prefixWord ++ tailWord_3953362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953362).length < 2 ^ (prefixWord ++ tailWord_3953362).sum := by decide
  have hdescent : baseEnd_3953362 < baseStart_3953362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953375 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 2, 3]
def baseStart_3953375 : Nat := 118140960795 + 3953375 * 2 ^ 59
def prefixEnd_3953375 : Nat := 4983230072969 + 3 ^ 40 * 3953375 * 2
def baseEnd_3953375 : Nat := 1353321054979050090554177

theorem tailTrace_3953375 : CollatzResearch.WordTrace tailWord_3953375 prefixEnd_3953375 1353321054979050090554177 := by
  unfold tailWord_3953375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144191432052605032541069579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96127621368403355027379719 144191432052605032541069579)
  ·
    refine ⟨216287148078907548811604369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144191432052605032541069579 216287148078907548811604369)
    ·
      refine ⟨162215361059180661608703277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216287148078907548811604369 162215361059180661608703277)
      ·
        refine ⟨60830760397192748103263729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162215361059180661608703277 60830760397192748103263729)
        ·
          refine ⟨45623070297894561077447797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60830760397192748103263729 45623070297894561077447797)
          ·
            refine ⟨4277162840427615101010731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45623070297894561077447797 4277162840427615101010731)
            ·
              refine ⟨6415744260641422651516097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277162840427615101010731 6415744260641422651516097)
              ·
                refine ⟨4811808195481066988637073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6415744260641422651516097 4811808195481066988637073)
                ·
                  refine ⟨3608856146610800241477805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811808195481066988637073 3608856146610800241477805)
                  ·
                    refine ⟨1353321054979050090554177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608856146610800241477805 1353321054979050090554177)
                    ·
                      rfl

theorem cell22_3953375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_3953375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953375 prefixEnd_3953375 := by exact prefixLift 3953375
  have htrace : WordTrace (prefixWord ++ tailWord_3953375) baseStart_3953375 baseEnd_3953375 := by
    simpa [prefixWord, tailWord_3953375, baseEnd_3953375] using wordTrace_append hprefix tailTrace_3953375
  have hstable : (prefixWord ++ tailWord_3953375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953375).length < 2 ^ (prefixWord ++ tailWord_3953375).sum := by decide
  have hdescent : baseEnd_3953375 < baseStart_3953375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953416 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_3953416 : Nat := 118140960795 + 3953416 * 2 ^ 59
def prefixEnd_3953416 : Nat := 4983230072969 + 3 ^ 40 * 3953416 * 2
def baseEnd_3953416 : Nat := 451111696705646550093017

theorem tailTrace_3953416 : CollatzResearch.WordTrace tailWord_3953416 prefixEnd_3953416 451111696705646550093017 := by
  unfold tailWord_3953416
  simp only [CollatzResearch.WordTrace]
  refine ⟨72096463722728248271656051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96128618296970997695541401 72096463722728248271656051)
  ·
    refine ⟨108144695584092372407484077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72096463722728248271656051 108144695584092372407484077)
    ·
      refine ⟨40554260844034639652806529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108144695584092372407484077 40554260844034639652806529)
      ·
        refine ⟨30415695633025979739604897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40554260844034639652806529 30415695633025979739604897)
        ·
          refine ⟨22811771724769484804703673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30415695633025979739604897 22811771724769484804703673)
          ·
            refine ⟨17108828793577113603527755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22811771724769484804703673 17108828793577113603527755)
            ·
              refine ⟨25663243190365670405291633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17108828793577113603527755 25663243190365670405291633)
              ·
                refine ⟨19247432392774252803968725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25663243190365670405291633 19247432392774252803968725)
                ·
                  refine ⟨451111696705646550093017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19247432392774252803968725 451111696705646550093017)
                  ·
                    rfl

theorem cell22_3953416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_3953416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953416 prefixEnd_3953416 := by exact prefixLift 3953416
  have htrace : WordTrace (prefixWord ++ tailWord_3953416) baseStart_3953416 baseEnd_3953416 := by
    simpa [prefixWord, tailWord_3953416, baseEnd_3953416] using wordTrace_append hprefix tailTrace_3953416
  have hstable : (prefixWord ++ tailWord_3953416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953416).length < 2 ^ (prefixWord ++ tailWord_3953416).sum := by decide
  have hdescent : baseEnd_3953416 < baseStart_3953416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953480 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_3953480 : Nat := 118140960795 + 3953480 * 2 ^ 59
def prefixEnd_3953480 : Nat := 4983230072969 + 3 ^ 40 * 3953480 * 2
def baseEnd_3953480 : Nat := 1353356998624864816678855

theorem tailTrace_3953480 : CollatzResearch.WordTrace tailWord_3953480 prefixEnd_3953480 1353356998624864816678855 := by
  unfold tailWord_3953480
  simp only [CollatzResearch.WordTrace]
  refine ⟨72097630858612317736820947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96130174478149756982427929 72097630858612317736820947)
  ·
    refine ⟨108146446287918476605231421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72097630858612317736820947 108146446287918476605231421)
    ·
      refine ⟨40554917357969428726961783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108146446287918476605231421 40554917357969428726961783)
      ·
        refine ⟨60832376036954143090442675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40554917357969428726961783 60832376036954143090442675)
        ·
          refine ⟨91248564055431214635664013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60832376036954143090442675 91248564055431214635664013)
          ·
            refine ⟨34218211520786705488374005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91248564055431214635664013 34218211520786705488374005)
            ·
              refine ⟨3207957330073753639535063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34218211520786705488374005 3207957330073753639535063)
              ·
                refine ⟨4811935995110630459302595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207957330073753639535063 4811935995110630459302595)
                ·
                  refine ⟨7217903992665945688953893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811935995110630459302595 7217903992665945688953893)
                  ·
                    refine ⟨1353356998624864816678855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217903992665945688953893 1353356998624864816678855)
                    ·
                      rfl

theorem cell22_3953480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_3953480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953480 prefixEnd_3953480 := by exact prefixLift 3953480
  have htrace : WordTrace (prefixWord ++ tailWord_3953480) baseStart_3953480 baseEnd_3953480 := by
    simpa [prefixWord, tailWord_3953480, baseEnd_3953480] using wordTrace_append hprefix tailTrace_3953480
  have hstable : (prefixWord ++ tailWord_3953480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953480).length < 2 ^ (prefixWord ++ tailWord_3953480).sum := by decide
  have hdescent : baseEnd_3953480 < baseStart_3953480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953495 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 4]
def baseStart_3953495 : Nat := 118140960795 + 3953495 * 2 ^ 59
def prefixEnd_3953495 : Nat := 4983230072969 + 3 ^ 40 * 3953495 * 2
def baseEnd_3953495 : Nat := 451120711143803259184603

theorem tailTrace_3953495 : CollatzResearch.WordTrace tailWord_3953495 prefixEnd_3953495 451120711143803259184603 := by
  unfold tailWord_3953495
  simp only [CollatzResearch.WordTrace]
  refine ⟨144195808812170293035437939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96130539208113528690291959 144195808812170293035437939)
  ·
    refine ⟨216293713218255439553156909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144195808812170293035437939 216293713218255439553156909)
    ·
      refine ⟨81110142456845789832433841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216293713218255439553156909 81110142456845789832433841)
      ·
        refine ⟨60832606842634342374325381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81110142456845789832433841 60832606842634342374325381)
        ·
          refine ⟨11406113782993939195186009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60832606842634342374325381 11406113782993939195186009)
          ·
            refine ⟨8554585337245454396389507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11406113782993939195186009 8554585337245454396389507)
            ·
              refine ⟨12831878005868181594584261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8554585337245454396389507 12831878005868181594584261)
              ·
                refine ⟨2405977126100284048984549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12831878005868181594584261 2405977126100284048984549)
                ·
                  refine ⟨451120711143803259184603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405977126100284048984549 451120711143803259184603)
                  ·
                    rfl

theorem cell22_3953495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 4].length) (baseStart_3953495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953495 prefixEnd_3953495 := by exact prefixLift 3953495
  have htrace : WordTrace (prefixWord ++ tailWord_3953495) baseStart_3953495 baseEnd_3953495 := by
    simpa [prefixWord, tailWord_3953495, baseEnd_3953495] using wordTrace_append hprefix tailTrace_3953495
  have hstable : (prefixWord ++ tailWord_3953495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953495).length < 2 ^ (prefixWord ++ tailWord_3953495).sum := by decide
  have hdescent : baseEnd_3953495 < baseStart_3953495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953525 : List Nat := [1, 3, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3953525 : Nat := 118140960795 + 3953525 * 2 ^ 59
def prefixEnd_3953525 : Nat := 4983230072969 + 3 ^ 40 * 3953525 * 2
def baseEnd_3953525 : Nat := 1353372403044499699303717

theorem tailTrace_3953525 : CollatzResearch.WordTrace tailWord_3953525 prefixEnd_3953525 1353372403044499699303717 := by
  unfold tailWord_3953525
  simp only [CollatzResearch.WordTrace]
  refine ⟨144196903002061608159030029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96131268668041072106020019 144196903002061608159030029)
  ·
    refine ⟨54073838625773103059636261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144196903002061608159030029 54073838625773103059636261)
    ·
      refine ⟨10138844742332456823681799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54073838625773103059636261 10138844742332456823681799)
      ·
        refine ⟨15208267113498685235522699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10138844742332456823681799 15208267113498685235522699)
        ·
          refine ⟨22812400670248027853284049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208267113498685235522699 22812400670248027853284049)
          ·
            refine ⟨17109300502686020889963037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22812400670248027853284049 17109300502686020889963037)
            ·
              refine ⟨6415987688507257833736139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17109300502686020889963037 6415987688507257833736139)
              ·
                refine ⟨9623981532760886750604209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415987688507257833736139 9623981532760886750604209)
                ·
                  refine ⟨7217986149570665062953157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9623981532760886750604209 7217986149570665062953157)
                  ·
                    refine ⟨1353372403044499699303717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217986149570665062953157 1353372403044499699303717)
                    ·
                      rfl

theorem cell22_3953525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3953525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953525 prefixEnd_3953525 := by exact prefixLift 3953525
  have htrace : WordTrace (prefixWord ++ tailWord_3953525) baseStart_3953525 baseEnd_3953525 := by
    simpa [prefixWord, tailWord_3953525, baseEnd_3953525] using wordTrace_append hprefix tailTrace_3953525
  have hstable : (prefixWord ++ tailWord_3953525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953525).length < 2 ^ (prefixWord ++ tailWord_3953525).sum := by decide
  have hdescent : baseEnd_3953525 < baseStart_3953525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953536 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_3953536 : Nat := 118140960795 + 3953536 * 2 ^ 59
def prefixEnd_3953536 : Nat := 4983230072969 + 3 ^ 40 * 3953536 * 2
def baseEnd_3953536 : Nat := 1353376168569299337278683

theorem tailTrace_3953536 : CollatzResearch.WordTrace tailWord_3953536 prefixEnd_3953536 1353376168569299337278683 := by
  unfold tailWord_3953536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72098652102510878518840231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96131536136681171358453641 72098652102510878518840231)
  ·
    refine ⟨108147978153766317778260347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72098652102510878518840231 108147978153766317778260347)
    ·
      refine ⟨162221967230649476667390521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108147978153766317778260347 162221967230649476667390521)
      ·
        refine ⟨121666475422987107500542891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162221967230649476667390521 121666475422987107500542891)
        ·
          refine ⟨182499713134480661250814337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121666475422987107500542891 182499713134480661250814337)
          ·
            refine ⟨136874784850860495938110753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182499713134480661250814337 136874784850860495938110753)
            ·
              refine ⟨102656088638145371953583065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136874784850860495938110753 102656088638145371953583065)
              ·
                refine ⟨76992066478609028965187299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102656088638145371953583065 76992066478609028965187299)
                ·
                  refine ⟨115488099717913543447780949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76992066478609028965187299 115488099717913543447780949)
                  ·
                    refine ⟨1353376168569299337278683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115488099717913543447780949 1353376168569299337278683)
                    ·
                      rfl

theorem cell22_3953536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_3953536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953536 prefixEnd_3953536 := by exact prefixLift 3953536
  have htrace : WordTrace (prefixWord ++ tailWord_3953536) baseStart_3953536 baseEnd_3953536 := by
    simpa [prefixWord, tailWord_3953536, baseEnd_3953536] using wordTrace_append hprefix tailTrace_3953536
  have hstable : (prefixWord ++ tailWord_3953536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953536).length < 2 ^ (prefixWord ++ tailWord_3953536).sum := by decide
  have hdescent : baseEnd_3953536 < baseStart_3953536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953568 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_3953568 : Nat := 118140960795 + 3953568 * 2 ^ 59
def prefixEnd_3953568 : Nat := 4983230072969 + 3 ^ 40 * 3953568 * 2
def baseEnd_3953568 : Nat := 451129040941087306826195

theorem tailTrace_3953568 : CollatzResearch.WordTrace tailWord_3953568 prefixEnd_3953568 451129040941087306826195 := by
  unfold tailWord_3953568
  simp only [CollatzResearch.WordTrace]
  refine ⟨72099235670452913251422679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96132314227270551001896905 72099235670452913251422679)
  ·
    refine ⟨108148853505679369877134019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72099235670452913251422679 108148853505679369877134019)
    ·
      refine ⟨162223280258519054815701029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108148853505679369877134019 162223280258519054815701029)
      ·
        refine ⟨30416865048472322777943943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162223280258519054815701029 30416865048472322777943943)
        ·
          refine ⟨45625297572708484166915915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30416865048472322777943943 45625297572708484166915915)
          ·
            refine ⟨68437946359062726250373873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45625297572708484166915915 68437946359062726250373873)
            ·
              refine ⟨51328459769297044687780405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68437946359062726250373873 51328459769297044687780405)
              ·
                refine ⟨4812043103371597939479413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51328459769297044687780405 4812043103371597939479413)
                ·
                  refine ⟨451129040941087306826195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812043103371597939479413 451129040941087306826195)
                  ·
                    rfl

theorem cell22_3953568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_3953568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953568 prefixEnd_3953568 := by exact prefixLift 3953568
  have htrace : WordTrace (prefixWord ++ tailWord_3953568) baseStart_3953568 baseEnd_3953568 := by
    simpa [prefixWord, tailWord_3953568, baseEnd_3953568] using wordTrace_append hprefix tailTrace_3953568
  have hstable : (prefixWord ++ tailWord_3953568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953568).length < 2 ^ (prefixWord ++ tailWord_3953568).sum := by decide
  have hdescent : baseEnd_3953568 < baseStart_3953568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953660 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3953660 : Nat := 118140960795 + 3953660 * 2 ^ 59
def prefixEnd_3953660 : Nat := 4983230072969 + 3 ^ 40 * 3953660 * 2
def baseEnd_3953660 : Nat := 1353418616303404347178303

theorem tailTrace_3953660 : CollatzResearch.WordTrace tailWord_3953660 prefixEnd_3953660 1353418616303404347178303 := by
  unfold tailWord_3953660
  simp only [CollatzResearch.WordTrace]
  refine ⟨72100913428286263107597217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96134551237715017476796289 72100913428286263107597217)
  ·
    refine ⟨54075685071214697330697913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72100913428286263107597217 54075685071214697330697913)
    ·
      refine ⟨40556763803411022998023435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54075685071214697330697913 40556763803411022998023435)
      ·
        refine ⟨60835145705116534497035153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40556763803411022998023435 60835145705116534497035153)
        ·
          refine ⟨45626359278837400872776365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60835145705116534497035153 45626359278837400872776365)
          ·
            refine ⟨17109884729564025327291137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45626359278837400872776365 17109884729564025327291137)
            ·
              refine ⟨12832413547173018995468353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17109884729564025327291137 12832413547173018995468353)
              ·
                refine ⟨9624310160379764246601265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12832413547173018995468353 9624310160379764246601265)
                ·
                  refine ⟨7218232620284823184950949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9624310160379764246601265 7218232620284823184950949)
                  ·
                    refine ⟨1353418616303404347178303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218232620284823184950949 1353418616303404347178303)
                    ·
                      rfl

theorem cell22_3953660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3953660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953660 prefixEnd_3953660 := by exact prefixLift 3953660
  have htrace : WordTrace (prefixWord ++ tailWord_3953660) baseStart_3953660 baseEnd_3953660 := by
    simpa [prefixWord, tailWord_3953660, baseEnd_3953660] using wordTrace_append hprefix tailTrace_3953660
  have hstable : (prefixWord ++ tailWord_3953660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953660).length < 2 ^ (prefixWord ++ tailWord_3953660).sum := by decide
  have hdescent : baseEnd_3953660 < baseStart_3953660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953675 : List Nat := [1, 1, 1, 1, 6, 4, 1, 7]
def baseStart_3953675 : Nat := 118140960795 + 3953675 * 2 ^ 59
def prefixEnd_3953675 : Nat := 4983230072969 + 3 ^ 40 * 3953675 * 2
def baseEnd_3953675 : Nat := 150380416789994367561473

theorem tailTrace_3953675 : CollatzResearch.WordTrace tailWord_3953675 prefixEnd_3953675 150380416789994367561473 := by
  unfold tailWord_3953675
  simp only [CollatzResearch.WordTrace]
  refine ⟨144202373951518183776990479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96134915967678789184660319 144202373951518183776990479)
  ·
    refine ⟨216303560927277275665485719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144202373951518183776990479 216303560927277275665485719)
    ·
      refine ⟨324455341390915913498228579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216303560927277275665485719 324455341390915913498228579)
      ·
        refine ⟨486683012086373870247342869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324455341390915913498228579 486683012086373870247342869)
        ·
          refine ⟨22813266191548775167844197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 486683012086373870247342869 22813266191548775167844197)
          ·
            refine ⟨4277487410915395343970787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22813266191548775167844197 4277487410915395343970787)
            ·
              refine ⟨6416231116373093015956181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277487410915395343970787 6416231116373093015956181)
              ·
                refine ⟨150380416789994367561473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6416231116373093015956181 150380416789994367561473)
                ·
                  rfl

theorem cell22_3953675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 7].length) (baseStart_3953675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953675 prefixEnd_3953675 := by exact prefixLift 3953675
  have htrace : WordTrace (prefixWord ++ tailWord_3953675) baseStart_3953675 baseEnd_3953675 := by
    simpa [prefixWord, tailWord_3953675, baseEnd_3953675] using wordTrace_append hprefix tailTrace_3953675
  have hstable : (prefixWord ++ tailWord_3953675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953675).length < 2 ^ (prefixWord ++ tailWord_3953675).sum := by decide
  have hdescent : baseEnd_3953675 < baseStart_3953675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953692 : List Nat := [2, 2, 3, 1, 4, 1, 3, 6]
def baseStart_3953692 : Nat := 118140960795 + 3953692 * 2 ^ 59
def prefixEnd_3953692 : Nat := 4983230072969 + 3 ^ 40 * 3953692 * 2
def baseEnd_3953692 : Nat := 150381063395262992264245

theorem tailTrace_3953692 : CollatzResearch.WordTrace tailWord_3953692 prefixEnd_3953692 150381063395262992264245 := by
  unfold tailWord_3953692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72101496996228297840179665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96135329328304397120239553 72101496996228297840179665)
  ·
    refine ⟨54076122747171223380134749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72101496996228297840179665 54076122747171223380134749)
    ·
      refine ⟨20278546030189208767550531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54076122747171223380134749 20278546030189208767550531)
      ·
        refine ⟨30417819045283813151325797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278546030189208767550531 30417819045283813151325797)
        ·
          refine ⟨5703341070990714965873587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30417819045283813151325797 5703341070990714965873587)
          ·
            refine ⟨8555011606486072448810381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703341070990714965873587 8555011606486072448810381)
            ·
              refine ⟨3208129352432277168303893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8555011606486072448810381 3208129352432277168303893)
              ·
                refine ⟨150381063395262992264245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3208129352432277168303893 150381063395262992264245)
                ·
                  rfl

theorem cell22_3953692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_3953692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953692 prefixEnd_3953692 := by exact prefixLift 3953692
  have htrace : WordTrace (prefixWord ++ tailWord_3953692) baseStart_3953692 baseEnd_3953692 := by
    simpa [prefixWord, tailWord_3953692, baseEnd_3953692] using wordTrace_append hprefix tailTrace_3953692
  have hstable : (prefixWord ++ tailWord_3953692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953692).length < 2 ^ (prefixWord ++ tailWord_3953692).sum := by decide
  have hdescent : baseEnd_3953692 < baseStart_3953692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953720 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_3953720 : Nat := 118140960795 + 3953720 * 2 ^ 59
def prefixEnd_3953720 : Nat := 4983230072969 + 3 ^ 40 * 3953720 * 2
def baseEnd_3953720 : Nat := 451146385176528063559373

theorem tailTrace_3953720 : CollatzResearch.WordTrace tailWord_3953720 prefixEnd_3953720 451146385176528063559373 := by
  unfold tailWord_3953720
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102007618177578231189307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96136010157570104308252409 72102007618177578231189307)
  ·
    refine ⟨108153011427266367346783961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72102007618177578231189307 108153011427266367346783961)
    ·
      refine ⟨81114758570449775510087971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108153011427266367346783961 81114758570449775510087971)
      ·
        refine ⟨121672137855674663265131957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81114758570449775510087971 121672137855674663265131957)
        ·
          refine ⟨11406762923969499681106121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121672137855674663265131957 11406762923969499681106121)
          ·
            refine ⟨8555072192977124760829591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11406762923969499681106121 8555072192977124760829591)
            ·
              refine ⟨12832608289465687141244387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8555072192977124760829591 12832608289465687141244387)
              ·
                refine ⟨19248912434198530711866581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12832608289465687141244387 19248912434198530711866581)
                ·
                  refine ⟨451146385176528063559373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19248912434198530711866581 451146385176528063559373)
                  ·
                    rfl

theorem cell22_3953720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_3953720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953720 prefixEnd_3953720 := by exact prefixLift 3953720
  have htrace : WordTrace (prefixWord ++ tailWord_3953720) baseStart_3953720 baseEnd_3953720 := by
    simpa [prefixWord, tailWord_3953720, baseEnd_3953720] using wordTrace_append hprefix tailTrace_3953720
  have hstable : (prefixWord ++ tailWord_3953720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953720).length < 2 ^ (prefixWord ++ tailWord_3953720).sum := by decide
  have hdescent : baseEnd_3953720 < baseStart_3953720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953724 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_3953724 : Nat := 118140960795 + 3953724 * 2 ^ 59
def prefixEnd_3953724 : Nat := 4983230072969 + 3 ^ 40 * 3953724 * 2
def baseEnd_3953724 : Nat := 1353440524811329513578107

theorem tailTrace_3953724 : CollatzResearch.WordTrace tailWord_3953724 prefixEnd_3953724 1353440524811329513578107 := by
  unfold tailWord_3953724
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102080564170332572762113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96136107418893776763682817 72102080564170332572762113)
  ·
    refine ⟨54076560423127749429571585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72102080564170332572762113 54076560423127749429571585)
    ·
      refine ⟨40557420317345812072178689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54076560423127749429571585 40557420317345812072178689)
      ·
        refine ⟨30418065238009359054134017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40557420317345812072178689 30418065238009359054134017)
        ·
          refine ⟨22813548928507019290600513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30418065238009359054134017 22813548928507019290600513)
          ·
            refine ⟨17110161696380264467950385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22813548928507019290600513 17110161696380264467950385)
            ·
              refine ⟨12832621272285198350962789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110161696380264467950385 12832621272285198350962789)
              ·
                refine ⟨2406116488553474690805523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12832621272285198350962789 2406116488553474690805523)
                ·
                  refine ⟨3609174732830212036208285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406116488553474690805523 3609174732830212036208285)
                  ·
                    refine ⟨1353440524811329513578107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609174732830212036208285 1353440524811329513578107)
                    ·
                      rfl

theorem cell22_3953724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_3953724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953724 prefixEnd_3953724 := by exact prefixLift 3953724
  have htrace : WordTrace (prefixWord ++ tailWord_3953724) baseStart_3953724 baseEnd_3953724 := by
    simpa [prefixWord, tailWord_3953724, baseEnd_3953724] using wordTrace_append hprefix tailTrace_3953724
  have hstable : (prefixWord ++ tailWord_3953724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953724).length < 2 ^ (prefixWord ++ tailWord_3953724).sum := by decide
  have hdescent : baseEnd_3953724 < baseStart_3953724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953735 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3953735 : Nat := 118140960795 + 3953735 * 2 ^ 59
def prefixEnd_3953735 : Nat := 4983230072969 + 3 ^ 40 * 3953735 * 2
def baseEnd_3953735 : Nat := 1353444290336129151553073

theorem tailTrace_3953735 : CollatzResearch.WordTrace tailWord_3953735 prefixEnd_3953735 1353444290336129151553073 := by
  unfold tailWord_3953735
  simp only [CollatzResearch.WordTrace]
  refine ⟨144204562331300814024174659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96136374887533876016116439 144204562331300814024174659)
  ·
    refine ⟨216306843496951221036261989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144204562331300814024174659 216306843496951221036261989)
    ·
      refine ⟨40557533155678353944299123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216306843496951221036261989 40557533155678353944299123)
      ·
        refine ⟨60836299733517530916448685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40557533155678353944299123 60836299733517530916448685)
        ·
          refine ⟨22813612400069074093668257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60836299733517530916448685 22813612400069074093668257)
          ·
            refine ⟨17110209300051805570251193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22813612400069074093668257 17110209300051805570251193)
            ·
              refine ⟨12832656975038854177688395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110209300051805570251193 12832656975038854177688395)
              ·
                refine ⟨19248985462558281266532593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12832656975038854177688395 19248985462558281266532593)
                ·
                  refine ⟨14436739096918710949899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19248985462558281266532593 14436739096918710949899445)
                  ·
                    refine ⟨1353444290336129151553073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14436739096918710949899445 1353444290336129151553073)
                    ·
                      rfl

theorem cell22_3953735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3953735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953735 prefixEnd_3953735 := by exact prefixLift 3953735
  have htrace : WordTrace (prefixWord ++ tailWord_3953735) baseStart_3953735 baseEnd_3953735 := by
    simpa [prefixWord, tailWord_3953735, baseEnd_3953735] using wordTrace_append hprefix tailTrace_3953735
  have hstable : (prefixWord ++ tailWord_3953735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953735).length < 2 ^ (prefixWord ++ tailWord_3953735).sum := by decide
  have hdescent : baseEnd_3953735 < baseStart_3953735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953767 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3953767 : Nat := 118140960795 + 3953767 * 2 ^ 59
def prefixEnd_3953767 : Nat := 4983230072969 + 3 ^ 40 * 3953767 * 2
def baseEnd_3953767 : Nat := 1353455244590091734752975

theorem tailTrace_3953767 : CollatzResearch.WordTrace tailWord_3953767 prefixEnd_3953767 1353455244590091734752975 := by
  unfold tailWord_3953767
  simp only [CollatzResearch.WordTrace]
  refine ⟨144205729467184883489339555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96137152978123255659559703 144205729467184883489339555)
  ·
    refine ⟨216308594200777325234009333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144205729467184883489339555 216308594200777325234009333)
    ·
      refine ⟨20278930706322874240688375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216308594200777325234009333 20278930706322874240688375)
      ·
        refine ⟨30418396059484311361032563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20278930706322874240688375 30418396059484311361032563)
        ·
          refine ⟨45627594089226467041548845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30418396059484311361032563 45627594089226467041548845)
          ·
            refine ⟨17110347783459925140580817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45627594089226467041548845 17110347783459925140580817)
            ·
              refine ⟨12832760837594943855435613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17110347783459925140580817 12832760837594943855435613)
              ·
                refine ⟨4812285314098103945788355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12832760837594943855435613 4812285314098103945788355)
                ·
                  refine ⟨7218427971147155918682533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812285314098103945788355 7218427971147155918682533)
                  ·
                    refine ⟨1353455244590091734752975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218427971147155918682533 1353455244590091734752975)
                    ·
                      rfl

theorem cell22_3953767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3953767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953767 prefixEnd_3953767 := by exact prefixLift 3953767
  have htrace : WordTrace (prefixWord ++ tailWord_3953767) baseStart_3953767 baseEnd_3953767 := by
    simpa [prefixWord, tailWord_3953767, baseEnd_3953767] using wordTrace_append hprefix tailTrace_3953767
  have hstable : (prefixWord ++ tailWord_3953767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953767).length < 2 ^ (prefixWord ++ tailWord_3953767).sum := by decide
  have hdescent : baseEnd_3953767 < baseStart_3953767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953795 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_3953795 : Nat := 118140960795 + 3953795 * 2 ^ 59
def prefixEnd_3953795 : Nat := 4983230072969 + 3 ^ 40 * 3953795 * 2
def baseEnd_3953795 : Nat := 1353464829562308995052889

theorem tailTrace_3953795 : CollatzResearch.WordTrace tailWord_3953795 prefixEnd_3953795 1353464829562308995052889 := by
  unfold tailWord_3953795
  simp only [CollatzResearch.WordTrace]
  refine ⟨144206750711083444271358839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96137833807388962847572559 144206750711083444271358839)
  ·
    refine ⟨216310126066625166407038259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144206750711083444271358839 216310126066625166407038259)
    ·
      refine ⟨324465189099937749610557389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216310126066625166407038259 324465189099937749610557389)
      ·
        refine ⟨121674445912476656103959021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324465189099937749610557389 121674445912476656103959021)
        ·
          refine ⟨45627917217178746038984633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121674445912476656103959021 45627917217178746038984633)
          ·
            refine ⟨34220937912884059529238475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45627917217178746038984633 34220937912884059529238475)
            ·
              refine ⟨51331406869326089293857713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34220937912884059529238475 51331406869326089293857713)
              ·
                refine ⟨38498555151994566970393285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51331406869326089293857713 38498555151994566970393285)
                ·
                  refine ⟨7218479090998981306948741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38498555151994566970393285 7218479090998981306948741)
                  ·
                    refine ⟨1353464829562308995052889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218479090998981306948741 1353464829562308995052889)
                    ·
                      rfl

theorem cell22_3953795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_3953795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953795 prefixEnd_3953795 := by exact prefixLift 3953795
  have htrace : WordTrace (prefixWord ++ tailWord_3953795) baseStart_3953795 baseEnd_3953795 := by
    simpa [prefixWord, tailWord_3953795, baseEnd_3953795] using wordTrace_append hprefix tailTrace_3953795
  have hstable : (prefixWord ++ tailWord_3953795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953795).length < 2 ^ (prefixWord ++ tailWord_3953795).sum := by decide
  have hdescent : baseEnd_3953795 < baseStart_3953795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953831 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3953831 : Nat := 118140960795 + 3953831 * 2 ^ 59
def prefixEnd_3953831 : Nat := 4983230072969 + 3 ^ 40 * 3953831 * 2
def baseEnd_3953831 : Nat := 1353477153098016901152779

theorem tailTrace_3953831 : CollatzResearch.WordTrace tailWord_3953831 prefixEnd_3953831 1353477153098016901152779 := by
  unfold tailWord_3953831
  simp only [CollatzResearch.WordTrace]
  refine ⟨144208063738953022419669347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96138709159302014946446231 144208063738953022419669347)
  ·
    refine ⟨216312095608429533629504021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144208063738953022419669347 216312095608429533629504021)
    ·
      refine ⟨10139629481645134388883001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 216312095608429533629504021 10139629481645134388883001)
      ·
        refine ⟨7604722111233850791662251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10139629481645134388883001 7604722111233850791662251)
        ·
          refine ⟨11407083166850776187493377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604722111233850791662251 11407083166850776187493377)
          ·
            refine ⟨8555312375138082140620033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11407083166850776187493377 8555312375138082140620033)
            ·
              refine ⟨6416484281353561605465025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555312375138082140620033 6416484281353561605465025)
              ·
                refine ⟨4812363211015171204098769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416484281353561605465025 4812363211015171204098769)
                ·
                  refine ⟨3609272408261378403074077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4812363211015171204098769 3609272408261378403074077)
                  ·
                    refine ⟨1353477153098016901152779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609272408261378403074077 1353477153098016901152779)
                    ·
                      rfl

theorem cell22_3953831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3953831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953831 prefixEnd_3953831 := by exact prefixLift 3953831
  have htrace : WordTrace (prefixWord ++ tailWord_3953831) baseStart_3953831 baseEnd_3953831 := by
    simpa [prefixWord, tailWord_3953831, baseEnd_3953831] using wordTrace_append hprefix tailTrace_3953831
  have hstable : (prefixWord ++ tailWord_3953831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953831).length < 2 ^ (prefixWord ++ tailWord_3953831).sum := by decide
  have hdescent : baseEnd_3953831 < baseStart_3953831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953889 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 5]
def baseStart_3953889 : Nat := 118140960795 + 3953889 * 2 ^ 59
def prefixEnd_3953889 : Nat := 4983230072969 + 3 ^ 40 * 3953889 * 2
def baseEnd_3953889 : Nat := 451165669227774694400867

theorem tailTrace_3953889 : CollatzResearch.WordTrace tailWord_3953889 prefixEnd_3953889 451165669227774694400867 := by
  unfold tailWord_3953889
  simp only [CollatzResearch.WordTrace]
  refine ⟨144210179172742898325280721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96140119448495265550187147 144210179172742898325280721)
  ·
    refine ⟨108157634379557173743960541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144210179172742898325280721 108157634379557173743960541)
    ·
      refine ⟨40559112892333940153985203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108157634379557173743960541 40559112892333940153985203)
      ·
        refine ⟨60838669338500910230977805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40559112892333940153985203 60838669338500910230977805)
        ·
          refine ⟨22814501001937841336616677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60838669338500910230977805 22814501001937841336616677)
          ·
            refine ⟨4277718937863345250615627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22814501001937841336616677 4277718937863345250615627)
            ·
              refine ⟨6416578406795017875923441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277718937863345250615627 6416578406795017875923441)
              ·
                refine ⟨4812433805096263406942581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416578406795017875923441 4812433805096263406942581)
                ·
                  refine ⟨451165669227774694400867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812433805096263406942581 451165669227774694400867)
                  ·
                    rfl

theorem cell22_3953889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_3953889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953889 prefixEnd_3953889 := by exact prefixLift 3953889
  have htrace : WordTrace (prefixWord ++ tailWord_3953889) baseStart_3953889 baseEnd_3953889 := by
    simpa [prefixWord, tailWord_3953889, baseEnd_3953889] using wordTrace_append hprefix tailTrace_3953889
  have hstable : (prefixWord ++ tailWord_3953889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953889).length < 2 ^ (prefixWord ++ tailWord_3953889).sum := by decide
  have hdescent : baseEnd_3953889 < baseStart_3953889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953902 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3953902 : Nat := 118140960795 + 3953902 * 2 ^ 59
def prefixEnd_3953902 : Nat := 4983230072969 + 3 ^ 40 * 3953902 * 2
def baseEnd_3953902 : Nat := 1353501457848996382627561

theorem tailTrace_3953902 : CollatzResearch.WordTrace tailWord_3953902 prefixEnd_3953902 1353501457848996382627561 := by
  unfold tailWord_3953902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18026331665211975193187995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96140435547797201030335973 18026331665211975193187995)
  ·
    refine ⟨27039497497817962789781993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18026331665211975193187995 27039497497817962789781993)
    ·
      refine ⟨20279623123363472092336495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27039497497817962789781993 20279623123363472092336495)
      ·
        refine ⟨30419434685045208138504743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20279623123363472092336495 30419434685045208138504743)
        ·
          refine ⟨45629152027567812207757115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30419434685045208138504743 45629152027567812207757115)
          ·
            refine ⟨68443728041351718311635673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45629152027567812207757115 68443728041351718311635673)
            ·
              refine ⟨51332796031013788733726755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68443728041351718311635673 51332796031013788733726755)
              ·
                refine ⟨76999194046520683100590133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51332796031013788733726755 76999194046520683100590133)
                ·
                  refine ⟨7218674441861314040680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76999194046520683100590133 7218674441861314040680325)
                  ·
                    refine ⟨1353501457848996382627561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218674441861314040680325 1353501457848996382627561)
                    ·
                      rfl

theorem cell22_3953902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3953902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953902 prefixEnd_3953902 := by exact prefixLift 3953902
  have htrace : WordTrace (prefixWord ++ tailWord_3953902) baseStart_3953902 baseEnd_3953902 := by
    simpa [prefixWord, tailWord_3953902, baseEnd_3953902] using wordTrace_append hprefix tailTrace_3953902
  have hstable : (prefixWord ++ tailWord_3953902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953902).length < 2 ^ (prefixWord ++ tailWord_3953902).sum := by decide
  have hdescent : baseEnd_3953902 < baseStart_3953902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953906 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_3953906 : Nat := 118140960795 + 3953906 * 2 ^ 59
def prefixEnd_3953906 : Nat := 4983230072969 + 3 ^ 40 * 3953906 * 2
def baseEnd_3953906 : Nat := 451167609043580568509183

theorem tailTrace_3953906 : CollatzResearch.WordTrace tailWord_3953906 prefixEnd_3953906 451167609043580568509183 := by
  unfold tailWord_3953906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052699803420327557162393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96140532809120873485766381 36052699803420327557162393)
  ·
    refine ⟨27039524852565245667871795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36052699803420327557162393 27039524852565245667871795)
    ·
      refine ⟨40559287278847868501807693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27039524852565245667871795 40559287278847868501807693)
      ·
        refine ⟨15209732729567950688177885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40559287278847868501807693 15209732729567950688177885)
        ·
          refine ⟨5703649773587981508066707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15209732729567950688177885 5703649773587981508066707)
          ·
            refine ⟨8555474660381972262100061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703649773587981508066707 8555474660381972262100061)
            ·
              refine ⟨3208302997643239598287523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8555474660381972262100061 3208302997643239598287523)
              ·
                refine ⟨4812454496464859397431285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208302997643239598287523 4812454496464859397431285)
                ·
                  refine ⟨451167609043580568509183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812454496464859397431285 451167609043580568509183)
                  ·
                    rfl

theorem cell22_3953906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_3953906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953906 prefixEnd_3953906 := by exact prefixLift 3953906
  have htrace : WordTrace (prefixWord ++ tailWord_3953906) baseStart_3953906 baseEnd_3953906 := by
    simpa [prefixWord, tailWord_3953906, baseEnd_3953906] using wordTrace_append hprefix tailTrace_3953906
  have hstable : (prefixWord ++ tailWord_3953906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953906).length < 2 ^ (prefixWord ++ tailWord_3953906).sum := by decide
  have hdescent : baseEnd_3953906 < baseStart_3953906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953919 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 1, 4]
def baseStart_3953919 : Nat := 118140960795 + 3953919 * 2 ^ 59
def prefixEnd_3953919 : Nat := 4983230072969 + 3 ^ 40 * 3953919 * 2
def baseEnd_3953919 : Nat := 1353507277296414004952509

theorem tailTrace_3953919 : CollatzResearch.WordTrace tailWord_3953919 prefixEnd_3953919 1353507277296414004952509 := by
  unfold tailWord_3953919
  simp only [CollatzResearch.WordTrace]
  refine ⟨144211273362634213448872811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96140848908422808965915207 144211273362634213448872811)
  ·
    refine ⟨216316910043951320173309217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144211273362634213448872811 216316910043951320173309217)
    ·
      refine ⟨162237682532963490129981913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216316910043951320173309217 162237682532963490129981913)
      ·
        refine ⟨121678261899722617597486435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162237682532963490129981913 121678261899722617597486435)
        ·
          refine ⟨182517392849583926396229653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121678261899722617597486435 182517392849583926396229653)
          ·
            refine ⟨8555502789824246549823265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182517392849583926396229653 8555502789824246549823265)
            ·
              refine ⟨6416627092368184912367449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555502789824246549823265 6416627092368184912367449)
              ·
                refine ⟨4812470319276138684275587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416627092368184912367449 4812470319276138684275587)
                ·
                  refine ⟨7218705478914208026413381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812470319276138684275587 7218705478914208026413381)
                  ·
                    refine ⟨1353507277296414004952509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7218705478914208026413381 1353507277296414004952509)
                    ·
                      rfl

theorem cell22_3953919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_3953919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953919 prefixEnd_3953919 := by exact prefixLift 3953919
  have htrace : WordTrace (prefixWord ++ tailWord_3953919) baseStart_3953919 baseEnd_3953919 := by
    simpa [prefixWord, tailWord_3953919, baseEnd_3953919] using wordTrace_append hprefix tailTrace_3953919
  have hstable : (prefixWord ++ tailWord_3953919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953919).length < 2 ^ (prefixWord ++ tailWord_3953919).sum := by decide
  have hdescent : baseEnd_3953919 < baseStart_3953919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3953951 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 6]
def baseStart_3953951 : Nat := 118140960795 + 3953951 * 2 ^ 59
def prefixEnd_3953951 : Nat := 4983230072969 + 3 ^ 40 * 3953951 * 2
def baseEnd_3953951 : Nat := 451172743850125529384137

theorem tailTrace_3953951 : CollatzResearch.WordTrace tailWord_3953951 prefixEnd_3953951 451172743850125529384137 := by
  unfold tailWord_3953951
  simp only [CollatzResearch.WordTrace]
  refine ⟨144212440498518282914037707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96141626999012188609358471 144212440498518282914037707)
  ·
    refine ⟨216318660747777424371056561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144212440498518282914037707 216318660747777424371056561)
    ·
      refine ⟨162238995560833068278292421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216318660747777424371056561 162238995560833068278292421)
      ·
        refine ⟨30419811667656200302179829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162238995560833068278292421 30419811667656200302179829)
        ·
          refine ⟨2851857343842768778329359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30419811667656200302179829 2851857343842768778329359)
          ·
            refine ⟨4277786015764153167494039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851857343842768778329359 4277786015764153167494039)
            ·
              refine ⟨6416679023646229751241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277786015764153167494039 6416679023646229751241059)
              ·
                refine ⟨9625018535469344626861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416679023646229751241059 9625018535469344626861589)
                ·
                  refine ⟨451172743850125529384137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9625018535469344626861589 451172743850125529384137)
                  ·
                    rfl

theorem cell22_3953951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 6].length) (baseStart_3953951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3953951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3953951 prefixEnd_3953951 := by exact prefixLift 3953951
  have htrace : WordTrace (prefixWord ++ tailWord_3953951) baseStart_3953951 baseEnd_3953951 := by
    simpa [prefixWord, tailWord_3953951, baseEnd_3953951] using wordTrace_append hprefix tailTrace_3953951
  have hstable : (prefixWord ++ tailWord_3953951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3953951).length < 2 ^ (prefixWord ++ tailWord_3953951).sum := by decide
  have hdescent : baseEnd_3953951 < baseStart_3953951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3953951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954101 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3954101 : Nat := 118140960795 + 3954101 * 2 ^ 59
def prefixEnd_3954101 : Nat := 4983230072969 + 3 ^ 40 * 3954101 * 2
def baseEnd_3954101 : Nat := 1353569579615826196901951

theorem tailTrace_3954101 : CollatzResearch.WordTrace tailWord_3954101 prefixEnd_3954101 1353569579615826196901951 := by
  unfold tailWord_3954101
  simp only [CollatzResearch.WordTrace]
  refine ⟨144217911447974858531998157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96145274298649905687998771 144217911447974858531998157)
  ·
    refine ⟨54081716792990571949499309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144217911447974858531998157 54081716792990571949499309)
    ·
      refine ⟨20280643797371464481062241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54081716792990571949499309 20280643797371464481062241)
      ·
        refine ⟨15210482848028598360796681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20280643797371464481062241 15210482848028598360796681)
        ·
          refine ⟨11407862136021448770597511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210482848028598360796681 11407862136021448770597511)
          ·
            refine ⟨17111793204032173155896267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407862136021448770597511 17111793204032173155896267)
            ·
              refine ⟨25667689806048259733844401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17111793204032173155896267 25667689806048259733844401)
              ·
                refine ⟨19250767354536194800383301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25667689806048259733844401 19250767354536194800383301)
                ·
                  refine ⟨3609518878975536525071869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19250767354536194800383301 3609518878975536525071869)
                  ·
                    refine ⟨1353569579615826196901951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609518878975536525071869 1353569579615826196901951)
                    ·
                      rfl

theorem cell22_3954101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3954101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954101 prefixEnd_3954101 := by exact prefixLift 3954101
  have htrace : WordTrace (prefixWord ++ tailWord_3954101) baseStart_3954101 baseEnd_3954101 := by
    simpa [prefixWord, tailWord_3954101, baseEnd_3954101] using wordTrace_append hprefix tailTrace_3954101
  have hstable : (prefixWord ++ tailWord_3954101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954101).length < 2 ^ (prefixWord ++ tailWord_3954101).sum := by decide
  have hdescent : baseEnd_3954101 < baseStart_3954101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954116 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3954116 : Nat := 118140960795 + 3954116 * 2 ^ 59
def prefixEnd_3954116 : Nat := 4983230072969 + 3 ^ 40 * 3954116 * 2
def baseEnd_3954116 : Nat := 1353574714422371157776905

theorem tailTrace_3954116 : CollatzResearch.WordTrace tailWord_3954116 prefixEnd_3954116 1353574714422371157776905 := by
  unfold tailWord_3954116
  simp only [CollatzResearch.WordTrace]
  refine ⟨72109229271460258046897101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96145639028613677395862801 72109229271460258046897101)
  ·
    refine ⟨27040960976797596767586413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72109229271460258046897101 27040960976797596767586413)
    ·
      refine ⟨10140360366299098787844905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27040960976797596767586413 10140360366299098787844905)
      ·
        refine ⟨7605270274724324090883679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10140360366299098787844905 7605270274724324090883679)
        ·
          refine ⟨11407905412086486136325519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7605270274724324090883679 11407905412086486136325519)
          ·
            refine ⟨17111858118129729204488279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11407905412086486136325519 17111858118129729204488279)
            ·
              refine ⟨25667787177194593806732419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17111858118129729204488279 25667787177194593806732419)
              ·
                refine ⟨38501680765791890710098629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25667787177194593806732419 38501680765791890710098629)
                ·
                  refine ⟨7219065143585979508143493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38501680765791890710098629 7219065143585979508143493)
                  ·
                    refine ⟨1353574714422371157776905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7219065143585979508143493 1353574714422371157776905)
                    ·
                      rfl

theorem cell22_3954116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3954116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954116 prefixEnd_3954116 := by exact prefixLift 3954116
  have htrace : WordTrace (prefixWord ++ tailWord_3954116) baseStart_3954116 baseEnd_3954116 := by
    simpa [prefixWord, tailWord_3954116, baseEnd_3954116] using wordTrace_append hprefix tailTrace_3954116
  have hstable : (prefixWord ++ tailWord_3954116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954116).length < 2 ^ (prefixWord ++ tailWord_3954116).sum := by decide
  have hdescent : baseEnd_3954116 < baseStart_3954116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954182 : List Nat := [6, 2, 1, 1, 2, 2, 1, 7]
def baseStart_3954182 : Nat := 118140960795 + 3954182 * 2 ^ 59
def prefixEnd_3954182 : Nat := 4983230072969 + 3 ^ 40 * 3954182 * 2
def baseEnd_3954182 : Nat := 150399700841240998402967

theorem tailTrace_3954182 : CollatzResearch.WordTrace tailWord_3954182 prefixEnd_3954182 150399700841240998402967 := by
  unfold tailWord_3954182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506902055021294042678025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96147243840454272910464533 4506902055021294042678025)
  ·
    refine ⟨3380176541265970532008519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4506902055021294042678025 3380176541265970532008519)
    ·
      refine ⟨5070264811898955798012779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3380176541265970532008519 5070264811898955798012779)
      ·
        refine ⟨7605397217848433697019169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070264811898955798012779 7605397217848433697019169)
        ·
          refine ⟨5704047913386325272764377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7605397217848433697019169 5704047913386325272764377)
          ·
            refine ⟨4278035935039743954573283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704047913386325272764377 4278035935039743954573283)
            ·
              refine ⟨6417053902559615931859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278035935039743954573283 6417053902559615931859925)
              ·
                refine ⟨150399700841240998402967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6417053902559615931859925 150399700841240998402967)
                ·
                  rfl

theorem cell22_3954182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3954182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954182 prefixEnd_3954182 := by exact prefixLift 3954182
  have htrace : WordTrace (prefixWord ++ tailWord_3954182) baseStart_3954182 baseEnd_3954182 := by
    simpa [prefixWord, tailWord_3954182, baseEnd_3954182] using wordTrace_append hprefix tailTrace_3954182
  have hstable : (prefixWord ++ tailWord_3954182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954182).length < 2 ^ (prefixWord ++ tailWord_3954182).sum := by decide
  have hdescent : baseEnd_3954182 < baseStart_3954182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954264 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3954264 : Nat := 118140960795 + 3954264 * 2 ^ 59
def prefixEnd_3954264 : Nat := 4983230072969 + 3 ^ 40 * 3954264 * 2
def baseEnd_3954264 : Nat := 1353625377846948105076451

theorem tailTrace_3954264 : CollatzResearch.WordTrace tailWord_3954264 prefixEnd_3954264 1353625377846948105076451 := by
  unfold tailWord_3954264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72111928273192168685090923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96149237697589558246787897 72111928273192168685090923)
  ·
    refine ⟨108167892409788253027636385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72111928273192168685090923 108167892409788253027636385)
    ·
      refine ⟨81125919307341189770727289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108167892409788253027636385 81125919307341189770727289)
      ·
        refine ⟨60844439480505892328045467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81125919307341189770727289 60844439480505892328045467)
        ·
          refine ⟨91266659220758838492068201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60844439480505892328045467 91266659220758838492068201)
          ·
            refine ⟨68449994415569128869051151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91266659220758838492068201 68449994415569128869051151)
            ·
              refine ⟨102674991623353693303576727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68449994415569128869051151 102674991623353693303576727)
              ·
                refine ⟨154012487435030539955365091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102674991623353693303576727 154012487435030539955365091)
                ·
                  refine ⟨231018731152545809933047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154012487435030539955365091 231018731152545809933047637)
                  ·
                    refine ⟨1353625377846948105076451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231018731152545809933047637 1353625377846948105076451)
                    ·
                      rfl

theorem cell22_3954264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3954264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954264 prefixEnd_3954264 := by exact prefixLift 3954264
  have htrace : WordTrace (prefixWord ++ tailWord_3954264) baseStart_3954264 baseEnd_3954264 := by
    simpa [prefixWord, tailWord_3954264, baseEnd_3954264] using wordTrace_append hprefix tailTrace_3954264
  have hstable : (prefixWord ++ tailWord_3954264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954264).length < 2 ^ (prefixWord ++ tailWord_3954264).sum := by decide
  have hdescent : baseEnd_3954264 < baseStart_3954264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954281 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_3954281 : Nat := 118140960795 + 3954281 * 2 ^ 59
def prefixEnd_3954281 : Nat := 4983230072969 + 3 ^ 40 * 3954281 * 2
def baseEnd_3954281 : Nat := 1353631197294365727401399

theorem tailTrace_3954281 : CollatzResearch.WordTrace tailWord_3954281 prefixEnd_3954281 1353631197294365727401399 := by
  unfold tailWord_3954281
  simp only [CollatzResearch.WordTrace]
  refine ⟨144224476587322749273550697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96149651058215166182367131 144224476587322749273550697)
  ·
    refine ⟨108168357440492061955163023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144224476587322749273550697 108168357440492061955163023)
    ·
      refine ⟨162252536160738092932744535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108168357440492061955163023 162252536160738092932744535)
      ·
        refine ⟨243378804241107139399116803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162252536160738092932744535 243378804241107139399116803)
        ·
          refine ⟨365068206361660709098675205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243378804241107139399116803 365068206361660709098675205)
          ·
            refine ⟨68450288692811382956001601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365068206361660709098675205 68450288692811382956001601)
            ·
              refine ⟨51337716519608537217001201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68450288692811382956001601 51337716519608537217001201)
              ·
                refine ⟨38503287389706402912750901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51337716519608537217001201 38503287389706402912750901)
                ·
                  refine ⟨3609683192784975273070397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38503287389706402912750901 3609683192784975273070397)
                  ·
                    refine ⟨1353631197294365727401399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609683192784975273070397 1353631197294365727401399)
                    ·
                      rfl

theorem cell22_3954281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_3954281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954281 prefixEnd_3954281 := by exact prefixLift 3954281
  have htrace : WordTrace (prefixWord ++ tailWord_3954281) baseStart_3954281 baseEnd_3954281 := by
    simpa [prefixWord, tailWord_3954281, baseEnd_3954281] using wordTrace_append hprefix tailTrace_3954281
  have hstable : (prefixWord ++ tailWord_3954281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954281).length < 2 ^ (prefixWord ++ tailWord_3954281).sum := by decide
  have hdescent : baseEnd_3954281 < baseStart_3954281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954431 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_3954431 : Nat := 118140960795 + 3954431 * 2 ^ 59
def prefixEnd_3954431 : Nat := 4983230072969 + 3 ^ 40 * 3954431 * 2
def baseEnd_3954431 : Nat := 1353682545359815336150939

theorem tailTrace_3954431 : CollatzResearch.WordTrace tailWord_3954431 prefixEnd_3954431 1353682545359815336150939 := by
  unfold tailWord_3954431
  simp only [CollatzResearch.WordTrace]
  refine ⟨144229947536779324891511147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96153298357852883261007431 144229947536779324891511147)
  ·
    refine ⟨216344921305168987337266721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144229947536779324891511147 216344921305168987337266721)
    ·
      refine ⟨162258690978876740502950041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216344921305168987337266721 162258690978876740502950041)
      ·
        refine ⟨121694018234157555377212531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162258690978876740502950041 121694018234157555377212531)
        ·
          refine ⟨182541027351236333065818797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121694018234157555377212531 182541027351236333065818797)
          ·
            refine ⟨68452885256713624899682049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182541027351236333065818797 68452885256713624899682049)
            ·
              refine ⟨51339663942535218674761537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68452885256713624899682049 51339663942535218674761537)
              ·
                refine ⟨38504747956901414006071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51339663942535218674761537 38504747956901414006071153)
                ·
                  refine ⟨28878560967676060504553365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38504747956901414006071153 28878560967676060504553365)
                  ·
                    refine ⟨1353682545359815336150939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28878560967676060504553365 1353682545359815336150939)
                    ·
                      rfl

theorem cell22_3954431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_3954431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954431 prefixEnd_3954431 := by exact prefixLift 3954431
  have htrace : WordTrace (prefixWord ++ tailWord_3954431) baseStart_3954431 baseEnd_3954431 := by
    simpa [prefixWord, tailWord_3954431, baseEnd_3954431] using wordTrace_append hprefix tailTrace_3954431
  have hstable : (prefixWord ++ tailWord_3954431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954431).length < 2 ^ (prefixWord ++ tailWord_3954431).sum := by decide
  have hdescent : baseEnd_3954431 < baseStart_3954431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954463 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 5]
def baseStart_3954463 : Nat := 118140960795 + 3954463 * 2 ^ 59
def prefixEnd_3954463 : Nat := 4983230072969 + 3 ^ 40 * 3954463 * 2
def baseEnd_3954463 : Nat := 451231166537925973116947

theorem tailTrace_3954463 : CollatzResearch.WordTrace tailWord_3954463 prefixEnd_3954463 451231166537925973116947 := by
  unfold tailWord_3954463
  simp only [CollatzResearch.WordTrace]
  refine ⟨144231114672663394356676043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96154076448442262904450695 144231114672663394356676043)
  ·
    refine ⟨216346672008995091535014065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144231114672663394356676043 216346672008995091535014065)
    ·
      refine ⟨162260004006746318651260549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216346672008995091535014065 162260004006746318651260549)
      ·
        refine ⟨30423750751264934747111353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162260004006746318651260549 30423750751264934747111353)
        ·
          refine ⟨22817813063448701060333515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30423750751264934747111353 22817813063448701060333515)
          ·
            refine ⟨34226719595173051590500273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22817813063448701060333515 34226719595173051590500273)
            ·
              refine ⟨25670039696379788692875205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34226719595173051590500273 25670039696379788692875205)
              ·
                refine ⟨4813132443071210379914101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25670039696379788692875205 4813132443071210379914101)
                ·
                  refine ⟨451231166537925973116947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4813132443071210379914101 451231166537925973116947)
                  ·
                    rfl

theorem cell22_3954463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].length) (baseStart_3954463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954463 prefixEnd_3954463 := by exact prefixLift 3954463
  have htrace : WordTrace (prefixWord ++ tailWord_3954463) baseStart_3954463 baseEnd_3954463 := by
    simpa [prefixWord, tailWord_3954463, baseEnd_3954463] using wordTrace_append hprefix tailTrace_3954463
  have hstable : (prefixWord ++ tailWord_3954463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954463).length < 2 ^ (prefixWord ++ tailWord_3954463).sum := by decide
  have hdescent : baseEnd_3954463 < baseStart_3954463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954540 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_3954540 : Nat := 118140960795 + 3954540 * 2 ^ 59
def prefixEnd_3954540 : Nat := 4983230072969 + 3 ^ 40 * 3954540 * 2
def baseEnd_3954540 : Nat := 1353719858287375385175605

theorem tailTrace_3954540 : CollatzResearch.WordTrace tailWord_3954540 prefixEnd_3954540 1353719858287375385175605 := by
  unfold tailWord_3954540
  simp only [CollatzResearch.WordTrace]
  refine ⟨72116961546692218253614537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96155948728922957671486049 72116961546692218253614537)
  ·
    refine ⟨54087721160019163690210903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72116961546692218253614537 54087721160019163690210903)
    ·
      refine ⟨81131581740028745535316355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54087721160019163690210903 81131581740028745535316355)
      ·
        refine ⟨121697372610043118302974533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81131581740028745535316355 121697372610043118302974533)
        ·
          refine ⟨22818257364383084681807725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121697372610043118302974533 22818257364383084681807725)
          ·
            refine ⟨8556846511643656755677897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22818257364383084681807725 8556846511643656755677897)
            ·
              refine ⟨6417634883732742566758423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556846511643656755677897 6417634883732742566758423)
              ·
                refine ⟨9626452325599113850137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417634883732742566758423 9626452325599113850137635)
                ·
                  refine ⟨14439678488398670775206453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9626452325599113850137635 14439678488398670775206453)
                  ·
                    refine ⟨1353719858287375385175605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14439678488398670775206453 1353719858287375385175605)
                    ·
                      rfl

theorem cell22_3954540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_3954540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954540 prefixEnd_3954540 := by exact prefixLift 3954540
  have htrace : WordTrace (prefixWord ++ tailWord_3954540) baseStart_3954540 baseEnd_3954540 := by
    simpa [prefixWord, tailWord_3954540, baseEnd_3954540] using wordTrace_append hprefix tailTrace_3954540
  have hstable : (prefixWord ++ tailWord_3954540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954540).length < 2 ^ (prefixWord ++ tailWord_3954540).sum := by decide
  have hdescent : baseEnd_3954540 < baseStart_3954540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954561 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_3954561 : Nat := 118140960795 + 3954561 * 2 ^ 59
def prefixEnd_3954561 : Nat := 4983230072969 + 3 ^ 40 * 3954561 * 2
def baseEnd_3954561 : Nat := 1353727047016538330400541

theorem tailTrace_3954561 : CollatzResearch.WordTrace tailWord_3954561 prefixEnd_3954561 1353727047016538330400541 := by
  unfold tailWord_3954561
  simp only [CollatzResearch.WordTrace]
  refine ⟨144234689026308357093743537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96156459350872238062495691 144234689026308357093743537)
  ·
    refine ⟨108176016769731267820307653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144234689026308357093743537 108176016769731267820307653)
    ·
      refine ⟨20283003144324612716307685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108176016769731267820307653 20283003144324612716307685)
      ·
        refine ⟨3803063089560864884307691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20283003144324612716307685 3803063089560864884307691)
        ·
          refine ⟨5704594634341297326461537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803063089560864884307691 5704594634341297326461537)
          ·
            refine ⟨4278445975755972994846153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704594634341297326461537 4278445975755972994846153)
            ·
              refine ⟨3208834481816979746134615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278445975755972994846153 3208834481816979746134615)
              ·
                refine ⟨4813251722725469619201923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208834481816979746134615 4813251722725469619201923)
                ·
                  refine ⟨7219877584088204428802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4813251722725469619201923 7219877584088204428802885)
                  ·
                    refine ⟨1353727047016538330400541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7219877584088204428802885 1353727047016538330400541)
                    ·
                      rfl

theorem cell22_3954561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_3954561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954561 prefixEnd_3954561 := by exact prefixLift 3954561
  have htrace : WordTrace (prefixWord ++ tailWord_3954561) baseStart_3954561 baseEnd_3954561 := by
    simpa [prefixWord, tailWord_3954561, baseEnd_3954561] using wordTrace_append hprefix tailTrace_3954561
  have hstable : (prefixWord ++ tailWord_3954561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954561).length < 2 ^ (prefixWord ++ tailWord_3954561).sum := by decide
  have hdescent : baseEnd_3954561 < baseStart_3954561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954570 : List Nat := [3, 1, 2, 4, 2, 1, 9]
def baseStart_3954570 : Nat := 118140960795 + 3954570 * 2 ^ 59
def prefixEnd_3954570 : Nat := 4983230072969 + 3 ^ 40 * 3954570 * 2
def baseEnd_3954570 : Nat := 50138152885202418775019

theorem tailTrace_3954570 : CollatzResearch.WordTrace tailWord_3954570 prefixEnd_3954570 50138152885202418775019 := by
  unfold tailWord_3954570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36058754320818937907705291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96156678188850501087214109 36058754320818937907705291)
  ·
    refine ⟨54088131481228406861557937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36058754320818937907705291 54088131481228406861557937)
    ·
      refine ⟨40566098610921305146168453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54088131481228406861557937 40566098610921305146168453)
      ·
        refine ⟨7606143489547744714906585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40566098610921305146168453 7606143489547744714906585)
        ·
          refine ⟨5704607617160808536179939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606143489547744714906585 5704607617160808536179939)
          ·
            refine ⟨8556911425741212804269909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704607617160808536179939 8556911425741212804269909)
            ·
              refine ⟨50138152885202418775019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8556911425741212804269909 50138152885202418775019)
              ·
                rfl

theorem cell22_3954570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 9].length) (baseStart_3954570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954570 prefixEnd_3954570 := by exact prefixLift 3954570
  have htrace : WordTrace (prefixWord ++ tailWord_3954570) baseStart_3954570 baseEnd_3954570 := by
    simpa [prefixWord, tailWord_3954570, baseEnd_3954570] using wordTrace_append hprefix tailTrace_3954570
  have hstable : (prefixWord ++ tailWord_3954570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954570).length < 2 ^ (prefixWord ++ tailWord_3954570).sum := by decide
  have hdescent : baseEnd_3954570 < baseStart_3954570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954574 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3954574 : Nat := 118140960795 + 3954574 * 2 ^ 59
def prefixEnd_3954574 : Nat := 4983230072969 + 3 ^ 40 * 3954574 * 2
def baseEnd_3954574 : Nat := 1353731497182210629825501

theorem tailTrace_3954574 : CollatzResearch.WordTrace tailWord_3954574 prefixEnd_3954574 1353731497182210629825501 := by
  unfold tailWord_3954574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029395396907657539245847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96156775450174173542644517 18029395396907657539245847)
  ·
    refine ⟨27044093095361486308868771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18029395396907657539245847 27044093095361486308868771)
    ·
      refine ⟨40566139643042229463303157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27044093095361486308868771 40566139643042229463303157)
      ·
        refine ⟨3803075591535209012184671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40566139643042229463303157 3803075591535209012184671)
        ·
          refine ⟨5704613387302813518277007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803075591535209012184671 5704613387302813518277007)
          ·
            refine ⟨8556920080954220277415511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704613387302813518277007 8556920080954220277415511)
            ·
              refine ⟨12835380121431330416123267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556920080954220277415511 12835380121431330416123267)
              ·
                refine ⟨19253070182146995624184901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835380121431330416123267 19253070182146995624184901)
                ·
                  refine ⟨3609950659152561679534669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19253070182146995624184901 3609950659152561679534669)
                  ·
                    refine ⟨1353731497182210629825501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609950659152561679534669 1353731497182210629825501)
                    ·
                      rfl

theorem cell22_3954574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3954574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954574 prefixEnd_3954574 := by exact prefixLift 3954574
  have htrace : WordTrace (prefixWord ++ tailWord_3954574) baseStart_3954574 baseEnd_3954574 := by
    simpa [prefixWord, tailWord_3954574, baseEnd_3954574] using wordTrace_append hprefix tailTrace_3954574
  have hstable : (prefixWord ++ tailWord_3954574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954574).length < 2 ^ (prefixWord ++ tailWord_3954574).sum := by decide
  have hdescent : baseEnd_3954574 < baseStart_3954574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954585 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_3954585 : Nat := 118140960795 + 3954585 * 2 ^ 59
def prefixEnd_3954585 : Nat := 4983230072969 + 3 ^ 40 * 3954585 * 2
def baseEnd_3954585 : Nat := 1353735262707010267800467

theorem tailTrace_3954585 : CollatzResearch.WordTrace tailWord_3954585 prefixEnd_3954585 1353735262707010267800467 := by
  unfold tailWord_3954585
  simp only [CollatzResearch.WordTrace]
  refine ⟨144235564378221409192617209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96157042918814272795078139 144235564378221409192617209)
  ·
    refine ⟨108176673283666056894462907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144235564378221409192617209 108176673283666056894462907)
    ·
      refine ⟨162265009925499085341694361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108176673283666056894462907 162265009925499085341694361)
      ·
        refine ⟨121698757444124314006270771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162265009925499085341694361 121698757444124314006270771)
        ·
          refine ⟨182548136166186471009406157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121698757444124314006270771 182548136166186471009406157)
          ·
            refine ⟨68455551062319926628527309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182548136166186471009406157 68455551062319926628527309)
            ·
              refine ⟨25670831648369972485697741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68455551062319926628527309 25670831648369972485697741)
              ·
                refine ⟨9626561868138739682136653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25670831648369972485697741 9626561868138739682136653)
                ·
                  refine ⟨3609960700552027380801245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9626561868138739682136653 3609960700552027380801245)
                  ·
                    refine ⟨1353735262707010267800467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609960700552027380801245 1353735262707010267800467)
                    ·
                      rfl

theorem cell22_3954585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_3954585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954585 prefixEnd_3954585 := by exact prefixLift 3954585
  have htrace : WordTrace (prefixWord ++ tailWord_3954585) baseStart_3954585 baseEnd_3954585 := by
    simpa [prefixWord, tailWord_3954585, baseEnd_3954585] using wordTrace_append hprefix tailTrace_3954585
  have hstable : (prefixWord ++ tailWord_3954585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954585).length < 2 ^ (prefixWord ++ tailWord_3954585).sum := by decide
  have hdescent : baseEnd_3954585 < baseStart_3954585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954636 : List Nat := [2, 2, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_3954636 : Nat := 118140960795 + 3954636 * 2 ^ 59
def prefixEnd_3954636 : Nat := 4983230072969 + 3 ^ 40 * 3954636 * 2
def baseEnd_3954636 : Nat := 1353752721049263134775311

theorem tailTrace_3954636 : CollatzResearch.WordTrace tailWord_3954636 prefixEnd_3954636 1353752721049263134775311 := by
  unfold tailWord_3954636
  simp only [CollatzResearch.WordTrace]
  refine ⟨72118712250518322451361881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96158283000691096601815841 72118712250518322451361881)
  ·
    refine ⟨54089034187888741838521411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72118712250518322451361881 54089034187888741838521411)
    ·
      refine ⟨81133551281833112757782117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54089034187888741838521411 81133551281833112757782117)
      ·
        refine ⟨15212540865343708642084147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81133551281833112757782117 15212540865343708642084147)
        ·
          refine ⟨22818811298015562963126221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15212540865343708642084147 22818811298015562963126221)
          ·
            refine ⟨8557054236755836111172333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22818811298015562963126221 8557054236755836111172333)
            ·
              refine ⟨3208895338783438541689625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8557054236755836111172333 3208895338783438541689625)
              ·
                refine ⟨2406671504087578906267219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208895338783438541689625 2406671504087578906267219)
                ·
                  refine ⟨3610007256131368359400829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406671504087578906267219 3610007256131368359400829)
                  ·
                    refine ⟨1353752721049263134775311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610007256131368359400829 1353752721049263134775311)
                    ·
                      rfl

theorem cell22_3954636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_3954636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954636 prefixEnd_3954636 := by exact prefixLift 3954636
  have htrace : WordTrace (prefixWord ++ tailWord_3954636) baseStart_3954636 baseEnd_3954636 := by
    simpa [prefixWord, tailWord_3954636, baseEnd_3954636] using wordTrace_append hprefix tailTrace_3954636
  have hstable : (prefixWord ++ tailWord_3954636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954636).length < 2 ^ (prefixWord ++ tailWord_3954636).sum := by decide
  have hdescent : baseEnd_3954636 < baseStart_3954636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954649 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 5]
def baseStart_3954649 : Nat := 118140960795 + 3954649 * 2 ^ 59
def prefixEnd_3954649 : Nat := 4983230072969 + 3 ^ 40 * 3954649 * 2
def baseEnd_3954649 : Nat := 451252390404978478066757

theorem tailTrace_3954649 : CollatzResearch.WordTrace tailWord_3954649 prefixEnd_3954649 451252390404978478066757 := by
  unfold tailWord_3954649
  simp only [CollatzResearch.WordTrace]
  refine ⟨144237898649989548122947001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96158599099993032081964667 144237898649989548122947001)
  ·
    refine ⟨108178423987492161092210251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144237898649989548122947001 108178423987492161092210251)
    ·
      refine ⟨162267635981238241638315377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108178423987492161092210251 162267635981238241638315377)
      ·
        refine ⟨121700726985928681228736533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162267635981238241638315377 121700726985928681228736533)
        ·
          refine ⟨5704721577465406932597025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121700726985928681228736533 5704721577465406932597025)
          ·
            refine ⟨4278541183099055199447769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704721577465406932597025 4278541183099055199447769)
            ·
              refine ⟨3208905887324291399585827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278541183099055199447769 3208905887324291399585827)
              ·
                refine ⟨4813358830986437099378741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208905887324291399585827 4813358830986437099378741)
                ·
                  refine ⟨451252390404978478066757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4813358830986437099378741 451252390404978478066757)
                  ·
                    rfl

theorem cell22_3954649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_3954649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954649 prefixEnd_3954649 := by exact prefixLift 3954649
  have htrace : WordTrace (prefixWord ++ tailWord_3954649) baseStart_3954649 baseEnd_3954649 := by
    simpa [prefixWord, tailWord_3954649, baseEnd_3954649] using wordTrace_append hprefix tailTrace_3954649
  have hstable : (prefixWord ++ tailWord_3954649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954649).length < 2 ^ (prefixWord ++ tailWord_3954649).sum := by decide
  have hdescent : baseEnd_3954649 < baseStart_3954649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954675 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 6, 3]
def baseStart_3954675 : Nat := 118140960795 + 3954675 * 2 ^ 59
def prefixEnd_3954675 : Nat := 4983230072969 + 3 ^ 40 * 3954675 * 2
def baseEnd_3954675 : Nat := 1353766071546280033050191

theorem tailTrace_3954675 : CollatzResearch.WordTrace tailWord_3954675 prefixEnd_3954675 1353766071546280033050191 := by
  unfold tailWord_3954675
  simp only [CollatzResearch.WordTrace]
  refine ⟨144238846947895354563393479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96159231298596903042262319 144238846947895354563393479)
  ·
    refine ⟨216358270421843031845090219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144238846947895354563393479 216358270421843031845090219)
    ·
      refine ⟨324537405632764547767635329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216358270421843031845090219 324537405632764547767635329)
      ·
        refine ⟨243403054224573410825726497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324537405632764547767635329 243403054224573410825726497)
        ·
          refine ⟨182552290668430058119294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243403054224573410825726497 182552290668430058119294873)
          ·
            refine ⟨136914218001322543589471155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182552290668430058119294873 136914218001322543589471155)
            ·
              refine ⟨205371327001983815384206733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136914218001322543589471155 205371327001983815384206733)
              ·
                refine ⟨77014247625743930769077525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205371327001983815384206733 77014247625743930769077525)
                ·
                  refine ⟨3610042857456746754800509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77014247625743930769077525 3610042857456746754800509)
                  ·
                    refine ⟨1353766071546280033050191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610042857456746754800509 1353766071546280033050191)
                    ·
                      rfl

theorem cell22_3954675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].length) (baseStart_3954675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954675 prefixEnd_3954675 := by exact prefixLift 3954675
  have htrace : WordTrace (prefixWord ++ tailWord_3954675) baseStart_3954675 baseEnd_3954675 := by
    simpa [prefixWord, tailWord_3954675, baseEnd_3954675] using wordTrace_append hprefix tailTrace_3954675
  have hstable : (prefixWord ++ tailWord_3954675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954675).length < 2 ^ (prefixWord ++ tailWord_3954675).sum := by decide
  have hdescent : baseEnd_3954675 < baseStart_3954675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954722 : List Nat := [3, 3, 1, 1, 1, 2, 5, 6]
def baseStart_3954722 : Nat := 118140960795 + 3954722 * 2 ^ 59
def prefixEnd_3954722 : Nat := 4983230072969 + 3 ^ 40 * 3954722 * 2
def baseEnd_3954722 : Nat := 150420240067420841902783

theorem tailTrace_3954722 : CollatzResearch.WordTrace tailWord_3954722 prefixEnd_3954722 150420240067420841902783 := by
  unfold tailWord_3954722
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060140294681270397588605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96160374119150054393569613 36060140294681270397588605)
  ·
    refine ⟨13522552610505476399095727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36060140294681270397588605 13522552610505476399095727)
    ·
      refine ⟨20283828915758214598643591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13522552610505476399095727 20283828915758214598643591)
      ·
        refine ⟨30425743373637321897965387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283828915758214598643591 30425743373637321897965387)
        ·
          refine ⟨45638615060455982846948081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30425743373637321897965387 45638615060455982846948081)
          ·
            refine ⟨34228961295341987135211061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45638615060455982846948081 34228961295341987135211061)
            ·
              refine ⟨3208965121438311293926037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34228961295341987135211061 3208965121438311293926037)
              ·
                refine ⟨150420240067420841902783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3208965121438311293926037 150420240067420841902783)
                ·
                  rfl

theorem cell22_3954722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_3954722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954722 prefixEnd_3954722 := by exact prefixLift 3954722
  have htrace : WordTrace (prefixWord ++ tailWord_3954722) baseStart_3954722 baseEnd_3954722 := by
    simpa [prefixWord, tailWord_3954722, baseEnd_3954722] using wordTrace_append hprefix tailTrace_3954722
  have hstable : (prefixWord ++ tailWord_3954722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954722).length < 2 ^ (prefixWord ++ tailWord_3954722).sum := by decide
  have hdescent : baseEnd_3954722 < baseStart_3954722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954812 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_3954812 : Nat := 118140960795 + 3954812 * 2 ^ 59
def prefixEnd_3954812 : Nat := 4983230072969 + 3 ^ 40 * 3954812 * 2
def baseEnd_3954812 : Nat := 451270989815352447458257

theorem tailTrace_3954812 : CollatzResearch.WordTrace tailWord_3954812 prefixEnd_3954812 451270989815352447458257 := by
  unfold tailWord_3954812
  simp only [CollatzResearch.WordTrace]
  refine ⟨72121921874199513480565345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96162562498932684640753793 72121921874199513480565345)
  ·
    refine ⟨54091441405649635110424009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72121921874199513480565345 54091441405649635110424009)
    ·
      refine ⟨40568581054237226332818007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54091441405649635110424009 40568581054237226332818007)
      ·
        refine ⟨60852871581355839499227011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40568581054237226332818007 60852871581355839499227011)
        ·
          refine ⟨91279307372033759248840517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60852871581355839499227011 91279307372033759248840517)
          ·
            refine ⟨17114870132256329859157597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91279307372033759248840517 17114870132256329859157597)
            ·
              refine ⟨6418076299596123697184099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17114870132256329859157597 6418076299596123697184099)
              ·
                refine ⟨9627114449394185545776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418076299596123697184099 9627114449394185545776149)
                ·
                  refine ⟨451270989815352447458257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627114449394185545776149 451270989815352447458257)
                  ·
                    rfl

theorem cell22_3954812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_3954812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954812 prefixEnd_3954812 := by exact prefixLift 3954812
  have htrace : WordTrace (prefixWord ++ tailWord_3954812) baseStart_3954812 baseEnd_3954812 := by
    simpa [prefixWord, tailWord_3954812, baseEnd_3954812] using wordTrace_append hprefix tailTrace_3954812
  have hstable : (prefixWord ++ tailWord_3954812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954812).length < 2 ^ (prefixWord ++ tailWord_3954812).sum := by decide
  have hdescent : baseEnd_3954812 < baseStart_3954812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954861 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3954861 : Nat := 118140960795 + 3954861 * 2 ^ 59
def prefixEnd_3954861 : Nat := 4983230072969 + 3 ^ 40 * 3954861 * 2
def baseEnd_3954861 : Nat := 1353829743147437547899621

theorem tailTrace_3954861 : CollatzResearch.WordTrace tailWord_3954861 prefixEnd_3954861 1353829743147437547899621 := by
  unfold tailWord_3954861
  simp only [CollatzResearch.WordTrace]
  refine ⟨144245630925221508329664437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96163753950147672219776291 144245630925221508329664437)
  ·
    refine ⟨13523027899239516405906041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144245630925221508329664437 13523027899239516405906041)
    ·
      refine ⟨10142270924429637304429531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13523027899239516405906041 10142270924429637304429531)
      ·
        refine ⟨15213406386644455956644297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10142270924429637304429531 15213406386644455956644297)
        ·
          refine ⟨11410054789983341967483223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15213406386644455956644297 11410054789983341967483223)
          ·
            refine ⟨17115082184975012951224835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11410054789983341967483223 17115082184975012951224835)
            ·
              refine ⟨25672623277462519426837253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17115082184975012951224835 25672623277462519426837253)
              ·
                refine ⟨4813616864524222392531985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25672623277462519426837253 4813616864524222392531985)
                ·
                  refine ⟨3610212648393166794398989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813616864524222392531985 3610212648393166794398989)
                  ·
                    refine ⟨1353829743147437547899621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610212648393166794398989 1353829743147437547899621)
                    ·
                      rfl

theorem cell22_3954861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3954861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954861 prefixEnd_3954861 := by exact prefixLift 3954861
  have htrace : WordTrace (prefixWord ++ tailWord_3954861) baseStart_3954861 baseEnd_3954861 := by
    simpa [prefixWord, tailWord_3954861, baseEnd_3954861] using wordTrace_append hprefix tailTrace_3954861
  have hstable : (prefixWord ++ tailWord_3954861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954861).length < 2 ^ (prefixWord ++ tailWord_3954861).sum := by decide
  have hdescent : baseEnd_3954861 < baseStart_3954861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954906 : List Nat := [3, 1, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_3954906 : Nat := 118140960795 + 3954906 * 2 ^ 59
def prefixEnd_3954906 : Nat := 4983230072969 + 3 ^ 40 * 3954906 * 2
def baseEnd_3954906 : Nat := 1353845147567072430524483

theorem tailTrace_3954906 : CollatzResearch.WordTrace tailWord_3954906 prefixEnd_3954906 1353845147567072430524483 := by
  unfold tailWord_3954906
  simp only [CollatzResearch.WordTrace]
  refine ⟨36061818052514620253763143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96164848140038987343368381 36061818052514620253763143)
  ·
    refine ⟨54092727078771930380644715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36061818052514620253763143 54092727078771930380644715)
    ·
      refine ⟨81139090618157895570967073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54092727078771930380644715 81139090618157895570967073)
      ·
        refine ⟨60854317963618421678225305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81139090618157895570967073 60854317963618421678225305)
        ·
          refine ⟨45640738472713816258668979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60854317963618421678225305 45640738472713816258668979)
          ·
            refine ⟨68461107709070724388003469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45640738472713816258668979 68461107709070724388003469)
            ·
              refine ⟨25672915390901521645501301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68461107709070724388003469 25672915390901521645501301)
              ·
                refine ⟨2406835817897017654265747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25672915390901521645501301 2406835817897017654265747)
                ·
                  refine ⟨3610253726845526481398621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406835817897017654265747 3610253726845526481398621)
                  ·
                    refine ⟨1353845147567072430524483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610253726845526481398621 1353845147567072430524483)
                    ·
                      rfl

theorem cell22_3954906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_3954906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954906 prefixEnd_3954906 := by exact prefixLift 3954906
  have htrace : WordTrace (prefixWord ++ tailWord_3954906) baseStart_3954906 baseEnd_3954906 := by
    simpa [prefixWord, tailWord_3954906, baseEnd_3954906] using wordTrace_append hprefix tailTrace_3954906
  have hstable : (prefixWord ++ tailWord_3954906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954906).length < 2 ^ (prefixWord ++ tailWord_3954906).sum := by decide
  have hdescent : baseEnd_3954906 < baseStart_3954906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954919 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 7]
def baseStart_3954919 : Nat := 118140960795 + 3954919 * 2 ^ 59
def prefixEnd_3954919 : Nat := 4983230072969 + 3 ^ 40 * 3954919 * 2
def baseEnd_3954919 : Nat := 451283199244248243316481

theorem tailTrace_3954919 : CollatzResearch.WordTrace tailWord_3954919 prefixEnd_3954919 451283199244248243316481 := by
  unfold tailWord_3954919
  simp only [CollatzResearch.WordTrace]
  refine ⟨144247746359011384235275811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96165164239340922823517207 144247746359011384235275811)
  ·
    refine ⟨216371619538517076352913717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144247746359011384235275811 216371619538517076352913717)
    ·
      refine ⟨20284839331735975908085661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216371619538517076352913717 20284839331735975908085661)
      ·
        refine ⟨7606814749400990965532123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20284839331735975908085661 7606814749400990965532123)
        ·
          refine ⟨11410222124101486448298185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606814749400990965532123 11410222124101486448298185)
          ·
            refine ⟨8557666593076114836223639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11410222124101486448298185 8557666593076114836223639)
            ·
              refine ⟨12836499889614172254335459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557666593076114836223639 12836499889614172254335459)
              ·
                refine ⟨19254749834421258381503189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836499889614172254335459 19254749834421258381503189)
                ·
                  refine ⟨451283199244248243316481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19254749834421258381503189 451283199244248243316481)
                  ·
                    rfl

theorem cell22_3954919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_3954919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954919 prefixEnd_3954919 := by exact prefixLift 3954919
  have htrace : WordTrace (prefixWord ++ tailWord_3954919) baseStart_3954919 baseEnd_3954919 := by
    simpa [prefixWord, tailWord_3954919, baseEnd_3954919] using wordTrace_append hprefix tailTrace_3954919
  have hstable : (prefixWord ++ tailWord_3954919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954919).length < 2 ^ (prefixWord ++ tailWord_3954919).sum := by decide
  have hdescent : baseEnd_3954919 < baseStart_3954919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954934 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3954934 : Nat := 118140960795 + 3954934 * 2 ^ 59
def prefixEnd_3954934 : Nat := 4983230072969 + 3 ^ 40 * 3954934 * 2
def baseEnd_3954934 : Nat := 1353854732539289690824397

theorem tailTrace_3954934 : CollatzResearch.WordTrace tailWord_3954934 prefixEnd_3954934 1353854732539289690824397 := by
  unfold tailWord_3954934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015518340872315112316991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96165528969304694531381237 9015518340872315112316991)
  ·
    refine ⟨13523277511308472668475487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015518340872315112316991 13523277511308472668475487)
    ·
      refine ⟨20284916266962709002713231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13523277511308472668475487 20284916266962709002713231)
      ·
        refine ⟨30427374400444063504069847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20284916266962709002713231 30427374400444063504069847)
        ·
          refine ⟨45641061600666095256104771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30427374400444063504069847 45641061600666095256104771)
          ·
            refine ⟨68461592400999142884157157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45641061600666095256104771 68461592400999142884157157)
            ·
              refine ⟨12836548575187339290779467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68461592400999142884157157 12836548575187339290779467)
              ·
                refine ⟨19254822862781008936169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12836548575187339290779467 19254822862781008936169201)
                ·
                  refine ⟨14441117147085756702126901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19254822862781008936169201 14441117147085756702126901)
                  ·
                    refine ⟨1353854732539289690824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14441117147085756702126901 1353854732539289690824397)
                    ·
                      rfl

theorem cell22_3954934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3954934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954934 prefixEnd_3954934 := by exact prefixLift 3954934
  have htrace : WordTrace (prefixWord ++ tailWord_3954934) baseStart_3954934 baseEnd_3954934 := by
    simpa [prefixWord, tailWord_3954934, baseEnd_3954934] using wordTrace_append hprefix tailTrace_3954934
  have hstable : (prefixWord ++ tailWord_3954934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954934).length < 2 ^ (prefixWord ++ tailWord_3954934).sum := by decide
  have hdescent : baseEnd_3954934 < baseStart_3954934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954947 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 6]
def baseStart_3954947 : Nat := 118140960795 + 3954947 * 2 ^ 59
def prefixEnd_3954947 : Nat := 4983230072969 + 3 ^ 40 * 3954947 * 2
def baseEnd_3954947 : Nat := 451286394234987330083119

theorem tailTrace_3954947 : CollatzResearch.WordTrace tailWord_3954947 prefixEnd_3954947 451286394234987330083119 := by
  unfold tailWord_3954947
  simp only [CollatzResearch.WordTrace]
  refine ⟨144248767602909945017295095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96165845068606630011530063 144248767602909945017295095)
  ·
    refine ⟨216373151404364917525942643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144248767602909945017295095 216373151404364917525942643)
    ·
      refine ⟨324559727106547376288913965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216373151404364917525942643 324559727106547376288913965)
      ·
        refine ⟨121709897664955266108342737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324559727106547376288913965 121709897664955266108342737)
        ·
          refine ⟨91282423248716449581257053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121709897664955266108342737 91282423248716449581257053)
          ·
            refine ⟨34230908718268668592971395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91282423248716449581257053 34230908718268668592971395)
            ·
              refine ⟨51346363077403002889457093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34230908718268668592971395 51346363077403002889457093)
              ·
                refine ⟨9627443077013063041773205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51346363077403002889457093 9627443077013063041773205)
                ·
                  refine ⟨451286394234987330083119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627443077013063041773205 451286394234987330083119)
                  ·
                    rfl

theorem cell22_3954947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_3954947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954947 prefixEnd_3954947 := by exact prefixLift 3954947
  have htrace : WordTrace (prefixWord ++ tailWord_3954947) baseStart_3954947 baseEnd_3954947 := by
    simpa [prefixWord, tailWord_3954947, baseEnd_3954947] using wordTrace_append hprefix tailTrace_3954947
  have hstable : (prefixWord ++ tailWord_3954947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954947).length < 2 ^ (prefixWord ++ tailWord_3954947).sum := by decide
  have hdescent : baseEnd_3954947 < baseStart_3954947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954979 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 4, 3]
def baseStart_3954979 : Nat := 118140960795 + 3954979 * 2 ^ 59
def prefixEnd_3954979 : Nat := 4983230072969 + 3 ^ 40 * 3954979 * 2
def baseEnd_3954979 : Nat := 1353870136958924573449259

theorem tailTrace_3954979 : CollatzResearch.WordTrace tailWord_3954979 prefixEnd_3954979 1353870136958924573449259 := by
  unfold tailWord_3954979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144249934738794014482459991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96166623159196009654973327 144249934738794014482459991)
  ·
    refine ⟨216374902108191021723689987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144249934738794014482459991 216374902108191021723689987)
    ·
      refine ⟨324562353162286532585534981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216374902108191021723689987 324562353162286532585534981)
      ·
        refine ⟨60855441217928724859787809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324562353162286532585534981 60855441217928724859787809)
        ·
          refine ⟨45641580913446543644840857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60855441217928724859787809 45641580913446543644840857)
          ·
            refine ⟨34231185685084907733630643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45641580913446543644840857 34231185685084907733630643)
            ·
              refine ⟨51346778527627361600445965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34231185685084907733630643 51346778527627361600445965)
              ·
                refine ⟨19255041947860260600167237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51346778527627361600445965 19255041947860260600167237)
                ·
                  refine ⟨3610320365223798862531357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19255041947860260600167237 3610320365223798862531357)
                  ·
                    refine ⟨1353870136958924573449259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610320365223798862531357 1353870136958924573449259)
                    ·
                      rfl

theorem cell22_3954979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].length) (baseStart_3954979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954979 prefixEnd_3954979 := by exact prefixLift 3954979
  have htrace : WordTrace (prefixWord ++ tailWord_3954979) baseStart_3954979 baseEnd_3954979 := by
    simpa [prefixWord, tailWord_3954979, baseEnd_3954979] using wordTrace_append hprefix tailTrace_3954979
  have hstable : (prefixWord ++ tailWord_3954979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954979).length < 2 ^ (prefixWord ++ tailWord_3954979).sum := by decide
  have hdescent : baseEnd_3954979 < baseStart_3954979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3954981 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 6]
def baseStart_3954981 : Nat := 118140960795 + 3954981 * 2 ^ 59
def prefixEnd_3954981 : Nat := 4983230072969 + 3 ^ 40 * 3954981 * 2
def baseEnd_3954981 : Nat := 451290273866599078299751

theorem tailTrace_3954981 : CollatzResearch.WordTrace tailWord_3954981 prefixEnd_3954981 451290273866599078299751 := by
  unfold tailWord_3954981
  simp only [CollatzResearch.WordTrace]
  refine ⟨144250007684786768824032797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96166671789857845882688531 144250007684786768824032797)
  ·
    refine ⟨54093752881795038309012299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144250007684786768824032797 54093752881795038309012299)
    ·
      refine ⟨81140629322692557463518449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54093752881795038309012299 81140629322692557463518449)
      ·
        refine ⟨60855471992019418097638837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81140629322692557463518449 60855471992019418097638837)
        ·
          refine ⟨5705200499251820446653641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60855471992019418097638837 5705200499251820446653641)
          ·
            refine ⟨4278900374438865334990231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5705200499251820446653641 4278900374438865334990231)
            ·
              refine ⟨6418350561658298002485347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278900374438865334990231 6418350561658298002485347)
              ·
                refine ⟨9627525842487447003728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418350561658298002485347 9627525842487447003728021)
                ·
                  refine ⟨451290273866599078299751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627525842487447003728021 451290273866599078299751)
                  ·
                    rfl

theorem cell22_3954981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_3954981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3954981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3954981 prefixEnd_3954981 := by exact prefixLift 3954981
  have htrace : WordTrace (prefixWord ++ tailWord_3954981) baseStart_3954981 baseEnd_3954981 := by
    simpa [prefixWord, tailWord_3954981, baseEnd_3954981] using wordTrace_append hprefix tailTrace_3954981
  have hstable : (prefixWord ++ tailWord_3954981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3954981).length < 2 ^ (prefixWord ++ tailWord_3954981).sum := by decide
  have hdescent : baseEnd_3954981 < baseStart_3954981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3954981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955062 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_3955062 : Nat := 118140960795 + 3955062 * 2 ^ 59
def prefixEnd_3955062 : Nat := 4983230072969 + 3 ^ 40 * 3955062 * 2
def baseEnd_3955062 : Nat := 1353898549555140023624005

theorem tailTrace_3955062 : CollatzResearch.WordTrace tailWord_3955062 prefixEnd_3955062 1353898549555140023624005 := by
  unfold tailWord_3955062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015810124843332478608215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96168641331662213105154293 9015810124843332478608215)
  ·
    refine ⟨13523715187264998717912323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015810124843332478608215 13523715187264998717912323)
    ·
      refine ⟨20285572780897498076868485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13523715187264998717912323 20285572780897498076868485)
      ·
        refine ⟨3803544896418280889412841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20285572780897498076868485 3803544896418280889412841)
        ·
          refine ⟨2852658672313710667059631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803544896418280889412841 2852658672313710667059631)
          ·
            refine ⟨4278988008470566000589447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852658672313710667059631 4278988008470566000589447)
            ·
              refine ⟨6418482012705849000884171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278988008470566000589447 6418482012705849000884171)
              ·
                refine ⟨9627723019058773501326257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418482012705849000884171 9627723019058773501326257)
                ·
                  refine ⟨7220792264294080125994693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627723019058773501326257 7220792264294080125994693)
                  ·
                    refine ⟨1353898549555140023624005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220792264294080125994693 1353898549555140023624005)
                    ·
                      rfl

theorem cell22_3955062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_3955062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955062 prefixEnd_3955062 := by exact prefixLift 3955062
  have htrace : WordTrace (prefixWord ++ tailWord_3955062) baseStart_3955062 baseEnd_3955062 := by
    simpa [prefixWord, tailWord_3955062, baseEnd_3955062] using wordTrace_append hprefix tailTrace_3955062
  have hstable : (prefixWord ++ tailWord_3955062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955062).length < 2 ^ (prefixWord ++ tailWord_3955062).sum := by decide
  have hdescent : baseEnd_3955062 < baseStart_3955062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955075 : List Nat := [1, 1, 1, 3, 6, 1, 2, 3, 1, 3]
def baseStart_3955075 : Nat := 118140960795 + 3955075 * 2 ^ 59
def prefixEnd_3955075 : Nat := 4983230072969 + 3 ^ 40 * 3955075 * 2
def baseEnd_3955075 : Nat := 1353902999720812323048965

theorem tailTrace_3955075 : CollatzResearch.WordTrace tailWord_3955075 prefixEnd_3955075 1353902999720812323048965 := by
  unfold tailWord_3955075
  simp only [CollatzResearch.WordTrace]
  refine ⟨144253436146446222877954679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96168957430964148585303119 144253436146446222877954679)
  ·
    refine ⟨216380154219669334316932019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144253436146446222877954679 216380154219669334316932019)
    ·
      refine ⟨324570231329504001475398029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216380154219669334316932019 324570231329504001475398029)
      ·
        refine ⟨121713836748564000553274261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324570231329504001475398029 121713836748564000553274261)
        ·
          refine ⟨5705336097588937525934731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121713836748564000553274261 5705336097588937525934731)
          ·
            refine ⟨8558004146383406288902097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705336097588937525934731 8558004146383406288902097)
            ·
              refine ⟨6418503109787554716676573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558004146383406288902097 6418503109787554716676573)
              ·
                refine ⟨2406938666170333018753715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418503109787554716676573 2406938666170333018753715)
                ·
                  refine ⟨3610407999255499528130573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406938666170333018753715 3610407999255499528130573)
                  ·
                    refine ⟨1353902999720812323048965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610407999255499528130573 1353902999720812323048965)
                    ·
                      rfl

theorem cell22_3955075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 3].length) (baseStart_3955075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955075 prefixEnd_3955075 := by exact prefixLift 3955075
  have htrace : WordTrace (prefixWord ++ tailWord_3955075) baseStart_3955075 baseEnd_3955075 := by
    simpa [prefixWord, tailWord_3955075, baseEnd_3955075] using wordTrace_append hprefix tailTrace_3955075
  have hstable : (prefixWord ++ tailWord_3955075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955075).length < 2 ^ (prefixWord ++ tailWord_3955075).sum := by decide
  have hdescent : baseEnd_3955075 < baseStart_3955075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955086 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_3955086 : Nat := 118140960795 + 3955086 * 2 ^ 59
def prefixEnd_3955086 : Nat := 4983230072969 + 3 ^ 40 * 3955086 * 2
def baseEnd_3955086 : Nat := 1353906765245611961023931

theorem tailTrace_3955086 : CollatzResearch.WordTrace tailWord_3955086 prefixEnd_3955086 1353906765245611961023931 := by
  unfold tailWord_3955086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18031729668675796469575639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96169224899604247837736741 18031729668675796469575639)
  ·
    refine ⟨27047594503013694704363459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18031729668675796469575639 27047594503013694704363459)
    ·
      refine ⟨40571391754520542056545189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27047594503013694704363459 40571391754520542056545189)
      ·
        refine ⟨7607135953972601635602223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40571391754520542056545189 7607135953972601635602223)
        ·
          refine ⟨11410703930958902453403335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607135953972601635602223 11410703930958902453403335)
          ·
            refine ⟨17116055896438353680105003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11410703930958902453403335 17116055896438353680105003)
            ·
              refine ⟨25674083844657530520157505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17116055896438353680105003 25674083844657530520157505)
              ·
                refine ⟨19255562883493147890118129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25674083844657530520157505 19255562883493147890118129)
                ·
                  refine ⟨14441672162619860917588597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19255562883493147890118129 14441672162619860917588597)
                  ·
                    refine ⟨1353906765245611961023931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14441672162619860917588597 1353906765245611961023931)
                    ·
                      rfl

theorem cell22_3955086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_3955086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955086 prefixEnd_3955086 := by exact prefixLift 3955086
  have htrace : WordTrace (prefixWord ++ tailWord_3955086) baseStart_3955086 baseEnd_3955086 := by
    simpa [prefixWord, tailWord_3955086, baseEnd_3955086] using wordTrace_append hprefix tailTrace_3955086
  have hstable : (prefixWord ++ tailWord_3955086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955086).length < 2 ^ (prefixWord ++ tailWord_3955086).sum := by decide
  have hdescent : baseEnd_3955086 < baseStart_3955086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955105 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 5]
def baseStart_3955105 : Nat := 118140960795 + 3955105 * 2 ^ 59
def prefixEnd_3955105 : Nat := 4983230072969 + 3 ^ 40 * 3955105 * 2
def baseEnd_3955105 : Nat := 451304423111300748266291

theorem tailTrace_3955105 : CollatzResearch.WordTrace tailWord_3955105 prefixEnd_3955105 451304423111300748266291 := by
  unfold tailWord_3955105
  simp only [CollatzResearch.WordTrace]
  refine ⟨144254530336337538001546769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96169686890891692001031179 144254530336337538001546769)
  ·
    refine ⟨108190897752253153501160077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144254530336337538001546769 108190897752253153501160077)
    ·
      refine ⟨40571586657094932562935029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108190897752253153501160077 40571586657094932562935029)
      ·
        refine ⟨3803586249102649927775159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40571586657094932562935029 3803586249102649927775159)
        ·
          refine ⟨5705379373653974891662739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803586249102649927775159 5705379373653974891662739)
          ·
            refine ⟨8558069060480962337494109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705379373653974891662739 8558069060480962337494109)
            ·
              refine ⟨3209275897680360876560291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8558069060480962337494109 3209275897680360876560291)
              ·
                refine ⟨4813913846520541314840437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209275897680360876560291 4813913846520541314840437)
                ·
                  refine ⟨451304423111300748266291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4813913846520541314840437 451304423111300748266291)
                  ·
                    rfl

theorem cell22_3955105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_3955105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955105 prefixEnd_3955105 := by exact prefixLift 3955105
  have htrace : WordTrace (prefixWord ++ tailWord_3955105) baseStart_3955105 baseEnd_3955105 := by
    simpa [prefixWord, tailWord_3955105, baseEnd_3955105] using wordTrace_append hprefix tailTrace_3955105
  have hstable : (prefixWord ++ tailWord_3955105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955105).length < 2 ^ (prefixWord ++ tailWord_3955105).sum := by decide
  have hdescent : baseEnd_3955105 < baseStart_3955105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955133 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 4]
def baseStart_3955133 : Nat := 118140960795 + 3955133 * 2 ^ 59
def prefixEnd_3955133 : Nat := 4983230072969 + 3 ^ 40 * 3955133 * 2
def baseEnd_3955133 : Nat := 451307618102039835032929

theorem tailTrace_3955133 : CollatzResearch.WordTrace tailWord_3955133 prefixEnd_3955133 451307618102039835032929 := by
  unfold tailWord_3955133
  simp only [CollatzResearch.WordTrace]
  refine ⟨144255551580236098783566053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96170367720157399189044035 144255551580236098783566053)
  ·
    refine ⟨27047915921294268521918635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144255551580236098783566053 27047915921294268521918635)
    ·
      refine ⟨40571873881941402782877953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27047915921294268521918635 40571873881941402782877953)
      ·
        refine ⟨30428905411456052087158465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40571873881941402782877953 30428905411456052087158465)
        ·
          refine ⟨22821679058592039065368849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30428905411456052087158465 22821679058592039065368849)
          ·
            refine ⟨17116259293944029299026637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821679058592039065368849 17116259293944029299026637)
            ·
              refine ⟨6418597235229010987134989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17116259293944029299026637 6418597235229010987134989)
              ·
                refine ⟨2406973963210879120175621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418597235229010987134989 2406973963210879120175621)
                ·
                  refine ⟨451307618102039835032929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406973963210879120175621 451307618102039835032929)
                  ·
                    rfl

theorem cell22_3955133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_3955133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955133 prefixEnd_3955133 := by exact prefixLift 3955133
  have htrace : WordTrace (prefixWord ++ tailWord_3955133) baseStart_3955133 baseEnd_3955133 := by
    simpa [prefixWord, tailWord_3955133, baseEnd_3955133] using wordTrace_append hprefix tailTrace_3955133
  have hstable : (prefixWord ++ tailWord_3955133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955133).length < 2 ^ (prefixWord ++ tailWord_3955133).sum := by decide
  have hdescent : baseEnd_3955133 < baseStart_3955133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955144 : List Nat := [2, 1, 3, 1, 3, 2, 10]
def baseStart_3955144 : Nat := 118140960795 + 3955144 * 2 ^ 59
def prefixEnd_3955144 : Nat := 4983230072969 + 3 ^ 40 * 3955144 * 2
def baseEnd_3955144 : Nat := 50145430364108116410139

theorem tailTrace_3955144 : CollatzResearch.WordTrace tailWord_3955144 prefixEnd_3955144 50145430364108116410139 := by
  unfold tailWord_3955144
  simp only [CollatzResearch.WordTrace]
  refine ⟨72127976391598123831108243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96170635188797498441477657 72127976391598123831108243)
  ·
    refine ⟨108191964587397185746662365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72127976391598123831108243 108191964587397185746662365)
    ·
      refine ⟨40571986720273944654998387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108191964587397185746662365 40571986720273944654998387)
      ·
        refine ⟨60857980080410916982497581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571986720273944654998387 60857980080410916982497581)
        ·
          refine ⟨22821742530154093868436593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60857980080410916982497581 22821742530154093868436593)
          ·
            refine ⟨17116306897615570401327445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821742530154093868436593 17116306897615570401327445)
            ·
              refine ⟨50145430364108116410139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17116306897615570401327445 50145430364108116410139)
              ·
                rfl

theorem cell22_3955144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 10].length) (baseStart_3955144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955144 prefixEnd_3955144 := by exact prefixLift 3955144
  have htrace : WordTrace (prefixWord ++ tailWord_3955144) baseStart_3955144 baseEnd_3955144 := by
    simpa [prefixWord, tailWord_3955144, baseEnd_3955144] using wordTrace_append hprefix tailTrace_3955144
  have hstable : (prefixWord ++ tailWord_3955144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955144).length < 2 ^ (prefixWord ++ tailWord_3955144).sum := by decide
  have hdescent : baseEnd_3955144 < baseStart_3955144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955146 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3955146 : Nat := 118140960795 + 3955146 * 2 ^ 59
def prefixEnd_3955146 : Nat := 4983230072969 + 3 ^ 40 * 3955146 * 2
def baseEnd_3955146 : Nat := 1353927304471791804523747

theorem tailTrace_3955146 : CollatzResearch.WordTrace tailWord_3955146 prefixEnd_3955146 1353927304471791804523747 := by
  unfold tailWord_3955146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064006432297250500947323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96170683819459334669192861 36064006432297250500947323)
  ·
    refine ⟨54096009648445875751420985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36064006432297250500947323 54096009648445875751420985)
    ·
      refine ⟨40572007236334406813565739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54096009648445875751420985 40572007236334406813565739)
      ·
        refine ⟨60858010854501610220348609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40572007236334406813565739 60858010854501610220348609)
        ·
          refine ⟨45643508140876207665261457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60858010854501610220348609 45643508140876207665261457)
          ·
            refine ⟨34232631105657155748946093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45643508140876207665261457 34232631105657155748946093)
            ·
              refine ⟨12837236664621433405854785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34232631105657155748946093 12837236664621433405854785)
              ·
                refine ⟨9627927498466075054391089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12837236664621433405854785 9627927498466075054391089)
                ·
                  refine ⟨7220945623849556290793317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627927498466075054391089 7220945623849556290793317)
                  ·
                    refine ⟨1353927304471791804523747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7220945623849556290793317 1353927304471791804523747)
                    ·
                      rfl

theorem cell22_3955146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3955146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955146 prefixEnd_3955146 := by exact prefixLift 3955146
  have htrace : WordTrace (prefixWord ++ tailWord_3955146) baseStart_3955146 baseEnd_3955146 := by
    simpa [prefixWord, tailWord_3955146, baseEnd_3955146] using wordTrace_append hprefix tailTrace_3955146
  have hstable : (prefixWord ++ tailWord_3955146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955146).length < 2 ^ (prefixWord ++ tailWord_3955146).sum := by decide
  have hdescent : baseEnd_3955146 < baseStart_3955146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955210 : List Nat := [3, 1, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3955210 : Nat := 118140960795 + 3955210 * 2 ^ 59
def prefixEnd_3955210 : Nat := 4983230072969 + 3 ^ 40 * 3955210 * 2
def baseEnd_3955210 : Nat := 1353949212979716970923551

theorem tailTrace_3955210 : CollatzResearch.WordTrace tailWord_3955210 prefixEnd_3955210 1353949212979716970923551 := by
  unfold tailWord_3955210
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064590000239285233529771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96172240000638093956079389 36064590000239285233529771)
  ·
    refine ⟨54096885000358927850294657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36064590000239285233529771 54096885000358927850294657)
    ·
      refine ⟨40572663750269195887720993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54096885000358927850294657 40572663750269195887720993)
      ·
        refine ⟨30429497812701896915790745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40572663750269195887720993 30429497812701896915790745)
        ·
          refine ⟨22822123359526422686843059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30429497812701896915790745 22822123359526422686843059)
          ·
            refine ⟨34233185039289634030264589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822123359526422686843059 34233185039289634030264589)
            ·
              refine ⟨12837444389733612761349221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34233185039289634030264589 12837444389733612761349221)
              ·
                refine ⟨2407020823075052392752979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12837444389733612761349221 2407020823075052392752979)
                ·
                  refine ⟨3610531234612578589129469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407020823075052392752979 3610531234612578589129469)
                  ·
                    refine ⟨1353949212979716970923551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610531234612578589129469 1353949212979716970923551)
                    ·
                      rfl

theorem cell22_3955210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3955210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955210 prefixEnd_3955210 := by exact prefixLift 3955210
  have htrace : WordTrace (prefixWord ++ tailWord_3955210) baseStart_3955210 baseEnd_3955210 := by
    simpa [prefixWord, tailWord_3955210, baseEnd_3955210] using wordTrace_append hprefix tailTrace_3955210
  have hstable : (prefixWord ++ tailWord_3955210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955210).length < 2 ^ (prefixWord ++ tailWord_3955210).sum := by decide
  have hdescent : baseEnd_3955210 < baseStart_3955210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955221 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3955221 : Nat := 118140960795 + 3955221 * 2 ^ 59
def prefixEnd_3955221 : Nat := 4983230072969 + 3 ^ 40 * 3955221 * 2
def baseEnd_3955221 : Nat := 1353952978504516608898517

theorem tailTrace_3955221 : CollatzResearch.WordTrace tailWord_3955221 prefixEnd_3955221 1353952978504516608898517 := by
  unfold tailWord_3955221
  simp only [CollatzResearch.WordTrace]
  refine ⟨144258761203917289812769517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96172507469278193208513011 144258761203917289812769517)
  ·
    refine ⟨54097035451468983679788569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144258761203917289812769517 54097035451468983679788569)
    ·
      refine ⟨40572776588601737759841427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54097035451468983679788569 40572776588601737759841427)
      ·
        refine ⟨60859164882902606639762141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40572776588601737759841427 60859164882902606639762141)
        ·
          refine ⟨22822186831088477489910803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60859164882902606639762141 22822186831088477489910803)
          ·
            refine ⟨34233280246632716234866205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822186831088477489910803 34233280246632716234866205)
            ·
              refine ⟨12837480092487268588074827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34233280246632716234866205 12837480092487268588074827)
              ·
                refine ⟨19256220138730902882112241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12837480092487268588074827 19256220138730902882112241)
                ·
                  refine ⟨14442165104048177161584181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19256220138730902882112241 14442165104048177161584181)
                  ·
                    refine ⟨1353952978504516608898517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14442165104048177161584181 1353952978504516608898517)
                    ·
                      rfl

theorem cell22_3955221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3955221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955221 prefixEnd_3955221 := by exact prefixLift 3955221
  have htrace : WordTrace (prefixWord ++ tailWord_3955221) baseStart_3955221 baseEnd_3955221 := by
    simpa [prefixWord, tailWord_3955221, baseEnd_3955221] using wordTrace_append hprefix tailTrace_3955221
  have hstable : (prefixWord ++ tailWord_3955221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955221).length < 2 ^ (prefixWord ++ tailWord_3955221).sum := by decide
  have hdescent : baseEnd_3955221 < baseStart_3955221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955253 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3955253 : Nat := 118140960795 + 3955253 * 2 ^ 59
def prefixEnd_3955253 : Nat := 4983230072969 + 3 ^ 40 * 3955253 * 2
def baseEnd_3955253 : Nat := 1353963932758479192098419

theorem tailTrace_3955253 : CollatzResearch.WordTrace tailWord_3955253 prefixEnd_3955253 1353963932758479192098419 := by
  unfold tailWord_3955253
  simp only [CollatzResearch.WordTrace]
  refine ⟨144259928339801359277934413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96173285559867572851956275 144259928339801359277934413)
  ·
    refine ⟨54097473127425509729225405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144259928339801359277934413 54097473127425509729225405)
    ·
      refine ⟨20286552422784566148459527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54097473127425509729225405 20286552422784566148459527)
      ·
        refine ⟨30429828634176849222689291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20286552422784566148459527 30429828634176849222689291)
        ·
          refine ⟨45644742951265273834033937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30429828634176849222689291 45644742951265273834033937)
          ·
            refine ⟨34233557213448955375525453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45644742951265273834033937 34233557213448955375525453)
            ·
              refine ⟨12837583955043358265822045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34233557213448955375525453 12837583955043358265822045)
              ·
                refine ⟨4814093983141259349683267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12837583955043358265822045 4814093983141259349683267)
                ·
                  refine ⟨7221140974711889024524901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814093983141259349683267 7221140974711889024524901)
                  ·
                    refine ⟨1353963932758479192098419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221140974711889024524901 1353963932758479192098419)
                    ·
                      rfl

theorem cell22_3955253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3955253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955253 prefixEnd_3955253 := by exact prefixLift 3955253
  have htrace : WordTrace (prefixWord ++ tailWord_3955253) baseStart_3955253 baseEnd_3955253 := by
    simpa [prefixWord, tailWord_3955253, baseEnd_3955253] using wordTrace_append hprefix tailTrace_3955253
  have hstable : (prefixWord ++ tailWord_3955253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955253).length < 2 ^ (prefixWord ++ tailWord_3955253).sum := by decide
  have hdescent : baseEnd_3955253 < baseStart_3955253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955281 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3955281 : Nat := 118140960795 + 3955281 * 2 ^ 59
def prefixEnd_3955281 : Nat := 4983230072969 + 3 ^ 40 * 3955281 * 2
def baseEnd_3955281 : Nat := 1353973517730696452398333

theorem tailTrace_3955281 : CollatzResearch.WordTrace tailWord_3955281 prefixEnd_3955281 1353973517730696452398333 := by
  unfold tailWord_3955281
  simp only [CollatzResearch.WordTrace]
  refine ⟨144260949583699920059953697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96173966389133280039969131 144260949583699920059953697)
  ·
    refine ⟨108195712187774940044965273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144260949583699920059953697 108195712187774940044965273)
    ·
      refine ⟨81146784140831205033723955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108195712187774940044965273 81146784140831205033723955)
      ·
        refine ⟨121720176211246807550585933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81146784140831205033723955 121720176211246807550585933)
        ·
          refine ⟨45645066079217552831469725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121720176211246807550585933 45645066079217552831469725)
          ·
            refine ⟨17116899779706582311801147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45645066079217552831469725 17116899779706582311801147)
            ·
              refine ⟨25675349669559873467701721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17116899779706582311801147 25675349669559873467701721)
              ·
                refine ⟨19256512252169905100776291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25675349669559873467701721 19256512252169905100776291)
                ·
                  refine ⟨28884768378254857651164437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19256512252169905100776291 28884768378254857651164437)
                  ·
                    refine ⟨1353973517730696452398333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28884768378254857651164437 1353973517730696452398333)
                    ·
                      rfl

theorem cell22_3955281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3955281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955281 prefixEnd_3955281 := by exact prefixLift 3955281
  have htrace : WordTrace (prefixWord ++ tailWord_3955281) baseStart_3955281 baseEnd_3955281 := by
    simpa [prefixWord, tailWord_3955281, baseEnd_3955281] using wordTrace_append hprefix tailTrace_3955281
  have hstable : (prefixWord ++ tailWord_3955281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955281).length < 2 ^ (prefixWord ++ tailWord_3955281).sum := by decide
  have hdescent : baseEnd_3955281 < baseStart_3955281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955379 : List Nat := [1, 1, 1, 2, 3, 6, 2, 2, 1, 3]
def baseStart_3955379 : Nat := 118140960795 + 3955379 * 2 ^ 59
def prefixEnd_3955379 : Nat := 4983230072969 + 3 ^ 40 * 3955379 * 2
def baseEnd_3955379 : Nat := 1354007065133456863448033

theorem tailTrace_3955379 : CollatzResearch.WordTrace tailWord_3955379 prefixEnd_3955379 1354007065133456863448033 := by
  unfold tailWord_3955379
  simp only [CollatzResearch.WordTrace]
  refine ⟨144264523937344882797021191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96176349291563255198014127 144264523937344882797021191)
  ·
    refine ⟨216396785906017324195531787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144264523937344882797021191 216396785906017324195531787)
    ·
      refine ⟨324595178859025986293297681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216396785906017324195531787 324595178859025986293297681)
      ·
        refine ⟨243446384144269489719973261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324595178859025986293297681 243446384144269489719973261)
        ·
          refine ⟨91292394054101058644989973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243446384144269489719973261 91292394054101058644989973)
          ·
            refine ⟨4279330971285987123983905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91292394054101058644989973 4279330971285987123983905)
            ·
              refine ⟨3209498228464490342987929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279330971285987123983905 3209498228464490342987929)
              ·
                refine ⟨2407123671348367757240947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3209498228464490342987929 2407123671348367757240947)
                ·
                  refine ⟨3610685507022551635861421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407123671348367757240947 3610685507022551635861421)
                  ·
                    refine ⟨1354007065133456863448033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610685507022551635861421 1354007065133456863448033)
                    ·
                      rfl

theorem cell22_3955379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2, 1, 3].length) (baseStart_3955379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955379 prefixEnd_3955379 := by exact prefixLift 3955379
  have htrace : WordTrace (prefixWord ++ tailWord_3955379) baseStart_3955379 baseEnd_3955379 := by
    simpa [prefixWord, tailWord_3955379, baseEnd_3955379] using wordTrace_append hprefix tailTrace_3955379
  have hstable : (prefixWord ++ tailWord_3955379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955379).length < 2 ^ (prefixWord ++ tailWord_3955379).sum := by decide
  have hdescent : baseEnd_3955379 < baseStart_3955379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955388 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3955388 : Nat := 118140960795 + 3955388 * 2 ^ 59
def prefixEnd_3955388 : Nat := 4983230072969 + 3 ^ 40 * 3955388 * 2
def baseEnd_3955388 : Nat := 1354010146017383839973005

theorem tailTrace_3955388 : CollatzResearch.WordTrace tailWord_3955388 prefixEnd_3955388 1354010146017383839973005 := by
  unfold tailWord_3955388
  simp only [CollatzResearch.WordTrace]
  refine ⟨72132426097156138667049409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96176568129541518222732545 72132426097156138667049409)
  ·
    refine ⟨54099319572867104000287057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72132426097156138667049409 54099319572867104000287057)
    ·
      refine ⟨40574489679650328000215293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54099319572867104000287057 40574489679650328000215293)
      ·
        refine ⟨15215433629868873000080735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40574489679650328000215293 15215433629868873000080735)
        ·
          refine ⟨22823150444803309500121103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215433629868873000080735 22823150444803309500121103)
          ·
            refine ⟨34234725667204964250181655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22823150444803309500121103 34234725667204964250181655)
            ·
              refine ⟨51352088500807446375272483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34234725667204964250181655 51352088500807446375272483)
              ·
                refine ⟨77028132751211169562908725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51352088500807446375272483 77028132751211169562908725)
                ·
                  refine ⟨7221387445426047146522693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77028132751211169562908725 7221387445426047146522693)
                  ·
                    refine ⟨1354010146017383839973005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221387445426047146522693 1354010146017383839973005)
                    ·
                      rfl

theorem cell22_3955388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3955388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955388 prefixEnd_3955388 := by exact prefixLift 3955388
  have htrace : WordTrace (prefixWord ++ tailWord_3955388) baseStart_3955388 baseEnd_3955388 := by
    simpa [prefixWord, tailWord_3955388, baseEnd_3955388] using wordTrace_append hprefix tailTrace_3955388
  have hstable : (prefixWord ++ tailWord_3955388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955388).length < 2 ^ (prefixWord ++ tailWord_3955388).sum := by decide
  have hdescent : baseEnd_3955388 < baseStart_3955388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955418 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_3955418 : Nat := 118140960795 + 3955418 * 2 ^ 59
def prefixEnd_3955418 : Nat := 4983230072969 + 3 ^ 40 * 3955418 * 2
def baseEnd_3955418 : Nat := 1354020415630473761722913

theorem tailTrace_3955418 : CollatzResearch.WordTrace tailWord_3955418 prefixEnd_3955418 1354020415630473761722913 := by
  unfold tailWord_3955418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36066486596050898114422727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96177297589469061638460605 36066486596050898114422727)
  ·
    refine ⟨54099729894076347171634091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36066486596050898114422727 54099729894076347171634091)
    ·
      refine ⟨81149594841114520757451137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54099729894076347171634091 81149594841114520757451137)
      ·
        refine ⟨60862196130835890568088353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81149594841114520757451137 60862196130835890568088353)
        ·
          refine ⟨45646647098126917926066265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60862196130835890568088353 45646647098126917926066265)
          ·
            refine ⟨34234985323595188444549699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45646647098126917926066265 34234985323595188444549699)
            ·
              refine ⟨51352477985392782666824549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34234985323595188444549699 51352477985392782666824549)
              ·
                refine ⟨9628589622261146750029603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51352477985392782666824549 9628589622261146750029603)
                ·
                  refine ⟨14442884433391720125044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628589622261146750029603 14442884433391720125044405)
                  ·
                    refine ⟨1354020415630473761722913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14442884433391720125044405 1354020415630473761722913)
                    ·
                      rfl

theorem cell22_3955418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_3955418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955418 prefixEnd_3955418 := by exact prefixLift 3955418
  have htrace : WordTrace (prefixWord ++ tailWord_3955418) baseStart_3955418 baseEnd_3955418 := by
    simpa [prefixWord, tailWord_3955418, baseEnd_3955418] using wordTrace_append hprefix tailTrace_3955418
  have hstable : (prefixWord ++ tailWord_3955418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955418).length < 2 ^ (prefixWord ++ tailWord_3955418).sum := by decide
  have hdescent : baseEnd_3955418 < baseStart_3955418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955433 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_3955433 : Nat := 118140960795 + 3955433 * 2 ^ 59
def prefixEnd_3955433 : Nat := 4983230072969 + 3 ^ 40 * 3955433 * 2
def baseEnd_3955433 : Nat := 1354025550437018722597867

theorem tailTrace_3955433 : CollatzResearch.WordTrace tailWord_3955433 prefixEnd_3955433 1354025550437018722597867 := by
  unfold tailWord_3955433
  simp only [CollatzResearch.WordTrace]
  refine ⟨144266493479149250019486953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96177662319432833346324635 144266493479149250019486953)
  ·
    refine ⟨108199870109361937514615215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144266493479149250019486953 108199870109361937514615215)
    ·
      refine ⟨162299805164042906271922823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108199870109361937514615215 162299805164042906271922823)
      ·
        refine ⟨243449707746064359407884235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162299805164042906271922823 243449707746064359407884235)
        ·
          refine ⟨365174561619096539111826353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243449707746064359407884235 365174561619096539111826353)
          ·
            refine ⟨273880921214322404333869765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365174561619096539111826353 273880921214322404333869765)
            ·
              refine ⟨51352672727685450812600581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273880921214322404333869765 51352672727685450812600581)
              ·
                refine ⟨9628626136441022027362609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51352672727685450812600581 9628626136441022027362609)
                ·
                  refine ⟨7221469602330766520521957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9628626136441022027362609 7221469602330766520521957)
                  ·
                    refine ⟨1354025550437018722597867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7221469602330766520521957 1354025550437018722597867)
                    ·
                      rfl

theorem cell22_3955433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_3955433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955433 prefixEnd_3955433 := by exact prefixLift 3955433
  have htrace : WordTrace (prefixWord ++ tailWord_3955433) baseStart_3955433 baseEnd_3955433 := by
    simpa [prefixWord, tailWord_3955433, baseEnd_3955433] using wordTrace_append hprefix tailTrace_3955433
  have hstable : (prefixWord ++ tailWord_3955433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955433).length < 2 ^ (prefixWord ++ tailWord_3955433).sum := by decide
  have hdescent : baseEnd_3955433 < baseStart_3955433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955493 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 7]
def baseStart_3955493 : Nat := 118140960795 + 3955493 * 2 ^ 59
def prefixEnd_3955493 : Nat := 4983230072969 + 3 ^ 40 * 3955493 * 2
def baseEnd_3955493 : Nat := 451348696554399522032561

theorem tailTrace_3955493 : CollatzResearch.WordTrace tailWord_3955493 prefixEnd_3955493 451348696554399522032561 := by
  unfold tailWord_3955493
  simp only [CollatzResearch.WordTrace]
  refine ⟨144268681858931880266671133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96179121239287920177780755 144268681858931880266671133)
  ·
    refine ⟨54100755697099455100001675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144268681858931880266671133 54100755697099455100001675)
    ·
      refine ⟨81151133545649182650002513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54100755697099455100001675 81151133545649182650002513)
      ·
        refine ⟨60863350159236886987501885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81151133545649182650002513 60863350159236886987501885)
        ·
          refine ⟨22823756309713832620313207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60863350159236886987501885 22823756309713832620313207)
          ·
            refine ⟨34235634464570748930469811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22823756309713832620313207 34235634464570748930469811)
            ·
              refine ⟨51353451696856123395704717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34235634464570748930469811 51353451696856123395704717)
              ·
                refine ⟨19257544386321046273389269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51353451696856123395704717 19257544386321046273389269)
                ·
                  refine ⟨451348696554399522032561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19257544386321046273389269 451348696554399522032561)
                  ·
                    rfl

theorem cell22_3955493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_3955493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955493 prefixEnd_3955493 := by exact prefixLift 3955493
  have htrace : WordTrace (prefixWord ++ tailWord_3955493) baseStart_3955493 baseEnd_3955493 := by
    simpa [prefixWord, tailWord_3955493, baseEnd_3955493] using wordTrace_append hprefix tailTrace_3955493
  have hstable : (prefixWord ++ tailWord_3955493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955493).length < 2 ^ (prefixWord ++ tailWord_3955493).sum := by decide
  have hdescent : baseEnd_3955493 < baseStart_3955493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955548 : List Nat := [2, 2, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3955548 : Nat := 118140960795 + 3955548 * 2 ^ 59
def prefixEnd_3955548 : Nat := 4983230072969 + 3 ^ 40 * 3955548 * 2
def baseEnd_3955548 : Nat := 1354064917287196755972515

theorem tailTrace_3955548 : CollatzResearch.WordTrace tailWord_3955548 prefixEnd_3955548 1354064917287196755972515 := by
  unfold tailWord_3955548
  simp only [CollatzResearch.WordTrace]
  refine ⟨72135343936866312329961649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96180458582488416439948865 72135343936866312329961649)
  ·
    refine ⟨54101507952649734247471237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72135343936866312329961649 54101507952649734247471237)
    ·
      refine ⟨10144032741121825171400857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54101507952649734247471237 10144032741121825171400857)
      ·
        refine ⟨7608024555841368878550643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10144032741121825171400857 7608024555841368878550643)
        ·
          refine ⟨11412036833762053317825965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608024555841368878550643 11412036833762053317825965)
          ·
            refine ⟨4279513812660769994184737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11412036833762053317825965 4279513812660769994184737)
            ·
              refine ⟨3209635359495577495638553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279513812660769994184737 3209635359495577495638553)
              ·
                refine ⟨2407226519621683121728915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3209635359495577495638553 2407226519621683121728915)
                ·
                  refine ⟨3610839779432524682593373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407226519621683121728915 3610839779432524682593373)
                  ·
                    refine ⟨1354064917287196755972515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610839779432524682593373 1354064917287196755972515)
                    ·
                      rfl

theorem cell22_3955548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3955548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955548 prefixEnd_3955548 := by exact prefixLift 3955548
  have htrace : WordTrace (prefixWord ++ tailWord_3955548) baseStart_3955548 baseEnd_3955548 := by
    simpa [prefixWord, tailWord_3955548, baseEnd_3955548] using wordTrace_append hprefix tailTrace_3955548
  have hstable : (prefixWord ++ tailWord_3955548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955548).length < 2 ^ (prefixWord ++ tailWord_3955548).sum := by decide
  have hdescent : baseEnd_3955548 < baseStart_3955548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955570 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3955570 : Nat := 118140960795 + 3955570 * 2 ^ 59
def prefixEnd_3955570 : Nat := 4983230072969 + 3 ^ 40 * 3955570 * 2
def baseEnd_3955570 : Nat := 1354072448336796031922447

theorem tailTrace_3955570 : CollatzResearch.WordTrace tailWord_3955570 prefixEnd_3955570 1354072448336796031922447 := by
  unfold tailWord_3955570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067872569913230604306041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96180993519768614944816109 36067872569913230604306041)
  ·
    refine ⟨27050904427434922953229531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36067872569913230604306041 27050904427434922953229531)
    ·
      refine ⟨40576356641152384429844297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27050904427434922953229531 40576356641152384429844297)
      ·
        refine ⟨30432267480864288322383223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40576356641152384429844297 30432267480864288322383223)
        ·
          refine ⟨45648401221296432483574835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30432267480864288322383223 45648401221296432483574835)
          ·
            refine ⟨68472601831944648725362253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45648401221296432483574835 68472601831944648725362253)
            ·
              refine ⟨25677225686979243272010845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68472601831944648725362253 25677225686979243272010845)
              ·
                refine ⟨9628959632617216227004067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25677225686979243272010845 9628959632617216227004067)
                ·
                  refine ⟨14443439448925824340506101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628959632617216227004067 14443439448925824340506101)
                  ·
                    refine ⟨1354072448336796031922447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14443439448925824340506101 1354072448336796031922447)
                    ·
                      rfl

theorem cell22_3955570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3955570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955570 prefixEnd_3955570 := by exact prefixLift 3955570
  have htrace : WordTrace (prefixWord ++ tailWord_3955570) baseStart_3955570 baseEnd_3955570 := by
    simpa [prefixWord, tailWord_3955570, baseEnd_3955570] using wordTrace_append hprefix tailTrace_3955570
  have hstable : (prefixWord ++ tailWord_3955570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955570).length < 2 ^ (prefixWord ++ tailWord_3955570).sum := by decide
  have hdescent : baseEnd_3955570 < baseStart_3955570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955583 : List Nat := [1, 1, 2, 2, 1, 1, 4, 10]
def baseStart_3955583 : Nat := 118140960795 + 3955583 * 2 ^ 59
def prefixEnd_3955583 : Nat := 4983230072969 + 3 ^ 40 * 3955583 * 2
def baseEnd_3955583 : Nat := 150452988722496481260823

theorem tailTrace_3955583 : CollatzResearch.WordTrace tailWord_3955583 prefixEnd_3955583 150452988722496481260823 := by
  unfold tailWord_3955583
  simp only [CollatzResearch.WordTrace]
  refine ⟨144271964428605825637447403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96181309619070550424964935 144271964428605825637447403)
  ·
    refine ⟨216407946642908738456171105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144271964428605825637447403 216407946642908738456171105)
    ·
      refine ⟨162305959982181553842128329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216407946642908738456171105 162305959982181553842128329)
      ·
        refine ⟨121729469986636165381596247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162305959982181553842128329 121729469986636165381596247)
        ·
          refine ⟨182594204979954248072394371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121729469986636165381596247 182594204979954248072394371)
          ·
            refine ⟨273891307469931372108591557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182594204979954248072394371 273891307469931372108591557)
            ·
              refine ⟨51354620150612132270360917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273891307469931372108591557 51354620150612132270360917)
              ·
                refine ⟨150452988722496481260823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51354620150612132270360917 150452988722496481260823)
                ·
                  rfl

theorem cell22_3955583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 10].length) (baseStart_3955583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955583 prefixEnd_3955583 := by exact prefixLift 3955583
  have htrace : WordTrace (prefixWord ++ tailWord_3955583) baseStart_3955583 baseEnd_3955583 := by
    simpa [prefixWord, tailWord_3955583, baseEnd_3955583] using wordTrace_append hprefix tailTrace_3955583
  have hstable : (prefixWord ++ tailWord_3955583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955583).length < 2 ^ (prefixWord ++ tailWord_3955583).sum := by decide
  have hdescent : baseEnd_3955583 < baseStart_3955583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955606 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3955606 : Nat := 118140960795 + 3955606 * 2 ^ 59
def prefixEnd_3955606 : Nat := 4983230072969 + 3 ^ 40 * 3955606 * 2
def baseEnd_3955606 : Nat := 451361590624167979340779

theorem tailTrace_3955606 : CollatzResearch.WordTrace tailWord_3955606 prefixEnd_3955606 451361590624167979340779 := by
  unfold tailWord_3955606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017050206720156285345917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96181868871681667043689781 9017050206720156285345917)
  ·
    refine ⟨3381393827520058607004719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9017050206720156285345917 3381393827520058607004719)
    ·
      refine ⟨5072090741280087910507079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381393827520058607004719 5072090741280087910507079)
      ·
        refine ⟨7608136111920131865760619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5072090741280087910507079 7608136111920131865760619)
        ·
          refine ⟨11412204167880197798640929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608136111920131865760619 11412204167880197798640929)
          ·
            refine ⟨8559153125910148348980697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11412204167880197798640929 8559153125910148348980697)
            ·
              refine ⟨6419364844432611261735523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8559153125910148348980697 6419364844432611261735523)
              ·
                refine ⟨9629047266648916892603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419364844432611261735523 9629047266648916892603285)
                ·
                  refine ⟨451361590624167979340779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9629047266648916892603285 451361590624167979340779)
                  ·
                    rfl

theorem cell22_3955606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3955606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955606 prefixEnd_3955606 := by exact prefixLift 3955606
  have htrace : WordTrace (prefixWord ++ tailWord_3955606) baseStart_3955606 baseEnd_3955606 := by
    simpa [prefixWord, tailWord_3955606, baseEnd_3955606] using wordTrace_append hprefix tailTrace_3955606
  have hstable : (prefixWord ++ tailWord_3955606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955606).length < 2 ^ (prefixWord ++ tailWord_3955606).sum := by decide
  have hdescent : baseEnd_3955606 < baseStart_3955606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955666 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3955666 : Nat := 118140960795 + 3955666 * 2 ^ 59
def prefixEnd_3955666 : Nat := 4983230072969 + 3 ^ 40 * 3955666 * 2
def baseEnd_3955666 : Nat := 1354105311098683781522153

theorem tailTrace_3955666 : CollatzResearch.WordTrace tailWord_3955666 prefixEnd_3955666 1354105311098683781522153 := by
  unfold tailWord_3955666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36068747921826282703179713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96183327791536753875145901 36068747921826282703179713)
  ·
    refine ⟨27051560941369712027384785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36068747921826282703179713 27051560941369712027384785)
    ·
      refine ⟨20288670706027284020538589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27051560941369712027384785 20288670706027284020538589)
      ·
        refine ⟨7608251514760231507701971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20288670706027284020538589 7608251514760231507701971)
        ·
          refine ⟨11412377272140347261552957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7608251514760231507701971 11412377272140347261552957)
          ·
            refine ⟨4279641477052630223082359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11412377272140347261552957 4279641477052630223082359)
            ·
              refine ⟨6419462215578945334623539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279641477052630223082359 6419462215578945334623539)
              ·
                refine ⟨9629193323368418001935309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419462215578945334623539 9629193323368418001935309)
                ·
                  refine ⟨3610947496263156750725741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9629193323368418001935309 3610947496263156750725741)
                  ·
                    refine ⟨1354105311098683781522153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610947496263156750725741 1354105311098683781522153)
                    ·
                      rfl

theorem cell22_3955666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3955666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955666 prefixEnd_3955666 := by exact prefixLift 3955666
  have htrace : WordTrace (prefixWord ++ tailWord_3955666) baseStart_3955666 baseEnd_3955666 := by
    simpa [prefixWord, tailWord_3955666, baseEnd_3955666] using wordTrace_append hprefix tailTrace_3955666
  have hstable : (prefixWord ++ tailWord_3955666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955666).length < 2 ^ (prefixWord ++ tailWord_3955666).sum := by decide
  have hdescent : baseEnd_3955666 < baseStart_3955666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955707 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 4]
def baseStart_3955707 : Nat := 118140960795 + 3955707 * 2 ^ 59
def prefixEnd_3955707 : Nat := 4983230072969 + 3 ^ 40 * 3955707 * 2
def baseEnd_3955707 : Nat := 451373115412191113749009

theorem tailTrace_3955707 : CollatzResearch.WordTrace tailWord_3955707 prefixEnd_3955707 451373115412191113749009 := by
  unfold tailWord_3955707
  simp only [CollatzResearch.WordTrace]
  refine ⟨144276487080156594814961375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96184324720104396543307583 144276487080156594814961375)
  ·
    refine ⟨216414730620234892222442063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144276487080156594814961375 216414730620234892222442063)
    ·
      refine ⟨324622095930352338333663095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216414730620234892222442063 324622095930352338333663095)
      ·
        refine ⟨486933143895528507500494643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324622095930352338333663095 486933143895528507500494643)
        ·
          refine ⟨730399715843292761250741965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486933143895528507500494643 730399715843292761250741965)
          ·
            refine ⟨273899893441234785469028237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 730399715843292761250741965 273899893441234785469028237)
            ·
              refine ⟨102712460040463044550885589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273899893441234785469028237 102712460040463044550885589)
              ·
                refine ⟨2407323282198352606661381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102712460040463044550885589 2407323282198352606661381)
                ·
                  refine ⟨451373115412191113749009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407323282198352606661381 451373115412191113749009)
                  ·
                    rfl

theorem cell22_3955707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 4].length) (baseStart_3955707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955707 prefixEnd_3955707 := by exact prefixLift 3955707
  have htrace : WordTrace (prefixWord ++ tailWord_3955707) baseStart_3955707 baseEnd_3955707 := by
    simpa [prefixWord, tailWord_3955707, baseEnd_3955707] using wordTrace_append hprefix tailTrace_3955707
  have hstable : (prefixWord ++ tailWord_3955707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955707).length < 2 ^ (prefixWord ++ tailWord_3955707).sum := by decide
  have hdescent : baseEnd_3955707 < baseStart_3955707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955724 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_3955724 : Nat := 118140960795 + 3955724 * 2 ^ 59
def prefixEnd_3955724 : Nat := 4983230072969 + 3 ^ 40 * 3955724 * 2
def baseEnd_3955724 : Nat := 451375055227996987857325

theorem tailTrace_3955724 : CollatzResearch.WordTrace tailWord_3955724 prefixEnd_3955724 451375055227996987857325 := by
  unfold tailWord_3955724
  simp only [CollatzResearch.WordTrace]
  refine ⟨72138553560547503359165113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96184738080730004478886817 72138553560547503359165113)
  ·
    refine ⟨54103915170410627519373835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72138553560547503359165113 54103915170410627519373835)
    ·
      refine ⟨81155872755615941279060753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54103915170410627519373835 81155872755615941279060753)
      ·
        refine ⟨60866904566711955959295565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81155872755615941279060753 60866904566711955959295565)
        ·
          refine ⟨22825089212516983484735837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60866904566711955959295565 22825089212516983484735837)
          ·
            refine ⟨8559408454693868806775939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22825089212516983484735837 8559408454693868806775939)
            ·
              refine ⟨12839112682040803210163909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559408454693868806775939 12839112682040803210163909)
              ·
                refine ⟨2407333627882650601905733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12839112682040803210163909 2407333627882650601905733)
                ·
                  refine ⟨451375055227996987857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407333627882650601905733 451375055227996987857325)
                  ·
                    rfl

theorem cell22_3955724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_3955724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955724 prefixEnd_3955724 := by exact prefixLift 3955724
  have htrace : WordTrace (prefixWord ++ tailWord_3955724) baseStart_3955724 baseEnd_3955724 := by
    simpa [prefixWord, tailWord_3955724, baseEnd_3955724] using wordTrace_append hprefix tailTrace_3955724
  have hstable : (prefixWord ++ tailWord_3955724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955724).length < 2 ^ (prefixWord ++ tailWord_3955724).sum := by decide
  have hdescent : baseEnd_3955724 < baseStart_3955724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955754 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3955754 : Nat := 118140960795 + 3955754 * 2 ^ 59
def prefixEnd_3955754 : Nat := 4983230072969 + 3 ^ 40 * 3955754 * 2
def baseEnd_3955754 : Nat := 1354135435297080885321883

theorem tailTrace_3955754 : CollatzResearch.WordTrace tailWord_3955754 prefixEnd_3955754 1354135435297080885321883 := by
  unfold tailWord_3955754
  simp only [CollatzResearch.WordTrace]
  refine ⟨36069550327746580460480579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96185467540657547894614877 36069550327746580460480579)
  ·
    refine ⟨54104325491619870690720869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36069550327746580460480579 54104325491619870690720869)
    ·
      refine ⟨10144561029678725754510163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54104325491619870690720869 10144561029678725754510163)
      ·
        refine ⟨15216841544518088631765245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10144561029678725754510163 15216841544518088631765245)
        ·
          refine ⟨5706315579194283236911967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15216841544518088631765245 5706315579194283236911967)
          ·
            refine ⟨8559473368791424855367951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706315579194283236911967 8559473368791424855367951)
            ·
              refine ⟨12839210053187137283051927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559473368791424855367951 12839210053187137283051927)
              ·
                refine ⟨19258815079780705924577891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12839210053187137283051927 19258815079780705924577891)
                ·
                  refine ⟨28888222619671058886866837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19258815079780705924577891 28888222619671058886866837)
                  ·
                    refine ⟨1354135435297080885321883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28888222619671058886866837 1354135435297080885321883)
                    ·
                      rfl

theorem cell22_3955754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3955754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955754 prefixEnd_3955754 := by exact prefixLift 3955754
  have htrace : WordTrace (prefixWord ++ tailWord_3955754) baseStart_3955754 baseEnd_3955754 := by
    simpa [prefixWord, tailWord_3955754, baseEnd_3955754] using wordTrace_append hprefix tailTrace_3955754
  have hstable : (prefixWord ++ tailWord_3955754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955754).length < 2 ^ (prefixWord ++ tailWord_3955754).sum := by decide
  have hdescent : baseEnd_3955754 < baseStart_3955754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955767 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 7, 3]
def baseStart_3955767 : Nat := 118140960795 + 3955767 * 2 ^ 59
def prefixEnd_3955767 : Nat := 4983230072969 + 3 ^ 40 * 3955767 * 2
def baseEnd_3955767 : Nat := 1354139885462753184746843

theorem tailTrace_3955767 : CollatzResearch.WordTrace tailWord_3955767 prefixEnd_3955767 1354139885462753184746843 := by
  unfold tailWord_3955767
  simp only [CollatzResearch.WordTrace]
  refine ⟨144278675459939225062145555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96185783639959483374763703 144278675459939225062145555)
  ·
    refine ⟨216418013189908837593218333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144278675459939225062145555 216418013189908837593218333)
    ·
      refine ⟨81156754946215814097456875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216418013189908837593218333 81156754946215814097456875)
      ·
        refine ⟨121735132419323721146185313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81156754946215814097456875 121735132419323721146185313)
        ·
          refine ⟨91301349314492790859638985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121735132419323721146185313 91301349314492790859638985)
          ·
            refine ⟨68476011985869593144729239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91301349314492790859638985 68476011985869593144729239)
            ·
              refine ⟨102714017978804389717093859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68476011985869593144729239 102714017978804389717093859)
              ·
                refine ⟨154071026968206584575640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102714017978804389717093859 154071026968206584575640789)
                ·
                  refine ⟨3611039694567341825991581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 154071026968206584575640789 3611039694567341825991581)
                  ·
                    refine ⟨1354139885462753184746843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611039694567341825991581 1354139885462753184746843)
                    ·
                      rfl

theorem cell22_3955767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_3955767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955767 prefixEnd_3955767 := by exact prefixLift 3955767
  have htrace : WordTrace (prefixWord ++ tailWord_3955767) baseStart_3955767 baseEnd_3955767 := by
    simpa [prefixWord, tailWord_3955767, baseEnd_3955767] using wordTrace_append hprefix tailTrace_3955767
  have hstable : (prefixWord ++ tailWord_3955767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955767).length < 2 ^ (prefixWord ++ tailWord_3955767).sum := by decide
  have hdescent : baseEnd_3955767 < baseStart_3955767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955784 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_3955784 : Nat := 118140960795 + 3955784 * 2 ^ 59
def prefixEnd_3955784 : Nat := 4983230072969 + 3 ^ 40 * 3955784 * 2
def baseEnd_3955784 : Nat := 1354145704910170807071791

theorem tailTrace_3955784 : CollatzResearch.WordTrace tailWord_3955784 prefixEnd_3955784 1354145704910170807071791 := by
  unfold tailWord_3955784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72139647750438818482757203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96186197000585091310342937 72139647750438818482757203)
  ·
    refine ⟨108209471625658227724135805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72139647750438818482757203 108209471625658227724135805)
    ·
      refine ⟨40578551859621835396550927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108209471625658227724135805 40578551859621835396550927)
      ·
        refine ⟨60867827789432753094826391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40578551859621835396550927 60867827789432753094826391)
        ·
          refine ⟨91301741684149129642239587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60867827789432753094826391 91301741684149129642239587)
          ·
            refine ⟨136952612526223694463359381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91301741684149129642239587 136952612526223694463359381)
            ·
              refine ⟨6419653712166735677969971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136952612526223694463359381 6419653712166735677969971)
              ·
                refine ⟨9629480568250103516954957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6419653712166735677969971 9629480568250103516954957)
                ·
                  refine ⟨3611055213093788818858109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9629480568250103516954957 3611055213093788818858109)
                  ·
                    refine ⟨1354145704910170807071791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611055213093788818858109 1354145704910170807071791)
                    ·
                      rfl

theorem cell22_3955784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_3955784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955784 prefixEnd_3955784 := by exact prefixLift 3955784
  have htrace : WordTrace (prefixWord ++ tailWord_3955784) baseStart_3955784 baseEnd_3955784 := by
    simpa [prefixWord, tailWord_3955784, baseEnd_3955784] using wordTrace_append hprefix tailTrace_3955784
  have hstable : (prefixWord ++ tailWord_3955784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955784).length < 2 ^ (prefixWord ++ tailWord_3955784).sum := by decide
  have hdescent : baseEnd_3955784 < baseStart_3955784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955818 : List Nat := [3, 1, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3955818 : Nat := 118140960795 + 3955818 * 2 ^ 59
def prefixEnd_3955818 : Nat := 4983230072969 + 3 ^ 40 * 3955818 * 2
def baseEnd_3955818 : Nat := 1354157343805006051721687

theorem tailTrace_3955818 : CollatzResearch.WordTrace tailWord_3955818 prefixEnd_3955818 1354157343805006051721687 := by
  unfold tailWord_3955818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36070133895688615193063027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96187023721836307181501405 36070133895688615193063027)
  ·
    refine ⟨54105200843532922789594541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36070133895688615193063027 54105200843532922789594541)
    ·
      refine ⟨20289450316324846046097953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54105200843532922789594541 20289450316324846046097953)
      ·
        refine ⟨15217087737243634534573465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20289450316324846046097953 15217087737243634534573465)
        ·
          refine ⟨11412815802932725900930099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15217087737243634534573465 11412815802932725900930099)
          ·
            refine ⟨17119223704399088851395149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11412815802932725900930099 17119223704399088851395149)
            ·
              refine ⟨6419708889149658319273181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17119223704399088851395149 6419708889149658319273181)
              ·
                refine ⟨2407390833431121869727443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6419708889149658319273181 2407390833431121869727443)
                ·
                  refine ⟨3611086250146682804591165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407390833431121869727443 3611086250146682804591165)
                  ·
                    refine ⟨1354157343805006051721687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611086250146682804591165 1354157343805006051721687)
                    ·
                      rfl

theorem cell22_3955818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3955818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955818 prefixEnd_3955818 := by exact prefixLift 3955818
  have htrace : WordTrace (prefixWord ++ tailWord_3955818) baseStart_3955818 baseEnd_3955818 := by
    simpa [prefixWord, tailWord_3955818, baseEnd_3955818] using wordTrace_append hprefix tailTrace_3955818
  have hstable : (prefixWord ++ tailWord_3955818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955818).length < 2 ^ (prefixWord ++ tailWord_3955818).sum := by decide
  have hdescent : baseEnd_3955818 < baseStart_3955818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955848 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_3955848 : Nat := 118140960795 + 3955848 * 2 ^ 59
def prefixEnd_3955848 : Nat := 4983230072969 + 3 ^ 40 * 3955848 * 2
def baseEnd_3955848 : Nat := 451389204472698657823865

theorem tailTrace_3955848 : CollatzResearch.WordTrace tailWord_3955848 prefixEnd_3955848 451389204472698657823865 := by
  unfold tailWord_3955848
  simp only [CollatzResearch.WordTrace]
  refine ⟨72140814886322887947922099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96187753181763850597229465 72140814886322887947922099)
  ·
    refine ⟨108211222329484331921883149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72140814886322887947922099 108211222329484331921883149)
    ·
      refine ⟨40579208373556624470706181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108211222329484331921883149 40579208373556624470706181)
      ·
        refine ⟨7608601570041867088257409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40579208373556624470706181 7608601570041867088257409)
        ·
          refine ⟨5706451177531400316193057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7608601570041867088257409 5706451177531400316193057)
          ·
            refine ⟨4279838383148550237144793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5706451177531400316193057 4279838383148550237144793)
            ·
              refine ⟨3209878787361412677858595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279838383148550237144793 3209878787361412677858595)
              ·
                refine ⟨4814818181042119016787893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209878787361412677858595 4814818181042119016787893)
                ·
                  refine ⟨451389204472698657823865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4814818181042119016787893 451389204472698657823865)
                  ·
                    rfl

theorem cell22_3955848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_3955848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955848 prefixEnd_3955848 := by exact prefixLift 3955848
  have htrace : WordTrace (prefixWord ++ tailWord_3955848) baseStart_3955848 baseEnd_3955848 := by
    simpa [prefixWord, tailWord_3955848, baseEnd_3955848] using wordTrace_append hprefix tailTrace_3955848
  have hstable : (prefixWord ++ tailWord_3955848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955848).length < 2 ^ (prefixWord ++ tailWord_3955848).sum := by decide
  have hdescent : baseEnd_3955848 < baseStart_3955848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955910 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3955910 : Nat := 118140960795 + 3955910 * 2 ^ 59
def prefixEnd_3955910 : Nat := 4983230072969 + 3 ^ 40 * 3955910 * 2
def baseEnd_3955910 : Nat := 451396279095049492807135

theorem tailTrace_3955910 : CollatzResearch.WordTrace tailWord_3955910 prefixEnd_3955910 451396279095049492807135 := by
  unfold tailWord_3955910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508871596825661265143787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96189260732280773656400789 4508871596825661265143787)
  ·
    refine ⟨6763307395238491897715681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4508871596825661265143787 6763307395238491897715681)
    ·
      refine ⟨5072480546428868923286761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6763307395238491897715681 5072480546428868923286761)
      ·
        refine ⟨3804360409821651692465071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5072480546428868923286761 3804360409821651692465071)
        ·
          refine ⟨5706540614732477538697607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804360409821651692465071 5706540614732477538697607)
          ·
            refine ⟨8559810922098716308046411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706540614732477538697607 8559810922098716308046411)
            ·
              refine ⟨12839716383148074462069617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559810922098716308046411 12839716383148074462069617)
              ·
                refine ⟨9629787287361055846552213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12839716383148074462069617 9629787287361055846552213)
                ·
                  refine ⟨451396279095049492807135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9629787287361055846552213 451396279095049492807135)
                  ·
                    rfl

theorem cell22_3955910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3955910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955910 prefixEnd_3955910 := by exact prefixLift 3955910
  have htrace : WordTrace (prefixWord ++ tailWord_3955910) baseStart_3955910 baseEnd_3955910 := by
    simpa [prefixWord, tailWord_3955910, baseEnd_3955910] using wordTrace_append hprefix tailTrace_3955910
  have hstable : (prefixWord ++ tailWord_3955910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955910).length < 2 ^ (prefixWord ++ tailWord_3955910).sum := by decide
  have hdescent : baseEnd_3955910 < baseStart_3955910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3955996 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3955996 : Nat := 118140960795 + 3955996 * 2 ^ 59
def prefixEnd_3955996 : Nat := 4983230072969 + 3 ^ 40 * 3955996 * 2
def baseEnd_3955996 : Nat := 1354218276842672920771141

theorem tailTrace_3955996 : CollatzResearch.WordTrace tailWord_3955996 prefixEnd_3955996 1354218276842672920771141 := by
  unfold tailWord_3955996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72143513888054798586115921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96191351850739731448154561 72143513888054798586115921)
  ·
    refine ⟨54107635416041098939586941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72143513888054798586115921 54107635416041098939586941)
    ·
      refine ⟨20290363281015412102345103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54107635416041098939586941 20290363281015412102345103)
      ·
        refine ⟨30435544921523118153517655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290363281015412102345103 30435544921523118153517655)
        ·
          refine ⟨45653317382284677230276483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30435544921523118153517655 45653317382284677230276483)
          ·
            refine ⟨68479976073427015845414725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45653317382284677230276483 68479976073427015845414725)
            ·
              refine ⟨12839995513767565471015261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68479976073427015845414725 12839995513767565471015261)
              ·
                refine ⟨4814998317662837051630723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12839995513767565471015261 4814998317662837051630723)
                ·
                  refine ⟨7222497476494255577446085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814998317662837051630723 7222497476494255577446085)
                  ·
                    refine ⟨1354218276842672920771141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222497476494255577446085 1354218276842672920771141)
                    ·
                      rfl

theorem cell22_3955996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3955996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3955996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3955996 prefixEnd_3955996 := by exact prefixLift 3955996
  have htrace : WordTrace (prefixWord ++ tailWord_3955996) baseStart_3955996 baseEnd_3955996 := by
    simpa [prefixWord, tailWord_3955996, baseEnd_3955996] using wordTrace_append hprefix tailTrace_3955996
  have hstable : (prefixWord ++ tailWord_3955996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3955996).length < 2 ^ (prefixWord ++ tailWord_3955996).sum := by decide
  have hdescent : baseEnd_3955996 < baseStart_3955996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3955996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956024 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3956024 : Nat := 118140960795 + 3956024 * 2 ^ 59
def prefixEnd_3956024 : Nat := 4983230072969 + 3 ^ 40 * 3956024 * 2
def baseEnd_3956024 : Nat := 1354227861814890181071055

theorem tailTrace_3956024 : CollatzResearch.WordTrace tailWord_3956024 prefixEnd_3956024 1354227861814890181071055 := by
  unfold tailWord_3956024
  simp only [CollatzResearch.WordTrace]
  refine ⟨72144024510004078977125563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96192032680005438636167417 72144024510004078977125563)
  ·
    refine ⟨108216036765006118465688345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72144024510004078977125563 108216036765006118465688345)
    ·
      refine ⟨81162027573754588849266259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108216036765006118465688345 81162027573754588849266259)
      ·
        refine ⟨121743041360631883273899389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81162027573754588849266259 121743041360631883273899389)
        ·
          refine ⟨45653640510236956227712271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121743041360631883273899389 45653640510236956227712271)
          ·
            refine ⟨68480460765355434341568407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45653640510236956227712271 68480460765355434341568407)
            ·
              refine ⟨102720691148033151512352611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68480460765355434341568407 102720691148033151512352611)
              ·
                refine ⟨154081036722049727268528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102720691148033151512352611 154081036722049727268528917)
                ·
                  refine ⟨7222548596346080965712293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154081036722049727268528917 7222548596346080965712293)
                  ·
                    refine ⟨1354227861814890181071055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222548596346080965712293 1354227861814890181071055)
                    ·
                      rfl

theorem cell22_3956024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3956024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956024 prefixEnd_3956024 := by exact prefixLift 3956024
  have htrace : WordTrace (prefixWord ++ tailWord_3956024) baseStart_3956024 baseEnd_3956024 := by
    simpa [prefixWord, tailWord_3956024, baseEnd_3956024] using wordTrace_append hprefix tailTrace_3956024
  have hstable : (prefixWord ++ tailWord_3956024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956024).length < 2 ^ (prefixWord ++ tailWord_3956024).sum := by decide
  have hdescent : baseEnd_3956024 < baseStart_3956024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956039 : List Nat := [1, 1, 4, 1, 2, 3, 2, 8]
def baseStart_3956039 : Nat := 118140960795 + 3956039 * 2 ^ 59
def prefixEnd_3956039 : Nat := 4983230072969 + 3 ^ 40 * 3956039 * 2
def baseEnd_3956039 : Nat := 150470332957937237994001

theorem tailTrace_3956039 : CollatzResearch.WordTrace tailWord_3956039 prefixEnd_3956039 150470332957937237994001 := by
  unfold tailWord_3956039
  simp only [CollatzResearch.WordTrace]
  refine ⟨144288596114953815516047171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96192397409969210344031447 144288596114953815516047171)
  ·
    refine ⟨216432894172430723274070757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144288596114953815516047171 216432894172430723274070757)
    ·
      refine ⟨40581167657330760613888267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216432894172430723274070757 40581167657330760613888267)
      ·
        refine ⟨60871751485996140920832401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40581167657330760613888267 60871751485996140920832401)
        ·
          refine ⟨45653813614497105690624301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60871751485996140920832401 45653813614497105690624301)
          ·
            refine ⟨17120180105436414633984113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45653813614497105690624301 17120180105436414633984113)
            ·
              refine ⟨12840135079077310975488085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17120180105436414633984113 12840135079077310975488085)
              ·
                refine ⟨150470332957937237994001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12840135079077310975488085 150470332957937237994001)
                ·
                  rfl

theorem cell22_3956039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 8].length) (baseStart_3956039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956039 prefixEnd_3956039 := by exact prefixLift 3956039
  have htrace : WordTrace (prefixWord ++ tailWord_3956039) baseStart_3956039 baseEnd_3956039 := by
    simpa [prefixWord, tailWord_3956039, baseEnd_3956039] using wordTrace_append hprefix tailTrace_3956039
  have hstable : (prefixWord ++ tailWord_3956039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956039).length < 2 ^ (prefixWord ++ tailWord_3956039).sum := by decide
  have hdescent : baseEnd_3956039 < baseStart_3956039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956069 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3956069 : Nat := 118140960795 + 3956069 * 2 ^ 59
def prefixEnd_3956069 : Nat := 4983230072969 + 3 ^ 40 * 3956069 * 2
def baseEnd_3956069 : Nat := 1354243266234525063695917

theorem tailTrace_3956069 : CollatzResearch.WordTrace tailWord_3956069 prefixEnd_3956069 1354243266234525063695917 := by
  unfold tailWord_3956069
  simp only [CollatzResearch.WordTrace]
  refine ⟨144289690304845130639639261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96193126869896753759759507 144289690304845130639639261)
  ·
    refine ⟨54108633864316923989864723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144289690304845130639639261 54108633864316923989864723)
    ·
      refine ⟨81162950796475385984797085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54108633864316923989864723 81162950796475385984797085)
      ·
        refine ⟨30436106548678269744298907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81162950796475385984797085 30436106548678269744298907)
        ·
          refine ⟨45654159823017404616448361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30436106548678269744298907 45654159823017404616448361)
          ·
            refine ⟨34240619867263053462336271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45654159823017404616448361 34240619867263053462336271)
            ·
              refine ⟨51360929800894580193504407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34240619867263053462336271 51360929800894580193504407)
              ·
                refine ⟨77041394701341870290256611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51360929800894580193504407 77041394701341870290256611)
                ·
                  refine ⟨115562092052012805435384917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77041394701341870290256611 115562092052012805435384917)
                  ·
                    refine ⟨1354243266234525063695917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115562092052012805435384917 1354243266234525063695917)
                    ·
                      rfl

theorem cell22_3956069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3956069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956069 prefixEnd_3956069 := by exact prefixLift 3956069
  have htrace : WordTrace (prefixWord ++ tailWord_3956069) baseStart_3956069 baseEnd_3956069 := by
    simpa [prefixWord, tailWord_3956069, baseEnd_3956069] using wordTrace_append hprefix tailTrace_3956069
  have hstable : (prefixWord ++ tailWord_3956069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956069).length < 2 ^ (prefixWord ++ tailWord_3956069).sum := by decide
  have hdescent : baseEnd_3956069 < baseStart_3956069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956163 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 4]
def baseStart_3956163 : Nat := 118140960795 + 3956163 * 2 ^ 59
def prefixEnd_3956163 : Nat := 4983230072969 + 3 ^ 40 * 3956163 * 2
def baseEnd_3956163 : Nat := 451425148118513383948543

theorem tailTrace_3956163 : CollatzResearch.WordTrace tailWord_3956163 prefixEnd_3956163 451425148118513383948543 := by
  unfold tailWord_3956163
  simp only [CollatzResearch.WordTrace]
  refine ⟨144293118766504584693561143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96195412511003056462374095 144293118766504584693561143)
  ·
    refine ⟨216439678149756877040341715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144293118766504584693561143 216439678149756877040341715)
    ·
      refine ⟨324659517224635315560512573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216439678149756877040341715 324659517224635315560512573)
      ·
        refine ⟨121747318959238243335192215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 324659517224635315560512573 121747318959238243335192215)
        ·
          refine ⟨182620978438857365002788323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121747318959238243335192215 182620978438857365002788323)
          ·
            refine ⟨273931467658286047504182485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182620978438857365002788323 273931467658286047504182485)
            ·
              refine ⟨6420268773241079238379277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 273931467658286047504182485 6420268773241079238379277)
              ·
                refine ⟨2407600789965404714392229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6420268773241079238379277 2407600789965404714392229)
                ·
                  refine ⟨451425148118513383948543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407600789965404714392229 451425148118513383948543)
                  ·
                    rfl

theorem cell22_3956163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 4].length) (baseStart_3956163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956163 prefixEnd_3956163 := by exact prefixLift 3956163
  have htrace : WordTrace (prefixWord ++ tailWord_3956163) baseStart_3956163 baseEnd_3956163 := by
    simpa [prefixWord, tailWord_3956163, baseEnd_3956163] using wordTrace_append hprefix tailTrace_3956163
  have hstable : (prefixWord ++ tailWord_3956163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956163).length < 2 ^ (prefixWord ++ tailWord_3956163).sum := by decide
  have hdescent : baseEnd_3956163 < baseStart_3956163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956176 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_3956176 : Nat := 118140960795 + 3956176 * 2 ^ 59
def prefixEnd_3956176 : Nat := 4983230072969 + 3 ^ 40 * 3956176 * 2
def baseEnd_3956176 : Nat := 1354279894521212451270589

theorem tailTrace_3956176 : CollatzResearch.WordTrace tailWord_3956176 prefixEnd_3956176 1354279894521212451270589 := by
  unfold tailWord_3956176
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146796457728743956892191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96195728610304991942522921 72146796457728743956892191)
  ·
    refine ⟨108220194686593115935338287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72146796457728743956892191 108220194686593115935338287)
    ·
      refine ⟨162330292029889673903007431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108220194686593115935338287 162330292029889673903007431)
      ·
        refine ⟨243495438044834510854511147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162330292029889673903007431 243495438044834510854511147)
        ·
          refine ⟨365243157067251766281766721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243495438044834510854511147 365243157067251766281766721)
          ·
            refine ⟨273932367800438824711325041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365243157067251766281766721 273932367800438824711325041)
            ·
              refine ⟨205449275850329118533493781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273932367800438824711325041 205449275850329118533493781)
              ·
                refine ⟨9630434805484177431257521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205449275850329118533493781 9630434805484177431257521)
                ·
                  refine ⟨7222826104113133073443141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630434805484177431257521 7222826104113133073443141)
                  ·
                    refine ⟨1354279894521212451270589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222826104113133073443141 1354279894521212451270589)
                    ·
                      rfl

theorem cell22_3956176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_3956176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956176 prefixEnd_3956176 := by exact prefixLift 3956176
  have htrace : WordTrace (prefixWord ++ tailWord_3956176) baseStart_3956176 baseEnd_3956176 := by
    simpa [prefixWord, tailWord_3956176, baseEnd_3956176] using wordTrace_append hprefix tailTrace_3956176
  have hstable : (prefixWord ++ tailWord_3956176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956176).length < 2 ^ (prefixWord ++ tailWord_3956176).sum := by decide
  have hdescent : baseEnd_3956176 < baseStart_3956176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956180 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_3956180 : Nat := 118140960795 + 3956180 * 2 ^ 59
def prefixEnd_3956180 : Nat := 4983230072969 + 3 ^ 40 * 3956180 * 2
def baseEnd_3956180 : Nat := 451427087934319258056859

theorem tailTrace_3956180 : CollatzResearch.WordTrace tailWord_3956180 prefixEnd_3956180 451427087934319258056859 := by
  unfold tailWord_3956180
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146869403721498298464997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96195825871628664397953329 72146869403721498298464997)
  ·
    refine ⟨13527538013197780930962187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72146869403721498298464997 13527538013197780930962187)
    ·
      refine ⟨20291307019796671396443281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13527538013197780930962187 20291307019796671396443281)
      ·
        refine ⟨15218480264847503547332461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20291307019796671396443281 15218480264847503547332461)
        ·
          refine ⟨5706930099317813830249673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15218480264847503547332461 5706930099317813830249673)
          ·
            refine ⟨4280197574488360372687255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5706930099317813830249673 4280197574488360372687255)
            ·
              refine ⟨6420296361732540559030883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280197574488360372687255 6420296361732540559030883)
              ·
                refine ⟨9630444542598810838546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420296361732540559030883 9630444542598810838546325)
                ·
                  refine ⟨451427087934319258056859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9630444542598810838546325 451427087934319258056859)
                  ·
                    rfl

theorem cell22_3956180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_3956180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956180 prefixEnd_3956180 := by exact prefixLift 3956180
  have htrace : WordTrace (prefixWord ++ tailWord_3956180) baseStart_3956180 baseEnd_3956180 := by
    simpa [prefixWord, tailWord_3956180, baseEnd_3956180] using wordTrace_append hprefix tailTrace_3956180
  have hstable : (prefixWord ++ tailWord_3956180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956180).length < 2 ^ (prefixWord ++ tailWord_3956180).sum := by decide
  have hdescent : baseEnd_3956180 < baseStart_3956180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956191 : List Nat := [1, 1, 2, 3, 3, 1, 4, 7]
def baseStart_3956191 : Nat := 118140960795 + 3956191 * 2 ^ 59
def prefixEnd_3956191 : Nat := 4983230072969 + 3 ^ 40 * 3956191 * 2
def baseEnd_3956191 : Nat := 150476114369750823571727

theorem tailTrace_3956191 : CollatzResearch.WordTrace tailWord_3956191 prefixEnd_3956191 150476114369750823571727 := by
  unfold tailWord_3956191
  simp only [CollatzResearch.WordTrace]
  refine ⟨144294140010403145475580427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96196093340268763650386951 144294140010403145475580427)
  ·
    refine ⟨216441210015604718213370641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144294140010403145475580427 216441210015604718213370641)
    ·
      refine ⟨162330907511703538660027981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216441210015604718213370641 162330907511703538660027981)
      ·
        refine ⟨60874090316888826997510493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162330907511703538660027981 60874090316888826997510493)
        ·
          refine ⟨22827783868833310124066435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60874090316888826997510493 22827783868833310124066435)
          ·
            refine ⟨34241675803249965186099653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22827783868833310124066435 34241675803249965186099653)
            ·
              refine ⟨6420314213109368472393685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34241675803249965186099653 6420314213109368472393685)
              ·
                refine ⟨150476114369750823571727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6420314213109368472393685 150476114369750823571727)
                ·
                  rfl

theorem cell22_3956191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 7].length) (baseStart_3956191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956191 prefixEnd_3956191 := by exact prefixLift 3956191
  have htrace : WordTrace (prefixWord ++ tailWord_3956191) baseStart_3956191 baseEnd_3956191 := by
    simpa [prefixWord, tailWord_3956191, baseEnd_3956191] using wordTrace_append hprefix tailTrace_3956191
  have hstable : (prefixWord ++ tailWord_3956191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956191).length < 2 ^ (prefixWord ++ tailWord_3956191).sum := by decide
  have hdescent : baseEnd_3956191 < baseStart_3956191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956195 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 2, 3]
def baseStart_3956195 : Nat := 118140960795 + 3956195 * 2 ^ 59
def prefixEnd_3956195 : Nat := 4983230072969 + 3 ^ 40 * 3956195 * 2
def baseEnd_3956195 : Nat := 1354286398609502735045531

theorem tailTrace_3956195 : CollatzResearch.WordTrace tailWord_3956195 prefixEnd_3956195 1354286398609502735045531 := by
  unfold tailWord_3956195
  simp only [CollatzResearch.WordTrace]
  refine ⟨144294285902388654158726039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96196190601592436105817359 144294285902388654158726039)
  ·
    refine ⟨216441428853582981238089059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144294285902388654158726039 216441428853582981238089059)
    ·
      refine ⟨324662143280374471857133589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216441428853582981238089059 324662143280374471857133589)
      ·
        refine ⟨15218537966267553368303137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 324662143280374471857133589 15218537966267553368303137)
        ·
          refine ⟨11413903474700665026227353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15218537966267553368303137 11413903474700665026227353)
          ·
            refine ⟨8560427606025498769670515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11413903474700665026227353 8560427606025498769670515)
            ·
              refine ⟨12840641409038248154505773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560427606025498769670515 12840641409038248154505773)
              ·
                refine ⟨4815240528389343057939665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12840641409038248154505773 4815240528389343057939665)
                ·
                  refine ⟨3611430396292007293454749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815240528389343057939665 3611430396292007293454749)
                  ·
                    refine ⟨1354286398609502735045531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611430396292007293454749 1354286398609502735045531)
                    ·
                      rfl

theorem cell22_3956195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].length) (baseStart_3956195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956195 prefixEnd_3956195 := by exact prefixLift 3956195
  have htrace : WordTrace (prefixWord ++ tailWord_3956195) baseStart_3956195 baseEnd_3956195 := by
    simpa [prefixWord, tailWord_3956195, baseEnd_3956195] using wordTrace_append hprefix tailTrace_3956195
  have hstable : (prefixWord ++ tailWord_3956195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956195).length < 2 ^ (prefixWord ++ tailWord_3956195).sum := by decide
  have hdescent : baseEnd_3956195 < baseStart_3956195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956210 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3956210 : Nat := 118140960795 + 3956210 * 2 ^ 59
def prefixEnd_3956210 : Nat := 4983230072969 + 3 ^ 40 * 3956210 * 2
def baseEnd_3956210 : Nat := 1354291533416047695920485

theorem tailTrace_3956210 : CollatzResearch.WordTrace tailWord_3956210 prefixEnd_3956210 1354291533416047695920485 := by
  unfold tailWord_3956210
  simp only [CollatzResearch.WordTrace]
  refine ⟨36073708249333577930130521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96196555331556207813681389 36073708249333577930130521)
  ·
    refine ⟨27055281187000183447597891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36073708249333577930130521 27055281187000183447597891)
    ·
      refine ⟨40582921780500275171396837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27055281187000183447597891 40582921780500275171396837)
      ·
        refine ⟨7609297833843801594636907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40582921780500275171396837 7609297833843801594636907)
        ·
          refine ⟨11413946750765702391955361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7609297833843801594636907 11413946750765702391955361)
          ·
            refine ⟨8560460063074276793966521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11413946750765702391955361 8560460063074276793966521)
            ·
              refine ⟨6420345047305707595474891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560460063074276793966521 6420345047305707595474891)
              ·
                refine ⟨9630517570958561393212337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420345047305707595474891 9630517570958561393212337)
                ·
                  refine ⟨7222888178218921044909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630517570958561393212337 7222888178218921044909253)
                  ·
                    refine ⟨1354291533416047695920485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222888178218921044909253 1354291533416047695920485)
                    ·
                      rfl

theorem cell22_3956210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3956210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956210 prefixEnd_3956210 := by exact prefixLift 3956210
  have htrace : WordTrace (prefixWord ++ tailWord_3956210) baseStart_3956210 baseEnd_3956210 := by
    simpa [prefixWord, tailWord_3956210, baseEnd_3956210] using wordTrace_append hprefix tailTrace_3956210
  have hstable : (prefixWord ++ tailWord_3956210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956210).length < 2 ^ (prefixWord ++ tailWord_3956210).sum := by decide
  have hdescent : baseEnd_3956210 < baseStart_3956210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956253 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3956253 : Nat := 118140960795 + 3956253 * 2 ^ 59
def prefixEnd_3956253 : Nat := 4983230072969 + 3 ^ 40 * 3956253 * 2
def baseEnd_3956253 : Nat := 451435417731603305698451

theorem tailTrace_3956253 : CollatzResearch.WordTrace tailWord_3956253 prefixEnd_3956253 451435417731603305698451 := by
  unfold tailWord_3956253
  simp only [CollatzResearch.WordTrace]
  refine ⟨144296401336178530064337413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96197600890785686709558275 144296401336178530064337413)
  ·
    refine ⟨27055575250533474387063265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144296401336178530064337413 27055575250533474387063265)
    ·
      refine ⟨20291681437900105790297449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27055575250533474387063265 20291681437900105790297449)
      ·
        refine ⟨15218761078425079342723087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20291681437900105790297449 15218761078425079342723087)
        ·
          refine ⟨22828141617637619014084631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218761078425079342723087 22828141617637619014084631)
          ·
            refine ⟨34242212426456428521126947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22828141617637619014084631 34242212426456428521126947)
            ·
              refine ⟨51363318639684642781690421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34242212426456428521126947 51363318639684642781690421)
              ·
                refine ⟨4815311122470435260783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51363318639684642781690421 4815311122470435260783477)
                ·
                  refine ⟨451435417731603305698451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4815311122470435260783477 451435417731603305698451)
                  ·
                    rfl

theorem cell22_3956253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3956253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956253 prefixEnd_3956253 := by exact prefixLift 3956253
  have htrace : WordTrace (prefixWord ++ tailWord_3956253) baseStart_3956253 baseEnd_3956253 := by
    simpa [prefixWord, tailWord_3956253, baseEnd_3956253] using wordTrace_append hprefix tailTrace_3956253
  have hstable : (prefixWord ++ tailWord_3956253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956253).length < 2 ^ (prefixWord ++ tailWord_3956253).sum := by decide
  have hdescent : baseEnd_3956253 < baseStart_3956253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956296 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_3956296 : Nat := 118140960795 + 3956296 * 2 ^ 59
def prefixEnd_3956296 : Nat := 4983230072969 + 3 ^ 40 * 3956296 * 2
def baseEnd_3956296 : Nat := 1354320972973572138270221

theorem tailTrace_3956296 : CollatzResearch.WordTrace tailWord_3956296 prefixEnd_3956296 1354320972973572138270221 := by
  unfold tailWord_3956296
  simp only [CollatzResearch.WordTrace]
  refine ⟨72148984837511374204076371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96198646450015165605435161 72148984837511374204076371)
  ·
    refine ⟨108223477256267061306114557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72148984837511374204076371 108223477256267061306114557)
    ·
      refine ⟨40583803971100147989792959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108223477256267061306114557 40583803971100147989792959)
      ·
        refine ⟨60875705956650221984689439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40583803971100147989792959 60875705956650221984689439)
        ·
          refine ⟨91313558934975332977034159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60875705956650221984689439 91313558934975332977034159)
          ·
            refine ⟨136970338402462999465551239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91313558934975332977034159 136970338402462999465551239)
            ·
              refine ⟨205455507603694499198326859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136970338402462999465551239 205455507603694499198326859)
              ·
                refine ⟨308183261405541748797490289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205455507603694499198326859 308183261405541748797490289)
                ·
                  refine ⟨231137446054156311598117717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308183261405541748797490289 231137446054156311598117717)
                  ·
                    refine ⟨1354320972973572138270221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231137446054156311598117717 1354320972973572138270221)
                    ·
                      rfl

theorem cell22_3956296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_3956296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956296 prefixEnd_3956296 := by exact prefixLift 3956296
  have htrace : WordTrace (prefixWord ++ tailWord_3956296) baseStart_3956296 baseEnd_3956296 := by
    simpa [prefixWord, tailWord_3956296, baseEnd_3956296] using wordTrace_append hprefix tailTrace_3956296
  have hstable : (prefixWord ++ tailWord_3956296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956296).length < 2 ^ (prefixWord ++ tailWord_3956296).sum := by decide
  have hdescent : baseEnd_3956296 < baseStart_3956296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956298 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_3956298 : Nat := 118140960795 + 3956298 * 2 ^ 59
def prefixEnd_3956298 : Nat := 4983230072969 + 3 ^ 40 * 3956298 * 2
def baseEnd_3956298 : Nat := 451440552538148266573405

theorem tailTrace_3956298 : CollatzResearch.WordTrace tailWord_3956298 prefixEnd_3956298 451440552538148266573405 := by
  unfold tailWord_3956298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074510655253875687431387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96198695080677001833150365 36074510655253875687431387)
  ·
    refine ⟨54111765982880813531147081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36074510655253875687431387 54111765982880813531147081)
    ·
      refine ⟨40583824487160610148360311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54111765982880813531147081 40583824487160610148360311)
      ·
        refine ⟨60875736730740915222540467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40583824487160610148360311 60875736730740915222540467)
        ·
          refine ⟨91313605096111372833810701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60875736730740915222540467 91313605096111372833810701)
          ·
            refine ⟨34242601911041764812679013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91313605096111372833810701 34242601911041764812679013)
            ·
              refine ⟨6420487858320330902377315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34242601911041764812679013 6420487858320330902377315)
              ·
                refine ⟨9630731787480496353565973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420487858320330902377315 9630731787480496353565973)
                ·
                  refine ⟨451440552538148266573405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9630731787480496353565973 451440552538148266573405)
                  ·
                    rfl

theorem cell22_3956298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_3956298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956298 prefixEnd_3956298 := by exact prefixLift 3956298
  have htrace : WordTrace (prefixWord ++ tailWord_3956298) baseStart_3956298 baseEnd_3956298 := by
    simpa [prefixWord, tailWord_3956298, baseEnd_3956298] using wordTrace_append hprefix tailTrace_3956298
  have hstable : (prefixWord ++ tailWord_3956298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956298).length < 2 ^ (prefixWord ++ tailWord_3956298).sum := by decide
  have hdescent : baseEnd_3956298 < baseStart_3956298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956330 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3956330 : Nat := 118140960795 + 3956330 * 2 ^ 59
def prefixEnd_3956330 : Nat := 4983230072969 + 3 ^ 40 * 3956330 * 2
def baseEnd_3956330 : Nat := 1354332611868407382920117

theorem tailTrace_3956330 : CollatzResearch.WordTrace tailWord_3956330 prefixEnd_3956330 1354332611868407382920117 := by
  unfold tailWord_3956330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074802439224893053722611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96199473171266381476593629 36074802439224893053722611)
  ·
    refine ⟨54112203658837339580583917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36074802439224893053722611 54112203658837339580583917)
    ·
      refine ⟨20292076372064002342718969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54112203658837339580583917 20292076372064002342718969)
      ·
        refine ⟨15219057279048001757039227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20292076372064002342718969 15219057279048001757039227)
        ·
          refine ⟨22828585918572002635558841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219057279048001757039227 22828585918572002635558841)
          ·
            refine ⟨17121439438929001976669131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22828585918572002635558841 17121439438929001976669131)
            ·
              refine ⟨25682159158393502965003697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121439438929001976669131 25682159158393502965003697)
              ·
                refine ⟨19261619368795127223752773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682159158393502965003697 19261619368795127223752773)
                ·
                  refine ⟨3611553631649086354453645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19261619368795127223752773 3611553631649086354453645)
                  ·
                    refine ⟨1354332611868407382920117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611553631649086354453645 1354332611868407382920117)
                    ·
                      rfl

theorem cell22_3956330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3956330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956330 prefixEnd_3956330 := by exact prefixLift 3956330
  have htrace : WordTrace (prefixWord ++ tailWord_3956330) baseStart_3956330 baseEnd_3956330 := by
    simpa [prefixWord, tailWord_3956330, baseEnd_3956330] using wordTrace_append hprefix tailTrace_3956330
  have hstable : (prefixWord ++ tailWord_3956330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956330).length < 2 ^ (prefixWord ++ tailWord_3956330).sum := by decide
  have hdescent : baseEnd_3956330 < baseStart_3956330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956403 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_3956403 : Nat := 118140960795 + 3956403 * 2 ^ 59
def prefixEnd_3956403 : Nat := 4983230072969 + 3 ^ 40 * 3956403 * 2
def baseEnd_3956403 : Nat := 1354357601260259525844893

theorem tailTrace_3956403 : CollatzResearch.WordTrace tailWord_3956403 prefixEnd_3956403 1354357601260259525844893 := by
  unfold tailWord_3956403
  simp only [CollatzResearch.WordTrace]
  refine ⟨144301872285635105682297863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96201248190423403788198575 144301872285635105682297863)
  ·
    refine ⟨216452808428452658523446795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144301872285635105682297863 216452808428452658523446795)
    ·
      refine ⟨324679212642678987785170193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216452808428452658523446795 324679212642678987785170193)
      ·
        refine ⟨243509409482009240838877645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324679212642678987785170193 243509409482009240838877645)
        ·
          refine ⟨91316028555753465314579117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243509409482009240838877645 91316028555753465314579117)
          ·
            refine ⟨34243510708407549492967169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91316028555753465314579117 34243510708407549492967169)
            ·
              refine ⟨25682633031305662119725377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34243510708407549492967169 25682633031305662119725377)
              ·
                refine ⟨19261974773479246589794033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25682633031305662119725377 19261974773479246589794033)
                ·
                  refine ⟨14446481080109434942345525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19261974773479246589794033 14446481080109434942345525)
                  ·
                    refine ⟨1354357601260259525844893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14446481080109434942345525 1354357601260259525844893)
                    ·
                      rfl

theorem cell22_3956403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_3956403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956403 prefixEnd_3956403 := by exact prefixLift 3956403
  have htrace : WordTrace (prefixWord ++ tailWord_3956403) baseStart_3956403 baseEnd_3956403 := by
    simpa [prefixWord, tailWord_3956403, baseEnd_3956403] using wordTrace_append hprefix tailTrace_3956403
  have hstable : (prefixWord ++ tailWord_3956403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956403).length < 2 ^ (prefixWord ++ tailWord_3956403).sum := by decide
  have hdescent : baseEnd_3956403 < baseStart_3956403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956409 : List Nat := [1, 2, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_3956409 : Nat := 118140960795 + 3956409 * 2 ^ 59
def prefixEnd_3956409 : Nat := 4983230072969 + 3 ^ 40 * 3956409 * 2
def baseEnd_3956409 : Nat := 1354359655182877510194875

theorem tailTrace_3956409 : CollatzResearch.WordTrace tailWord_3956409 prefixEnd_3956409 1354359655182877510194875 := by
  unfold tailWord_3956409
  simp only [CollatzResearch.WordTrace]
  refine ⟨144302091123613368707016281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96201394082408912471344187 144302091123613368707016281)
  ·
    refine ⟨108226568342710026530262211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144302091123613368707016281 108226568342710026530262211)
    ·
      refine ⟨162339852514065039795393317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108226568342710026530262211 162339852514065039795393317)
      ·
        refine ⟨30438722346387194961636247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162339852514065039795393317 30438722346387194961636247)
        ·
          refine ⟨45658083519580792442454371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30438722346387194961636247 45658083519580792442454371)
          ·
            refine ⟨68487125279371188663681557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45658083519580792442454371 68487125279371188663681557)
            ·
              refine ⟨3210333997470524468610073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68487125279371188663681557 3210333997470524468610073)
              ·
                refine ⟨2407750498102893351457555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210333997470524468610073 2407750498102893351457555)
                ·
                  refine ⟨3611625747154340027186333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407750498102893351457555 3611625747154340027186333)
                  ·
                    refine ⟨1354359655182877510194875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611625747154340027186333 1354359655182877510194875)
                    ·
                      rfl

theorem cell22_3956409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_3956409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956409 prefixEnd_3956409 := by exact prefixLift 3956409
  have htrace : WordTrace (prefixWord ++ tailWord_3956409) baseStart_3956409 baseEnd_3956409 := by
    simpa [prefixWord, tailWord_3956409, baseEnd_3956409] using wordTrace_append hprefix tailTrace_3956409
  have hstable : (prefixWord ++ tailWord_3956409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956409).length < 2 ^ (prefixWord ++ tailWord_3956409).sum := by decide
  have hdescent : baseEnd_3956409 < baseStart_3956409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956420 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3956420 : Nat := 118140960795 + 3956420 * 2 ^ 59
def prefixEnd_3956420 : Nat := 4983230072969 + 3 ^ 40 * 3956420 * 2
def baseEnd_3956420 : Nat := 1354363420707677148169841

theorem tailTrace_3956420 : CollatzResearch.WordTrace tailWord_3956420 prefixEnd_3956420 1354363420707677148169841 := by
  unfold tailWord_3956420
  simp only [CollatzResearch.WordTrace]
  refine ⟨72151246163286758792833357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96201661551049011723777809 72151246163286758792833357)
  ·
    refine ⟨27056717311232534547312509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72151246163286758792833357 27056717311232534547312509)
    ·
      refine ⟨10146268991712200455242191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27056717311232534547312509 10146268991712200455242191)
      ·
        refine ⟨15219403487568300682863287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146268991712200455242191 15219403487568300682863287)
        ·
          refine ⟨22829105231352451024294931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15219403487568300682863287 22829105231352451024294931)
          ·
            refine ⟨34243657847028676536442397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22829105231352451024294931 34243657847028676536442397)
            ·
              refine ⟨12841371692635753701165899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34243657847028676536442397 12841371692635753701165899)
              ·
                refine ⟨19262057538953630551748849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12841371692635753701165899 19262057538953630551748849)
                ·
                  refine ⟨14446543154215222913811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19262057538953630551748849 14446543154215222913811637)
                  ·
                    refine ⟨1354363420707677148169841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14446543154215222913811637 1354363420707677148169841)
                    ·
                      rfl

theorem cell22_3956420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3956420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956420 prefixEnd_3956420 := by exact prefixLift 3956420
  have htrace : WordTrace (prefixWord ++ tailWord_3956420) baseStart_3956420 baseEnd_3956420 := by
    simpa [prefixWord, tailWord_3956420, baseEnd_3956420] using wordTrace_append hprefix tailTrace_3956420
  have hstable : (prefixWord ++ tailWord_3956420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956420).length < 2 ^ (prefixWord ++ tailWord_3956420).sum := by decide
  have hdescent : baseEnd_3956420 < baseStart_3956420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956433 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 8]
def baseStart_3956433 : Nat := 118140960795 + 3956433 * 2 ^ 59
def prefixEnd_3956433 : Nat := 4983230072969 + 3 ^ 40 * 3956433 * 2
def baseEnd_3956433 : Nat := 451455956957783149198267

theorem tailTrace_3956433 : CollatzResearch.WordTrace tailWord_3956433 prefixEnd_3956433 451455956957783149198267 := by
  unfold tailWord_3956433
  simp only [CollatzResearch.WordTrace]
  refine ⟨144302966475526420805889953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96201977650350947203926635 144302966475526420805889953)
  ·
    refine ⟨108227224856644815604417465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144302966475526420805889953 108227224856644815604417465)
    ·
      refine ⟨81170418642483611703313099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108227224856644815604417465 81170418642483611703313099)
      ·
        refine ⟨121755627963725417554969649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81170418642483611703313099 121755627963725417554969649)
        ·
          refine ⟨91316720972794063166227237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121755627963725417554969649 91316720972794063166227237)
          ·
            refine ⟨17121885182398886843667607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91316720972794063166227237 17121885182398886843667607)
            ·
              refine ⟨25682827773598330265501411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17121885182398886843667607 25682827773598330265501411)
              ·
                refine ⟨38524241660397495398252117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25682827773598330265501411 38524241660397495398252117)
                ·
                  refine ⟨451455956957783149198267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38524241660397495398252117 451455956957783149198267)
                  ·
                    rfl

theorem cell22_3956433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_3956433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956433 prefixEnd_3956433 := by exact prefixLift 3956433
  have htrace : WordTrace (prefixWord ++ tailWord_3956433) baseStart_3956433 baseEnd_3956433 := by
    simpa [prefixWord, tailWord_3956433, baseEnd_3956433] using wordTrace_append hprefix tailTrace_3956433
  have hstable : (prefixWord ++ tailWord_3956433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956433).length < 2 ^ (prefixWord ++ tailWord_3956433).sum := by decide
  have hdescent : baseEnd_3956433 < baseStart_3956433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956523 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 11]
def baseStart_3956523 : Nat := 118140960795 + 3956523 * 2 ^ 59
def prefixEnd_3956523 : Nat := 4983230072969 + 3 ^ 40 * 3956523 * 2
def baseEnd_3956523 : Nat := 451466226570873070948175

theorem tailTrace_3956523 : CollatzResearch.WordTrace tailWord_3956523 prefixEnd_3956523 451466226570873070948175 := by
  unfold tailWord_3956523
  simp only [CollatzResearch.WordTrace]
  refine ⟨144306249045200366176666223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96204166030133577451110815 144306249045200366176666223)
  ·
    refine ⟨216459373567800549264999335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144306249045200366176666223 216459373567800549264999335)
    ·
      refine ⟨324689060351700823897499003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216459373567800549264999335 324689060351700823897499003)
      ·
        refine ⟨487033590527551235846248505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324689060351700823897499003 487033590527551235846248505)
        ·
          refine ⟨365275192895663426884686379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487033590527551235846248505 365275192895663426884686379)
          ·
            refine ⟨547912789343495140327029569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365275192895663426884686379 547912789343495140327029569)
            ·
              refine ⟨410934592007621355245272177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547912789343495140327029569 410934592007621355245272177)
              ·
                refine ⟨308200944005716016433954133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410934592007621355245272177 308200944005716016433954133)
                ·
                  refine ⟨451466226570873070948175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 308200944005716016433954133 451466226570873070948175)
                  ·
                    rfl

theorem cell22_3956523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_3956523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956523 prefixEnd_3956523 := by exact prefixLift 3956523
  have htrace : WordTrace (prefixWord ++ tailWord_3956523) baseStart_3956523 baseEnd_3956523 := by
    simpa [prefixWord, tailWord_3956523, baseEnd_3956523] using wordTrace_append hprefix tailTrace_3956523
  have hstable : (prefixWord ++ tailWord_3956523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956523).length < 2 ^ (prefixWord ++ tailWord_3956523).sum := by decide
  have hdescent : baseEnd_3956523 < baseStart_3956523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956533 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3956533 : Nat := 118140960795 + 3956533 * 2 ^ 59
def prefixEnd_3956533 : Nat := 4983230072969 + 3 ^ 40 * 3956533 * 2
def baseEnd_3956533 : Nat := 1354402102916982520094495

theorem tailTrace_3956533 : CollatzResearch.WordTrace tailWord_3956533 prefixEnd_3956533 1354402102916982520094495 := by
  unfold tailWord_3956533
  simp only [CollatzResearch.WordTrace]
  refine ⟨144306613775164137884530253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96204409183442758589686835 144306613775164137884530253)
  ·
    refine ⟨54114980165686551706698845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144306613775164137884530253 54114980165686551706698845)
    ·
      refine ⟨20293117562132456890012067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54114980165686551706698845 20293117562132456890012067)
      ·
        refine ⟨30439676343198685335018101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20293117562132456890012067 30439676343198685335018101)
        ·
          refine ⟨2853719657174876750157947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30439676343198685335018101 2853719657174876750157947)
          ·
            refine ⟨4280579485762315125236921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853719657174876750157947 4280579485762315125236921)
            ·
              refine ⟨3210434614321736343927691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280579485762315125236921 3210434614321736343927691)
              ·
                refine ⟨4815651921482604515891537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210434614321736343927691 4815651921482604515891537)
                ·
                  refine ⟨3611738941111953386918653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4815651921482604515891537 3611738941111953386918653)
                  ·
                    refine ⟨1354402102916982520094495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611738941111953386918653 1354402102916982520094495)
                    ·
                      rfl

theorem cell22_3956533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3956533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956533 prefixEnd_3956533 := by exact prefixLift 3956533
  have htrace : WordTrace (prefixWord ++ tailWord_3956533) baseStart_3956533 baseEnd_3956533 := by
    simpa [prefixWord, tailWord_3956533, baseEnd_3956533] using wordTrace_append hprefix tailTrace_3956533
  have hstable : (prefixWord ++ tailWord_3956533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956533).length < 2 ^ (prefixWord ++ tailWord_3956533).sum := by decide
  have hdescent : baseEnd_3956533 < baseStart_3956533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956578 : List Nat := [3, 3, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3956578 : Nat := 118140960795 + 3956578 * 2 ^ 59
def prefixEnd_3956578 : Nat := 4983230072969 + 3 ^ 40 * 3956578 * 2
def baseEnd_3956578 : Nat := 1354417507336617402719357

theorem tailTrace_3956578 : CollatzResearch.WordTrace tailWord_3956578 prefixEnd_3956578 1354417507336617402719357 := by
  unfold tailWord_3956578
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077063765000277642479597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96205503373334073713278925 36077063765000277642479597)
  ·
    refine ⟨13528898911875104115929849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36077063765000277642479597 13528898911875104115929849)
    ·
      refine ⟨10146674183906328086947387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13528898911875104115929849 10146674183906328086947387)
      ·
        refine ⟨15220011275859492130421081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146674183906328086947387 15220011275859492130421081)
        ·
          refine ⟨11415008456894619097815811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15220011275859492130421081 11415008456894619097815811)
          ·
            refine ⟨17122512685341928646723717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415008456894619097815811 17122512685341928646723717)
            ·
              refine ⟨3210471128501611621260697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17122512685341928646723717 3210471128501611621260697)
              ·
                refine ⟨2407853346376208715945523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210471128501611621260697 2407853346376208715945523)
                ·
                  refine ⟨3611780019564313073918285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407853346376208715945523 3611780019564313073918285)
                  ·
                    refine ⟨1354417507336617402719357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611780019564313073918285 1354417507336617402719357)
                    ·
                      rfl

theorem cell22_3956578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3956578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956578 prefixEnd_3956578 := by exact prefixLift 3956578
  have htrace : WordTrace (prefixWord ++ tailWord_3956578) baseStart_3956578 baseEnd_3956578 := by
    simpa [prefixWord, tailWord_3956578, baseEnd_3956578] using wordTrace_append hprefix tailTrace_3956578
  have hstable : (prefixWord ++ tailWord_3956578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956578).length < 2 ^ (prefixWord ++ tailWord_3956578).sum := by decide
  have hdescent : baseEnd_3956578 < baseStart_3956578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956617 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_3956617 : Nat := 118140960795 + 3956617 * 2 ^ 59
def prefixEnd_3956617 : Nat := 4983230072969 + 3 ^ 40 * 3956617 * 2
def baseEnd_3956617 : Nat := 1354430857833634300994237

theorem tailTrace_3956617 : CollatzResearch.WordTrace tailWord_3956617 prefixEnd_3956617 1354430857833634300994237 := by
  unfold tailWord_3956617
  simp only [CollatzResearch.WordTrace]
  refine ⟨144309677506859820230588105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96206451671239880153725403 144309677506859820230588105)
  ·
    refine ⟨108232258130144865172941079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144309677506859820230588105 108232258130144865172941079)
    ·
      refine ⟨162348387195217297759411619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108232258130144865172941079 162348387195217297759411619)
      ·
        refine ⟨243522580792825946639117429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162348387195217297759411619 243522580792825946639117429)
        ·
          refine ⟨22830241949327432497417259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243522580792825946639117429 22830241949327432497417259)
          ·
            refine ⟨34245362923991148746125889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22830241949327432497417259 34245362923991148746125889)
            ·
              refine ⟨25684022192993361559594417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34245362923991148746125889 25684022192993361559594417)
              ·
                refine ⟨19263016644745021169695813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25684022192993361559594417 19263016644745021169695813)
                ·
                  refine ⟨3611815620889691469317965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19263016644745021169695813 3611815620889691469317965)
                  ·
                    refine ⟨1354430857833634300994237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611815620889691469317965 1354430857833634300994237)
                    ·
                      rfl

theorem cell22_3956617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_3956617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956617 prefixEnd_3956617 := by exact prefixLift 3956617
  have htrace : WordTrace (prefixWord ++ tailWord_3956617) baseStart_3956617 baseEnd_3956617 := by
    simpa [prefixWord, tailWord_3956617, baseEnd_3956617] using wordTrace_append hprefix tailTrace_3956617
  have hstable : (prefixWord ++ tailWord_3956617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956617).length < 2 ^ (prefixWord ++ tailWord_3956617).sum := by decide
  have hdescent : baseEnd_3956617 < baseStart_3956617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956634 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_3956634 : Nat := 118140960795 + 3956634 * 2 ^ 59
def prefixEnd_3956634 : Nat := 4983230072969 + 3 ^ 40 * 3956634 * 2
def baseEnd_3956634 : Nat := 1354436677281051923319185

theorem tailTrace_3956634 : CollatzResearch.WordTrace tailWord_3956634 prefixEnd_3956634 1354436677281051923319185 := by
  unfold tailWord_3956634
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077574386949558033489239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96206865031865488089304637 36077574386949558033489239)
  ·
    refine ⟨54116361580424337050233859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077574386949558033489239 54116361580424337050233859)
    ·
      refine ⟨81174542370636505575350789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54116361580424337050233859 81174542370636505575350789)
      ·
        refine ⟨15220226694494344795378273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81174542370636505575350789 15220226694494344795378273)
        ·
          refine ⟨11415170020870758596533705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15220226694494344795378273 11415170020870758596533705)
          ·
            refine ⟨8561377515653068947400279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11415170020870758596533705 8561377515653068947400279)
            ·
              refine ⟨12842066273479603421100419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561377515653068947400279 12842066273479603421100419)
              ·
                refine ⟨19263099410219405131650629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12842066273479603421100419 19263099410219405131650629)
                ·
                  refine ⟨3611831139416138462184493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19263099410219405131650629 3611831139416138462184493)
                  ·
                    refine ⟨1354436677281051923319185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3611831139416138462184493 1354436677281051923319185)
                    ·
                      rfl

theorem cell22_3956634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_3956634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956634 prefixEnd_3956634 := by exact prefixLift 3956634
  have htrace : WordTrace (prefixWord ++ tailWord_3956634) baseStart_3956634 baseEnd_3956634 := by
    simpa [prefixWord, tailWord_3956634, baseEnd_3956634] using wordTrace_append hprefix tailTrace_3956634
  have hstable : (prefixWord ++ tailWord_3956634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956634).length < 2 ^ (prefixWord ++ tailWord_3956634).sum := by decide
  have hdescent : baseEnd_3956634 < baseStart_3956634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956692 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3956692 : Nat := 118140960795 + 3956692 * 2 ^ 59
def prefixEnd_3956692 : Nat := 4983230072969 + 3 ^ 40 * 3956692 * 2
def baseEnd_3956692 : Nat := 451485510622119701789669

theorem tailTrace_3956692 : CollatzResearch.WordTrace tailWord_3956692 prefixEnd_3956692 451485510622119701789669 := by
  unfold tailWord_3956692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72156206490794054019784165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96208275321058738693045553 72156206490794054019784165)
  ·
    refine ⟨13529288717023885128709531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72156206490794054019784165 13529288717023885128709531)
    ·
      refine ⟨20293933075535827693064297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13529288717023885128709531 20293933075535827693064297)
      ·
        refine ⟨15220449806651870769798223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20293933075535827693064297 15220449806651870769798223)
        ·
          refine ⟨22830674709977806154697335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220449806651870769798223 22830674709977806154697335)
          ·
            refine ⟨34246012064966709232046003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22830674709977806154697335 34246012064966709232046003)
            ·
              refine ⟨51369018097450063848069005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34246012064966709232046003 51369018097450063848069005)
              ·
                refine ⟨19263381786543773943025877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51369018097450063848069005 19263381786543773943025877)
                ·
                  refine ⟨451485510622119701789669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19263381786543773943025877 451485510622119701789669)
                  ·
                    rfl

theorem cell22_3956692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3956692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956692 prefixEnd_3956692 := by exact prefixLift 3956692
  have htrace : WordTrace (prefixWord ++ tailWord_3956692) baseStart_3956692 baseEnd_3956692 := by
    simpa [prefixWord, tailWord_3956692, baseEnd_3956692] using wordTrace_append hprefix tailTrace_3956692
  have hstable : (prefixWord ++ tailWord_3956692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956692).length < 2 ^ (prefixWord ++ tailWord_3956692).sum := by decide
  have hdescent : baseEnd_3956692 < baseStart_3956692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956767 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_3956767 : Nat := 118140960795 + 3956767 * 2 ^ 59
def prefixEnd_3956767 : Nat := 4983230072969 + 3 ^ 40 * 3956767 * 2
def baseEnd_3956767 : Nat := 1354482205899083909743777

theorem tailTrace_3956767 : CollatzResearch.WordTrace tailWord_3956767 prefixEnd_3956767 1354482205899083909743777 := by
  unfold tailWord_3956767
  simp only [CollatzResearch.WordTrace]
  refine ⟨144315148456316395848548555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96210098970877597232365703 144315148456316395848548555)
  ·
    refine ⟨216472722684474593772822833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144315148456316395848548555 216472722684474593772822833)
    ·
      refine ⟨162354542013355945329617125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216472722684474593772822833 162354542013355945329617125)
      ·
        refine ⟨30441476627504239749303211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162354542013355945329617125 30441476627504239749303211)
        ·
          refine ⟨45662214941256359623954817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30441476627504239749303211 45662214941256359623954817)
          ·
            refine ⟨34246661205942269717966113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45662214941256359623954817 34246661205942269717966113)
            ·
              refine ⟨25684995904456702288474585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34246661205942269717966113 25684995904456702288474585)
              ·
                refine ⟨19263746928342526716355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25684995904456702288474585 19263746928342526716355939)
                ·
                  refine ⟨28895620392513790074533909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19263746928342526716355939 28895620392513790074533909)
                  ·
                    refine ⟨1354482205899083909743777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28895620392513790074533909 1354482205899083909743777)
                    ·
                      rfl

theorem cell22_3956767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_3956767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956767 prefixEnd_3956767 := by exact prefixLift 3956767
  have htrace : WordTrace (prefixWord ++ tailWord_3956767) baseStart_3956767 baseEnd_3956767 := by
    simpa [prefixWord, tailWord_3956767, baseEnd_3956767] using wordTrace_append hprefix tailTrace_3956767
  have hstable : (prefixWord ++ tailWord_3956767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956767).length < 2 ^ (prefixWord ++ tailWord_3956767).sum := by decide
  have hdescent : baseEnd_3956767 < baseStart_3956767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956784 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_3956784 : Nat := 118140960795 + 3956784 * 2 ^ 59
def prefixEnd_3956784 : Nat := 4983230072969 + 3 ^ 40 * 3956784 * 2
def baseEnd_3956784 : Nat := 1354488025346501532068725

theorem tailTrace_3956784 : CollatzResearch.WordTrace tailWord_3956784 prefixEnd_3956784 1354488025346501532068725 := by
  unfold tailWord_3956784
  simp only [CollatzResearch.WordTrace]
  refine ⟨72157884248627403875958703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96210512331503205167944937 72157884248627403875958703)
  ·
    refine ⟨108236826372941105813938055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72157884248627403875958703 108236826372941105813938055)
    ·
      refine ⟨162355239559411658720907083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108236826372941105813938055 162355239559411658720907083)
      ·
        refine ⟨243532859339117488081360625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162355239559411658720907083 243532859339117488081360625)
        ·
          refine ⟨182649644504338116061020469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243532859339117488081360625 182649644504338116061020469)
          ·
            refine ⟨17123404172281698380720669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182649644504338116061020469 17123404172281698380720669)
            ·
              refine ⟨6421276564605636892770251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123404172281698380720669 6421276564605636892770251)
              ·
                refine ⟨9631914846908455339155377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421276564605636892770251 9631914846908455339155377)
                ·
                  refine ⟨7223936135181341504366533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9631914846908455339155377 7223936135181341504366533)
                  ·
                    refine ⟨1354488025346501532068725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7223936135181341504366533 1354488025346501532068725)
                    ·
                      rfl

theorem cell22_3956784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_3956784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956784 prefixEnd_3956784 := by exact prefixLift 3956784
  have htrace : WordTrace (prefixWord ++ tailWord_3956784) baseStart_3956784 baseEnd_3956784 := by
    simpa [prefixWord, tailWord_3956784, baseEnd_3956784] using wordTrace_append hprefix tailTrace_3956784
  have hstable : (prefixWord ++ tailWord_3956784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956784).length < 2 ^ (prefixWord ++ tailWord_3956784).sum := by decide
  have hdescent : baseEnd_3956784 < baseStart_3956784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956812 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3956812 : Nat := 118140960795 + 3956812 * 2 ^ 59
def prefixEnd_3956812 : Nat := 4983230072969 + 3 ^ 40 * 3956812 * 2
def baseEnd_3956812 : Nat := 1354497610318718792368639

theorem tailTrace_3956812 : CollatzResearch.WordTrace tailWord_3956812 prefixEnd_3956812 1354497610318718792368639 := by
  unfold tailWord_3956812
  simp only [CollatzResearch.WordTrace]
  refine ⟨72158394870576684266968345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96211193160768912355957793 72158394870576684266968345)
  ·
    refine ⟨54118796152932513200226259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72158394870576684266968345 54118796152932513200226259)
    ·
      refine ⟨81178194229398769800339389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54118796152932513200226259 81178194229398769800339389)
      ·
        refine ⟨30441822836024538675127271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81178194229398769800339389 30441822836024538675127271)
        ·
          refine ⟨45662734254036808012690907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30441822836024538675127271 45662734254036808012690907)
          ·
            refine ⟨68494101381055212019036361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45662734254036808012690907 68494101381055212019036361)
            ·
              refine ⟨51370576035791409014277271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68494101381055212019036361 51370576035791409014277271)
              ·
                refine ⟨77055864053687113521415907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51370576035791409014277271 77055864053687113521415907)
                ·
                  refine ⟨115583796080530670282123861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77055864053687113521415907 115583796080530670282123861)
                  ·
                    refine ⟨1354497610318718792368639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115583796080530670282123861 1354497610318718792368639)
                    ·
                      rfl

theorem cell22_3956812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3956812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956812 prefixEnd_3956812 := by exact prefixLift 3956812
  have htrace : WordTrace (prefixWord ++ tailWord_3956812) baseStart_3956812 baseEnd_3956812 := by
    simpa [prefixWord, tailWord_3956812, baseEnd_3956812] using wordTrace_append hprefix tailTrace_3956812
  have hstable : (prefixWord ++ tailWord_3956812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956812).length < 2 ^ (prefixWord ++ tailWord_3956812).sum := by decide
  have hdescent : baseEnd_3956812 < baseStart_3956812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956848 : List Nat := [2, 1, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_3956848 : Nat := 118140960795 + 3956848 * 2 ^ 59
def prefixEnd_3956848 : Nat := 4983230072969 + 3 ^ 40 * 3956848 * 2
def baseEnd_3956848 : Nat := 1354509933854426698468529

theorem tailTrace_3956848 : CollatzResearch.WordTrace tailWord_3956848 prefixEnd_3956848 1354509933854426698468529 := by
  unfold tailWord_3956848
  simp only [CollatzResearch.WordTrace]
  refine ⟨72159051384511473341123599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96212068512681964454831465 72159051384511473341123599)
  ·
    refine ⟨108238577076767210011685399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72159051384511473341123599 108238577076767210011685399)
    ·
      refine ⟨162357865615150815017528099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108238577076767210011685399 162357865615150815017528099)
      ·
        refine ⟨243536798422726222526292149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162357865615150815017528099 243536798422726222526292149)
        ·
          refine ⟨22831574852130583361839889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 243536798422726222526292149 22831574852130583361839889)
          ·
            refine ⟨17123681139097937521379917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22831574852130583361839889 17123681139097937521379917)
            ·
              refine ⟨6421380427161726570517469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123681139097937521379917 6421380427161726570517469)
              ·
                refine ⟨2408017660185647463944051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6421380427161726570517469 2408017660185647463944051)
                ·
                  refine ⟨3612026490278471195916077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408017660185647463944051 3612026490278471195916077)
                  ·
                    refine ⟨1354509933854426698468529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612026490278471195916077 1354509933854426698468529)
                    ·
                      rfl

theorem cell22_3956848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_3956848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956848 prefixEnd_3956848 := by exact prefixLift 3956848
  have htrace : WordTrace (prefixWord ++ tailWord_3956848) baseStart_3956848 baseEnd_3956848 := by
    simpa [prefixWord, tailWord_3956848, baseEnd_3956848] using wordTrace_append hprefix tailTrace_3956848
  have hstable : (prefixWord ++ tailWord_3956848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956848).length < 2 ^ (prefixWord ++ tailWord_3956848).sum := by decide
  have hdescent : baseEnd_3956848 < baseStart_3956848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956865 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3956865 : Nat := 118140960795 + 3956865 * 2 ^ 59
def prefixEnd_3956865 : Nat := 4983230072969 + 3 ^ 40 * 3956865 * 2
def baseEnd_3956865 : Nat := 1354515753301844320793477

theorem tailTrace_3956865 : CollatzResearch.WordTrace tailWord_3956865 prefixEnd_3956865 1354515753301844320793477 := by
  unfold tailWord_3956865
  simp only [CollatzResearch.WordTrace]
  refine ⟨144318722809961358585616049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96212481873307572390410699 144318722809961358585616049)
  ·
    refine ⟨108239042107471018939212037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144318722809961358585616049 108239042107471018939212037)
    ·
      refine ⟨20294820395150816051102257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108239042107471018939212037 20294820395150816051102257)
      ·
        refine ⟨15221115296363112038326693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20294820395150816051102257 15221115296363112038326693)
        ·
          refine ⟨2853959118068083507186255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15221115296363112038326693 2853959118068083507186255)
          ·
            refine ⟨4280938677102125260779383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853959118068083507186255 4280938677102125260779383)
            ·
              refine ⟨6421408015653187891169075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280938677102125260779383 6421408015653187891169075)
              ·
                refine ⟨9632112023479781836753613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421408015653187891169075 9632112023479781836753613)
                ·
                  refine ⟨3612042008804918188782605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9632112023479781836753613 3612042008804918188782605)
                  ·
                    refine ⟨1354515753301844320793477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612042008804918188782605 1354515753301844320793477)
                    ·
                      rfl

theorem cell22_3956865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3956865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956865 prefixEnd_3956865 := by exact prefixLift 3956865
  have htrace : WordTrace (prefixWord ++ tailWord_3956865) baseStart_3956865 baseEnd_3956865 := by
    simpa [prefixWord, tailWord_3956865, baseEnd_3956865] using wordTrace_append hprefix tailTrace_3956865
  have hstable : (prefixWord ++ tailWord_3956865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956865).length < 2 ^ (prefixWord ++ tailWord_3956865).sum := by decide
  have hdescent : baseEnd_3956865 < baseStart_3956865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3956979 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 7]
def baseStart_3956979 : Nat := 118140960795 + 3956979 * 2 ^ 59
def prefixEnd_3956979 : Nat := 4983230072969 + 3 ^ 40 * 3956979 * 2
def baseEnd_3956979 : Nat := 451518259277195341147709

theorem tailTrace_3956979 : CollatzResearch.WordTrace tailWord_3956979 prefixEnd_3956979 451518259277195341147709 := by
  unfold tailWord_3956979
  simp only [CollatzResearch.WordTrace]
  refine ⟨144322880731548356055265991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96215253821032237370177327 144322880731548356055265991)
  ·
    refine ⟨216484321097322534082898987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144322880731548356055265991 216484321097322534082898987)
    ·
      refine ⟨324726481645983801124348481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216484321097322534082898987 324726481645983801124348481)
      ·
        refine ⟨243544861234487850843261361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324726481645983801124348481 243544861234487850843261361)
        ·
          refine ⟨182658645925865888132446021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243544861234487850843261361 182658645925865888132446021)
          ·
            refine ⟨34248496111099854024833629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 182658645925865888132446021 34248496111099854024833629)
            ·
              refine ⟨12843186041662445259312611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34248496111099854024833629 12843186041662445259312611)
              ·
                refine ⟨19264779062493667888968917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12843186041662445259312611 19264779062493667888968917)
                ·
                  refine ⟨451518259277195341147709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19264779062493667888968917 451518259277195341147709)
                  ·
                    rfl

theorem cell22_3956979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_3956979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3956979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3956979 prefixEnd_3956979 := by exact prefixLift 3956979
  have htrace : WordTrace (prefixWord ++ tailWord_3956979) baseStart_3956979 baseEnd_3956979 := by
    simpa [prefixWord, tailWord_3956979, baseEnd_3956979] using wordTrace_append hprefix tailTrace_3956979
  have hstable : (prefixWord ++ tailWord_3956979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3956979).length < 2 ^ (prefixWord ++ tailWord_3956979).sum := by decide
  have hdescent : baseEnd_3956979 < baseStart_3956979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3956979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957034 : List Nat := [3, 1, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3957034 : Nat := 118140960795 + 3957034 * 2 ^ 59
def prefixEnd_3957034 : Nat := 4983230072969 + 3 ^ 40 * 3957034 * 2
def baseEnd_3957034 : Nat := 1354573605455584213317959

theorem tailTrace_3957034 : CollatzResearch.WordTrace tailWord_3957034 prefixEnd_3957034 1354573605455584213317959 := by
  unfold tailWord_3957034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36081221686587275112129539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96216591164232733632345437 36081221686587275112129539)
  ·
    refine ⟨54121832529880912668194309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36081221686587275112129539 54121832529880912668194309)
    ·
      refine ⟨10147843599352671125286433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54121832529880912668194309 10147843599352671125286433)
      ·
        refine ⟨7610882699514503343964825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10147843599352671125286433 7610882699514503343964825)
        ·
          refine ⟨5708162024635877507973619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610882699514503343964825 5708162024635877507973619)
          ·
            refine ⟨8562243036953816261960429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708162024635877507973619 8562243036953816261960429)
            ·
              refine ⟨3210841138857681098235161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8562243036953816261960429 3210841138857681098235161)
              ·
                refine ⟨2408130854143260823676371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210841138857681098235161 2408130854143260823676371)
                ·
                  refine ⟨3612196281214891235514557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408130854143260823676371 3612196281214891235514557)
                  ·
                    refine ⟨1354573605455584213317959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612196281214891235514557 1354573605455584213317959)
                    ·
                      rfl

theorem cell22_3957034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3957034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957034 prefixEnd_3957034 := by exact prefixLift 3957034
  have htrace : WordTrace (prefixWord ++ tailWord_3957034) baseStart_3957034 baseEnd_3957034 := by
    simpa [prefixWord, tailWord_3957034, baseEnd_3957034] using wordTrace_append hprefix tailTrace_3957034
  have hstable : (prefixWord ++ tailWord_3957034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957034).length < 2 ^ (prefixWord ++ tailWord_3957034).sum := by decide
  have hdescent : baseEnd_3957034 < baseStart_3957034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957056 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_3957056 : Nat := 118140960795 + 3957056 * 2 ^ 59
def prefixEnd_3957056 : Nat := 4983230072969 + 3 ^ 40 * 3957056 * 2
def baseEnd_3957056 : Nat := 1354581136505183489267891

theorem tailTrace_3957056 : CollatzResearch.WordTrace tailWord_3957056 prefixEnd_3957056 1354581136505183489267891 := by
  unfold tailWord_3957056
  simp only [CollatzResearch.WordTrace]
  refine ⟨72162844576134699102909511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96217126101512932137212681 72162844576134699102909511)
  ·
    refine ⟨108244266864202048654364267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72162844576134699102909511 108244266864202048654364267)
    ·
      refine ⟨162366400296303072981546401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108244266864202048654364267 162366400296303072981546401)
      ·
        refine ⟨121774800222227304736159801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162366400296303072981546401 121774800222227304736159801)
        ·
          refine ⟨91331100166670478552119851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121774800222227304736159801 91331100166670478552119851)
          ·
            refine ⟨136996650250005717828179777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91331100166670478552119851 136996650250005717828179777)
            ·
              refine ⟨102747487687504288371134833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136996650250005717828179777 102747487687504288371134833)
              ·
                refine ⟨77060615765628216278351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102747487687504288371134833 77060615765628216278351125)
                ·
                  refine ⟨3612216364013822638047709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77060615765628216278351125 3612216364013822638047709)
                  ·
                    refine ⟨1354581136505183489267891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612216364013822638047709 1354581136505183489267891)
                    ·
                      rfl

theorem cell22_3957056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_3957056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957056 prefixEnd_3957056 := by exact prefixLift 3957056
  have htrace : WordTrace (prefixWord ++ tailWord_3957056) baseStart_3957056 baseEnd_3957056 := by
    simpa [prefixWord, tailWord_3957056, baseEnd_3957056] using wordTrace_append hprefix tailTrace_3957056
  have hstable : (prefixWord ++ tailWord_3957056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957056).length < 2 ^ (prefixWord ++ tailWord_3957056).sum := by decide
  have hdescent : baseEnd_3957056 < baseStart_3957056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957060 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3957060 : Nat := 118140960795 + 3957060 * 2 ^ 59
def prefixEnd_3957060 : Nat := 4983230072969 + 3 ^ 40 * 3957060 * 2
def baseEnd_3957060 : Nat := 1354582505786928812167879

theorem tailTrace_3957060 : CollatzResearch.WordTrace tailWord_3957060 prefixEnd_3957060 1354582505786928812167879 := by
  unfold tailWord_3957060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72162917522127453444482317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96217223362836604592643089 72162917522127453444482317)
  ·
    refine ⟨27061094070797795041680869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72162917522127453444482317 27061094070797795041680869)
    ·
      refine ⟨5073955138274586570315163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27061094070797795041680869 5073955138274586570315163)
      ·
        refine ⟨7610932707411879855472745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073955138274586570315163 7610932707411879855472745)
        ·
          refine ⟨5708199530558909891604559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610932707411879855472745 5708199530558909891604559)
          ·
            refine ⟨8562299295838364837406839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708199530558909891604559 8562299295838364837406839)
            ·
              refine ⟨12843448943757547256110259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8562299295838364837406839 12843448943757547256110259)
              ·
                refine ⟨19265173415636320884165389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12843448943757547256110259 19265173415636320884165389)
                ·
                  refine ⟨7224440030863620331562021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19265173415636320884165389 7224440030863620331562021)
                  ·
                    refine ⟨1354582505786928812167879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224440030863620331562021 1354582505786928812167879)
                    ·
                      rfl

theorem cell22_3957060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3957060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957060 prefixEnd_3957060 := by exact prefixLift 3957060
  have htrace : WordTrace (prefixWord ++ tailWord_3957060) baseStart_3957060 baseEnd_3957060 := by
    simpa [prefixWord, tailWord_3957060, baseEnd_3957060] using wordTrace_append hprefix tailTrace_3957060
  have hstable : (prefixWord ++ tailWord_3957060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957060).length < 2 ^ (prefixWord ++ tailWord_3957060).sum := by decide
  have hdescent : baseEnd_3957060 < baseStart_3957060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957090 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3957090 : Nat := 118140960795 + 3957090 * 2 ^ 59
def prefixEnd_3957090 : Nat := 4983230072969 + 3 ^ 40 * 3957090 * 2
def baseEnd_3957090 : Nat := 1354592775400018733917787

theorem tailTrace_3957090 : CollatzResearch.WordTrace tailWord_3957090 prefixEnd_3957090 1354592775400018733917787 := by
  unfold tailWord_3957090
  simp only [CollatzResearch.WordTrace]
  refine ⟨36081732308536555503139181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96217952822764148008371149 36081732308536555503139181)
  ·
    refine ⟨13530649615701208313677193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36081732308536555503139181 13530649615701208313677193)
    ·
      refine ⟨10147987211775906235257895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13530649615701208313677193 10147987211775906235257895)
      ·
        refine ⟨15221980817663859352886843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147987211775906235257895 15221980817663859352886843)
        ·
          refine ⟨22832971226495789029330265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221980817663859352886843 22832971226495789029330265)
          ·
            refine ⟨17124728419871841771997699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22832971226495789029330265 17124728419871841771997699)
            ·
              refine ⟨25687092629807762657996549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17124728419871841771997699 25687092629807762657996549)
              ·
                refine ⟨4816329868088955498374353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25687092629807762657996549 4816329868088955498374353)
                ·
                  refine ⟨3612247401066716623780765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4816329868088955498374353 3612247401066716623780765)
                  ·
                    refine ⟨1354592775400018733917787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612247401066716623780765 1354592775400018733917787)
                    ·
                      rfl

theorem cell22_3957090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3957090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957090 prefixEnd_3957090 := by exact prefixLift 3957090
  have htrace : WordTrace (prefixWord ++ tailWord_3957090) baseStart_3957090 baseEnd_3957090 := by
    simpa [prefixWord, tailWord_3957090, baseEnd_3957090] using wordTrace_append hprefix tailTrace_3957090
  have hstable : (prefixWord ++ tailWord_3957090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957090).length < 2 ^ (prefixWord ++ tailWord_3957090).sum := by decide
  have hdescent : baseEnd_3957090 < baseStart_3957090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957161 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_3957161 : Nat := 118140960795 + 3957161 * 2 ^ 59
def prefixEnd_3957161 : Nat := 4983230072969 + 3 ^ 40 * 3957161 * 2
def baseEnd_3957161 : Nat := 1354617080150998215392569

theorem tailTrace_3957161 : CollatzResearch.WordTrace tailWord_3957161 prefixEnd_3957161 1354617080150998215392569 := by
  unfold tailWord_3957161
  simp only [CollatzResearch.WordTrace]
  refine ⟨144329518816889001138391337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96219679211259334092260891 144329518816889001138391337)
  ·
    refine ⟨108247139112666750853793503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144329518816889001138391337 108247139112666750853793503)
    ·
      refine ⟨162370708669000126280690255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108247139112666750853793503 162370708669000126280690255)
      ·
        refine ⟨243556063003500189421035383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162370708669000126280690255 243556063003500189421035383)
        ·
          refine ⟨365334094505250284131553075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243556063003500189421035383 365334094505250284131553075)
          ·
            refine ⟨548001141757875426197329613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365334094505250284131553075 548001141757875426197329613)
            ·
              refine ⟨205500428159203284823998605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548001141757875426197329613 205500428159203284823998605)
              ·
                refine ⟨77062660559701231808999477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205500428159203284823998605 77062660559701231808999477)
                ·
                  refine ⟨7224624427471990482093701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77062660559701231808999477 7224624427471990482093701)
                  ·
                    refine ⟨1354617080150998215392569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224624427471990482093701 1354617080150998215392569)
                    ·
                      rfl

theorem cell22_3957161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_3957161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957161 prefixEnd_3957161 := by exact prefixLift 3957161
  have htrace : WordTrace (prefixWord ++ tailWord_3957161) baseStart_3957161 baseEnd_3957161 := by
    simpa [prefixWord, tailWord_3957161, baseEnd_3957161] using wordTrace_append hprefix tailTrace_3957161
  have hstable : (prefixWord ++ tailWord_3957161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957161).length < 2 ^ (prefixWord ++ tailWord_3957161).sum := by decide
  have hdescent : baseEnd_3957161 < baseStart_3957161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957223 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3957223 : Nat := 118140960795 + 3957223 * 2 ^ 59
def prefixEnd_3957223 : Nat := 4983230072969 + 3 ^ 40 * 3957223 * 2
def baseEnd_3957223 : Nat := 1354638304018050720342379

theorem tailTrace_3957223 : CollatzResearch.WordTrace tailWord_3957223 prefixEnd_3957223 1354638304018050720342379 := by
  unfold tailWord_3957223
  simp only [CollatzResearch.WordTrace]
  refine ⟨144331780142664385727148323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96221186761776257151432215 144331780142664385727148323)
  ·
    refine ⟨216497670213996578590722485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144331780142664385727148323 216497670213996578590722485)
    ·
      refine ⟨20296656582562179242880233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216497670213996578590722485 20296656582562179242880233)
      ·
        refine ⟨15222492436921634432160175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20296656582562179242880233 15222492436921634432160175)
        ·
          refine ⟨22833738655382451648240263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222492436921634432160175 22833738655382451648240263)
          ·
            refine ⟨34250607983073677472360395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833738655382451648240263 34250607983073677472360395)
            ·
              refine ⟨51375911974610516208540593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34250607983073677472360395 51375911974610516208540593)
              ·
                refine ⟨38531933980957887156405445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51375911974610516208540593 38531933980957887156405445)
                ·
                  refine ⟨7224737621429603841826021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38531933980957887156405445 7224737621429603841826021)
                  ·
                    refine ⟨1354638304018050720342379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224737621429603841826021 1354638304018050720342379)
                    ·
                      rfl

theorem cell22_3957223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3957223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957223 prefixEnd_3957223 := by exact prefixLift 3957223
  have htrace : WordTrace (prefixWord ++ tailWord_3957223) baseStart_3957223 baseEnd_3957223 := by
    simpa [prefixWord, tailWord_3957223, baseEnd_3957223] using wordTrace_append hprefix tailTrace_3957223
  have hstable : (prefixWord ++ tailWord_3957223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957223).length < 2 ^ (prefixWord ++ tailWord_3957223).sum := by decide
  have hdescent : baseEnd_3957223 < baseStart_3957223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957238 : List Nat := [5, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3957238 : Nat := 118140960795 + 3957238 * 2 ^ 59
def prefixEnd_3957238 : Nat := 4983230072969 + 3 ^ 40 * 3957238 * 2
def baseEnd_3957238 : Nat := 150515937647177297913037

theorem tailTrace_3957238 : CollatzResearch.WordTrace tailWord_3957238 prefixEnd_3957238 150515937647177297913037 := by
  unfold tailWord_3957238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020770452350627705559023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96221551491740028859296245 9020770452350627705559023)
  ·
    refine ⟨13531155678525941558338535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020770452350627705559023 13531155678525941558338535)
    ·
      refine ⟨20296733517788912337507803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13531155678525941558338535 20296733517788912337507803)
      ·
        refine ⟨30445100276683368506261705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20296733517788912337507803 30445100276683368506261705)
        ·
          refine ⟨22833825207512526379696279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30445100276683368506261705 22833825207512526379696279)
          ·
            refine ⟨34250737811268789569544419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22833825207512526379696279 34250737811268789569544419)
            ·
              refine ⟨51376106716903184354316629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34250737811268789569544419 51376106716903184354316629)
              ·
                refine ⟨150515937647177297913037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51376106716903184354316629 150515937647177297913037)
                ·
                  rfl

theorem cell22_3957238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3957238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957238 prefixEnd_3957238 := by exact prefixLift 3957238
  have htrace : WordTrace (prefixWord ++ tailWord_3957238) baseStart_3957238 baseEnd_3957238 := by
    simpa [prefixWord, tailWord_3957238, baseEnd_3957238] using wordTrace_append hprefix tailTrace_3957238
  have hstable : (prefixWord ++ tailWord_3957238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957238).length < 2 ^ (prefixWord ++ tailWord_3957238).sum := by decide
  have hdescent : baseEnd_3957238 < baseStart_3957238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957261 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3957261 : Nat := 118140960795 + 3957261 * 2 ^ 59
def prefixEnd_3957261 : Nat := 4983230072969 + 3 ^ 40 * 3957261 * 2
def baseEnd_3957261 : Nat := 451550437398210429297421

theorem tailTrace_3957261 : CollatzResearch.WordTrace tailWord_3957261 prefixEnd_3957261 451550437398210429297421 := by
  unfold tailWord_3957261
  simp only [CollatzResearch.WordTrace]
  refine ⟨144333166116526718217031637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96222110744351145478021091 144333166116526718217031637)
  ·
    refine ⟨3382808580856094958211679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 144333166116526718217031637 3382808580856094958211679)
    ·
      refine ⟨5074212871284142437317519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382808580856094958211679 5074212871284142437317519)
      ·
        refine ⟨7611319306926213655976279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074212871284142437317519 7611319306926213655976279)
        ·
          refine ⟨11416978960389320483964419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611319306926213655976279 11416978960389320483964419)
          ·
            refine ⟨17125468440583980725946629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416978960389320483964419 17125468440583980725946629)
            ·
              refine ⟨3211025332609496386114993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17125468440583980725946629 3211025332609496386114993)
              ·
                refine ⟨2408268999457122289586245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211025332609496386114993 2408268999457122289586245)
                ·
                  refine ⟨451550437398210429297421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408268999457122289586245 451550437398210429297421)
                  ·
                    rfl

theorem cell22_3957261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3957261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957261 prefixEnd_3957261 := by exact prefixLift 3957261
  have htrace : WordTrace (prefixWord ++ tailWord_3957261) baseStart_3957261 baseEnd_3957261 := by
    simpa [prefixWord, tailWord_3957261, baseEnd_3957261] using wordTrace_append hprefix tailTrace_3957261
  have hstable : (prefixWord ++ tailWord_3957261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957261).length < 2 ^ (prefixWord ++ tailWord_3957261).sum := by decide
  have hdescent : baseEnd_3957261 < baseStart_3957261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957377 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3957377 : Nat := 118140960795 + 3957377 * 2 ^ 59
def prefixEnd_3957377 : Nat := 4983230072969 + 3 ^ 40 * 3957377 * 2
def baseEnd_3957377 : Nat := 1354691021365245651991907

theorem tailTrace_3957377 : CollatzResearch.WordTrace tailWord_3957377 prefixEnd_3957377 1354691021365245651991907 := by
  unfold tailWord_3957377
  simp only [CollatzResearch.WordTrace]
  refine ⟨144337396984106470028254385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96224931322737646685502923 144337396984106470028254385)
  ·
    refine ⟨108253047738079852521190789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144337396984106470028254385 108253047738079852521190789)
    ·
      refine ⟨20297446450889972347723273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108253047738079852521190789 20297446450889972347723273)
      ·
        refine ⟨15223084838167479260792455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20297446450889972347723273 15223084838167479260792455)
        ·
          refine ⟨22834627257251218891188683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223084838167479260792455 22834627257251218891188683)
          ·
            refine ⟨34251940885876828336783025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22834627257251218891188683 34251940885876828336783025)
            ·
              refine ⟨25688955664407621252587269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34251940885876828336783025 25688955664407621252587269)
              ·
                refine ⟨4816679187076428984860113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25688955664407621252587269 4816679187076428984860113)
                ·
                  refine ⟨3612509390307321738645085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4816679187076428984860113 3612509390307321738645085)
                  ·
                    refine ⟨1354691021365245651991907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612509390307321738645085 1354691021365245651991907)
                    ·
                      rfl

theorem cell22_3957377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3957377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957377 prefixEnd_3957377 := by exact prefixLift 3957377
  have htrace : WordTrace (prefixWord ++ tailWord_3957377) baseStart_3957377 baseEnd_3957377 := by
    simpa [prefixWord, tailWord_3957377, baseEnd_3957377] using wordTrace_append hprefix tailTrace_3957377
  have hstable : (prefixWord ++ tailWord_3957377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957377).length < 2 ^ (prefixWord ++ tailWord_3957377).sum := by decide
  have hdescent : baseEnd_3957377 < baseStart_3957377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3957388 : Nat := 118140960795 + 3957388 * 2 ^ 59
def prefixEnd_3957388 : Nat := 4983230072969 + 3 ^ 40 * 3957388 * 2
def baseEnd_3957388 : Nat := 1354694786890045289966873

theorem tailTrace_3957388 : CollatzResearch.WordTrace tailWord_3957388 prefixEnd_3957388 1354694786890045289966873 := by
  unfold tailWord_3957388
  simp only [CollatzResearch.WordTrace]
  refine ⟨72168899093533309453452409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96225198791377745937936545 72168899093533309453452409)
  ·
    refine ⟨54126674320149982090089307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72168899093533309453452409 54126674320149982090089307)
    ·
      refine ⟨81190011480224973135133961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54126674320149982090089307 81190011480224973135133961)
      ·
        refine ⟨60892508610168729851350471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81190011480224973135133961 60892508610168729851350471)
        ·
          refine ⟨91338762915253094777025707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60892508610168729851350471 91338762915253094777025707)
          ·
            refine ⟨137008144372879642165538561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91338762915253094777025707 137008144372879642165538561)
            ·
              refine ⟨102756108279659731624153921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137008144372879642165538561 102756108279659731624153921)
              ·
                refine ⟨77067081209744798718115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102756108279659731624153921 77067081209744798718115441)
                ·
                  refine ⟨57800310907308599038586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77067081209744798718115441 57800310907308599038586581)
                  ·
                    refine ⟨1354694786890045289966873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57800310907308599038586581 1354694786890045289966873)
                    ·
                      rfl

theorem cell22_3957388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3957388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957388 prefixEnd_3957388 := by exact prefixLift 3957388
  have htrace : WordTrace (prefixWord ++ tailWord_3957388) baseStart_3957388 baseEnd_3957388 := by
    simpa [prefixWord, tailWord_3957388, baseEnd_3957388] using wordTrace_append hprefix tailTrace_3957388
  have hstable : (prefixWord ++ tailWord_3957388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957388).length < 2 ^ (prefixWord ++ tailWord_3957388).sum := by decide
  have hdescent : baseEnd_3957388 < baseStart_3957388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957390 : List Nat := [4, 1, 1, 3, 1, 1, 4, 7]
def baseStart_3957390 : Nat := 118140960795 + 3957390 * 2 ^ 59
def prefixEnd_3957390 : Nat := 4983230072969 + 3 ^ 40 * 3957390 * 2
def baseEnd_3957390 : Nat := 150521719058990883490763

theorem tailTrace_3957390 : CollatzResearch.WordTrace tailWord_3957390 prefixEnd_3957390 150521719058990883490763 := by
  unfold tailWord_3957390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042233891632421656059703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96225247422039582165651749 18042233891632421656059703)
  ·
    refine ⟨27063350837448632484089555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042233891632421656059703 27063350837448632484089555)
    ·
      refine ⟨40595026256172948726134333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27063350837448632484089555 40595026256172948726134333)
      ·
        refine ⟨15223134846064855772300375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40595026256172948726134333 15223134846064855772300375)
        ·
          refine ⟨22834702269097283658450563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223134846064855772300375 22834702269097283658450563)
          ·
            refine ⟨34252053403645925487675845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22834702269097283658450563 34252053403645925487675845)
            ·
              refine ⟨6422260013183611028939221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34252053403645925487675845 6422260013183611028939221)
              ·
                refine ⟨150521719058990883490763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6422260013183611028939221 150521719058990883490763)
                ·
                  rfl

theorem cell22_3957390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_3957390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957390 prefixEnd_3957390 := by exact prefixLift 3957390
  have htrace : WordTrace (prefixWord ++ tailWord_3957390) baseStart_3957390 baseEnd_3957390 := by
    simpa [prefixWord, tailWord_3957390, baseEnd_3957390] using wordTrace_append hprefix tailTrace_3957390
  have hstable : (prefixWord ++ tailWord_3957390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957390).length < 2 ^ (prefixWord ++ tailWord_3957390).sum := by decide
  have hdescent : baseEnd_3957390 < baseStart_3957390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957394 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3957394 : Nat := 118140960795 + 3957394 * 2 ^ 59
def prefixEnd_3957394 : Nat := 4983230072969 + 3 ^ 40 * 3957394 * 2
def baseEnd_3957394 : Nat := 1354696840812663274316855

theorem tailTrace_3957394 : CollatzResearch.WordTrace tailWord_3957394 prefixEnd_3957394 1354696840812663274316855 := by
  unfold tailWord_3957394
  simp only [CollatzResearch.WordTrace]
  refine ⟨36084504256261220482905809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96225344683363254621082157 36084504256261220482905809)
  ·
    refine ⟨27063378192195915362179357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36084504256261220482905809 27063378192195915362179357)
    ·
      refine ⟨10148766822073468260817259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27063378192195915362179357 10148766822073468260817259)
      ·
        refine ⟨15223150233110202391225889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148766822073468260817259 15223150233110202391225889)
        ·
          refine ⟨11417362674832651793419417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15223150233110202391225889 11417362674832651793419417)
          ·
            refine ⟨8563022006124488845064563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417362674832651793419417 8563022006124488845064563)
            ·
              refine ⟨12844533009186733267596845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563022006124488845064563 12844533009186733267596845)
              ·
                refine ⟨4816699878445024975348817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12844533009186733267596845 4816699878445024975348817)
                ·
                  refine ⟨3612524908833768731511613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4816699878445024975348817 3612524908833768731511613)
                  ·
                    refine ⟨1354696840812663274316855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612524908833768731511613 1354696840812663274316855)
                    ·
                      rfl

theorem cell22_3957394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3957394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957394 prefixEnd_3957394 := by exact prefixLift 3957394
  have htrace : WordTrace (prefixWord ++ tailWord_3957394) baseStart_3957394 baseEnd_3957394 := by
    simpa [prefixWord, tailWord_3957394, baseEnd_3957394] using wordTrace_append hprefix tailTrace_3957394
  have hstable : (prefixWord ++ tailWord_3957394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957394).length < 2 ^ (prefixWord ++ tailWord_3957394).sum := by decide
  have hdescent : baseEnd_3957394 < baseStart_3957394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957430 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3957430 : Nat := 118140960795 + 3957430 * 2 ^ 59
def prefixEnd_3957430 : Nat := 4983230072969 + 3 ^ 40 * 3957430 * 2
def baseEnd_3957430 : Nat := 451569721449457060138915

theorem tailTrace_3957430 : CollatzResearch.WordTrace tailWord_3957430 prefixEnd_3957430 451569721449457060138915 := by
  unfold tailWord_3957430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021208128307153754995859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96226220035276306719955829 9021208128307153754995859)
  ·
    refine ⟨13531812192460730632493789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9021208128307153754995859 13531812192460730632493789)
    ·
      refine ⟨5074429572172773987185171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13531812192460730632493789 5074429572172773987185171)
      ·
        refine ⟨7611644358259160980777757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074429572172773987185171 7611644358259160980777757)
        ·
          refine ⟨2854366634347185367791659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7611644358259160980777757 2854366634347185367791659)
          ·
            refine ⟨4281549951520778051687489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854366634347185367791659 4281549951520778051687489)
            ·
              refine ⟨3211162463640583538765617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281549951520778051687489 3211162463640583538765617)
              ·
                refine ⟨2408371847730437654074213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211162463640583538765617 2408371847730437654074213)
                ·
                  refine ⟨451569721449457060138915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408371847730437654074213 451569721449457060138915)
                  ·
                    rfl

theorem cell22_3957430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3957430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957430 prefixEnd_3957430 := by exact prefixLift 3957430
  have htrace : WordTrace (prefixWord ++ tailWord_3957430) baseStart_3957430 baseEnd_3957430 := by
    simpa [prefixWord, tailWord_3957430, baseEnd_3957430] using wordTrace_append hprefix tailTrace_3957430
  have hstable : (prefixWord ++ tailWord_3957430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957430).length < 2 ^ (prefixWord ++ tailWord_3957430).sum := by decide
  have hdescent : baseEnd_3957430 < baseStart_3957430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957439 : List Nat := [1, 1, 2, 2, 2, 5, 1, 4, 1, 3]
def baseStart_3957439 : Nat := 118140960795 + 3957439 * 2 ^ 59
def prefixEnd_3957439 : Nat := 4983230072969 + 3 ^ 40 * 3957439 * 2
def baseEnd_3957439 : Nat := 1354712245232298156941717

theorem tailTrace_3957439 : CollatzResearch.WordTrace tailWord_3957439 prefixEnd_3957439 1354712245232298156941717 := by
  unfold tailWord_3957439
  simp only [CollatzResearch.WordTrace]
  refine ⟨144339658309881854617011371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96226438873254569744674247 144339658309881854617011371)
  ·
    refine ⟨216509487464822781925517057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144339658309881854617011371 216509487464822781925517057)
    ·
      refine ⟨162382115598617086444137793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216509487464822781925517057 162382115598617086444137793)
      ·
        refine ⟨121786586698962814833103345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162382115598617086444137793 121786586698962814833103345)
        ·
          refine ⟨91339940024222111124827509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121786586698962814833103345 91339940024222111124827509)
          ·
            refine ⟨8563119377270822917952579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91339940024222111124827509 8563119377270822917952579)
            ·
              refine ⟨12844679065906234376928869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563119377270822917952579 12844679065906234376928869)
              ·
                refine ⟨2408377324857418945674163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12844679065906234376928869 2408377324857418945674163)
                ·
                  refine ⟨3612565987286128418511245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408377324857418945674163 3612565987286128418511245)
                  ·
                    refine ⟨1354712245232298156941717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612565987286128418511245 1354712245232298156941717)
                    ·
                      rfl

theorem cell22_3957439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_3957439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957439 prefixEnd_3957439 := by exact prefixLift 3957439
  have htrace : WordTrace (prefixWord ++ tailWord_3957439) baseStart_3957439 baseEnd_3957439 := by
    simpa [prefixWord, tailWord_3957439, baseEnd_3957439] using wordTrace_append hprefix tailTrace_3957439
  have hstable : (prefixWord ++ tailWord_3957439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957439).length < 2 ^ (prefixWord ++ tailWord_3957439).sum := by decide
  have hdescent : baseEnd_3957439 < baseStart_3957439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957441 : List Nat := [1, 2, 6, 2, 2, 1, 1, 7]
def baseStart_3957441 : Nat := 118140960795 + 3957441 * 2 ^ 59
def prefixEnd_3957441 : Nat := 4983230072969 + 3 ^ 40 * 3957441 * 2
def baseEnd_3957441 : Nat := 150523658874796757599079

theorem tailTrace_3957441 : CollatzResearch.WordTrace tailWord_3957441 prefixEnd_3957441 150523658874796757599079 := by
  unfold tailWord_3957441
  simp only [CollatzResearch.WordTrace]
  refine ⟨144339731255874608958584177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96226487503916405972389451 144339731255874608958584177)
  ·
    refine ⟨108254798441905956718938133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144339731255874608958584177 108254798441905956718938133)
    ·
      refine ⟨5074443676964341721200225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108254798441905956718938133 5074443676964341721200225)
      ·
        refine ⟨3805832757723256290900169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5074443676964341721200225 3805832757723256290900169)
        ·
          refine ⟨2854374568292442218175127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805832757723256290900169 2854374568292442218175127)
          ·
            refine ⟨4281561852438663327262691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854374568292442218175127 4281561852438663327262691)
            ·
              refine ⟨6422342778657994990894037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281561852438663327262691 6422342778657994990894037)
              ·
                refine ⟨150523658874796757599079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6422342778657994990894037 150523658874796757599079)
                ·
                  rfl

theorem cell22_3957441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 7].length) (baseStart_3957441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957441 prefixEnd_3957441 := by exact prefixLift 3957441
  have htrace : WordTrace (prefixWord ++ tailWord_3957441) baseStart_3957441 baseEnd_3957441 := by
    simpa [prefixWord, tailWord_3957441, baseEnd_3957441] using wordTrace_append hprefix tailTrace_3957441
  have hstable : (prefixWord ++ tailWord_3957441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957441).length < 2 ^ (prefixWord ++ tailWord_3957441).sum := by decide
  have hdescent : baseEnd_3957441 < baseStart_3957441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957450 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3957450 : Nat := 118140960795 + 3957450 * 2 ^ 59
def prefixEnd_3957450 : Nat := 4983230072969 + 3 ^ 40 * 3957450 * 2
def baseEnd_3957450 : Nat := 1354716010757097794916683

theorem tailTrace_3957450 : CollatzResearch.WordTrace tailWord_3957450 prefixEnd_3957450 1354716010757097794916683 := by
  unfold tailWord_3957450
  simp only [CollatzResearch.WordTrace]
  refine ⟨36085014878210500873915451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96226706341894668997107869 36085014878210500873915451)
  ·
    refine ⟨54127522317315751310873177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36085014878210500873915451 54127522317315751310873177)
    ·
      refine ⟨40595641737986813483154883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54127522317315751310873177 40595641737986813483154883)
      ·
        refine ⟨60893462606980220224732325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40595641737986813483154883 60893462606980220224732325)
        ·
          refine ⟨11417524238808791292137311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60893462606980220224732325 11417524238808791292137311)
          ·
            refine ⟨17126286358213186938205967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417524238808791292137311 17126286358213186938205967)
            ·
              refine ⟨25689429537319780407308951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126286358213186938205967 25689429537319780407308951)
              ·
                refine ⟨38534144305979670610963427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689429537319780407308951 38534144305979670610963427)
                ·
                  refine ⟨57801216458969505916445141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38534144305979670610963427 57801216458969505916445141)
                  ·
                    refine ⟨1354716010757097794916683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57801216458969505916445141 1354716010757097794916683)
                    ·
                      rfl

theorem cell22_3957450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3957450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957450 prefixEnd_3957450 := by exact prefixLift 3957450
  have htrace : WordTrace (prefixWord ++ tailWord_3957450) baseStart_3957450 baseEnd_3957450 := by
    simpa [prefixWord, tailWord_3957450, baseEnd_3957450] using wordTrace_append hprefix tailTrace_3957450
  have hstable : (prefixWord ++ tailWord_3957450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957450).length < 2 ^ (prefixWord ++ tailWord_3957450).sum := by decide
  have hdescent : baseEnd_3957450 < baseStart_3957450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957452 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_3957452 : Nat := 118140960795 + 3957452 * 2 ^ 59
def prefixEnd_3957452 : Nat := 4983230072969 + 3 ^ 40 * 3957452 * 2
def baseEnd_3957452 : Nat := 451572231799323485455559

theorem tailTrace_3957452 : CollatzResearch.WordTrace tailWord_3957452 prefixEnd_3957452 451572231799323485455559 := by
  unfold tailWord_3957452
  simp only [CollatzResearch.WordTrace]
  refine ⟨72170066229417378918617305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96226754972556505224823073 72170066229417378918617305)
  ·
    refine ⟨54127549672063034188962979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72170066229417378918617305 54127549672063034188962979)
    ·
      refine ⟨81191324508094551283444469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54127549672063034188962979 81191324508094551283444469)
      ·
        refine ⟨7611686672633864182822919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81191324508094551283444469 7611686672633864182822919)
        ·
          refine ⟨11417530008950796274234379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611686672633864182822919 11417530008950796274234379)
          ·
            refine ⟨17126295013426194411351569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417530008950796274234379 17126295013426194411351569)
            ·
              refine ⟨12844721260069645808513677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126295013426194411351569 12844721260069645808513677)
              ·
                refine ⟨4816770472526117178192629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12844721260069645808513677 4816770472526117178192629)
                ·
                  refine ⟨451572231799323485455559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816770472526117178192629 451572231799323485455559)
                  ·
                    rfl

theorem cell22_3957452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_3957452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957452 prefixEnd_3957452 := by exact prefixLift 3957452
  have htrace : WordTrace (prefixWord ++ tailWord_3957452) baseStart_3957452 baseEnd_3957452 := by
    simpa [prefixWord, tailWord_3957452, baseEnd_3957452] using wordTrace_append hprefix tailTrace_3957452
  have hstable : (prefixWord ++ tailWord_3957452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957452).length < 2 ^ (prefixWord ++ tailWord_3957452).sum := by decide
  have hdescent : baseEnd_3957452 < baseStart_3957452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957465 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_3957465 : Nat := 118140960795 + 3957465 * 2 ^ 59
def prefixEnd_3957465 : Nat := 4983230072969 + 3 ^ 40 * 3957465 * 2
def baseEnd_3957465 : Nat := 1354721145563642755791637

theorem tailTrace_3957465 : CollatzResearch.WordTrace tailWord_3957465 prefixEnd_3957465 1354721145563642755791637 := by
  unfold tailWord_3957465
  simp only [CollatzResearch.WordTrace]
  refine ⟨144340606607787661057457849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96227071071858440704971899 144340606607787661057457849)
  ·
    refine ⟨108255454955840745793093387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144340606607787661057457849 108255454955840745793093387)
    ·
      refine ⟨162383182433761118689640081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108255454955840745793093387 162383182433761118689640081)
      ·
        refine ⟨121787386825320839017230061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162383182433761118689640081 121787386825320839017230061)
        ·
          refine ⟨45670270059495314631461273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121787386825320839017230061 45670270059495314631461273)
          ·
            refine ⟨34252702544621485973595955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45670270059495314631461273 34252702544621485973595955)
            ·
              refine ⟨51379053816932228960393933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34252702544621485973595955 51379053816932228960393933)
              ·
                refine ⟨19267145181349585860147725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51379053816932228960393933 19267145181349585860147725)
                ·
                  refine ⟨7225179443006094697555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19267145181349585860147725 7225179443006094697555397)
                  ·
                    refine ⟨1354721145563642755791637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225179443006094697555397 1354721145563642755791637)
                    ·
                      rfl

theorem cell22_3957465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_3957465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957465 prefixEnd_3957465 := by exact prefixLift 3957465
  have htrace : WordTrace (prefixWord ++ tailWord_3957465) baseStart_3957465 baseEnd_3957465 := by
    simpa [prefixWord, tailWord_3957465, baseEnd_3957465] using wordTrace_append hprefix tailTrace_3957465
  have hstable : (prefixWord ++ tailWord_3957465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957465).length < 2 ^ (prefixWord ++ tailWord_3957465).sum := by decide
  have hdescent : baseEnd_3957465 < baseStart_3957465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957512 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3957512 : Nat := 118140960795 + 3957512 * 2 ^ 59
def prefixEnd_3957512 : Nat := 4983230072969 + 3 ^ 40 * 3957512 * 2
def baseEnd_3957512 : Nat := 1354737234624150299866493

theorem tailTrace_3957512 : CollatzResearch.WordTrace tailWord_3957512 prefixEnd_3957512 1354737234624150299866493 := by
  unfold tailWord_3957512
  simp only [CollatzResearch.WordTrace]
  refine ⟨72171160419308694042209395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96228213892411592056279193 72171160419308694042209395)
  ·
    refine ⟨108256740628963041063314093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72171160419308694042209395 108256740628963041063314093)
    ·
      refine ⟨40596277735861140398742785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108256740628963041063314093 40596277735861140398742785)
      ·
        refine ⟨30447208301895855299057089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40596277735861140398742785 30447208301895855299057089)
        ·
          refine ⟨22835406226421891474292817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30447208301895855299057089 22835406226421891474292817)
          ·
            refine ⟨17126554669816418605719613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22835406226421891474292817 17126554669816418605719613)
            ·
              refine ⟨6422458001181156977144855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17126554669816418605719613 6422458001181156977144855)
              ·
                refine ⟨9633687001771735465717283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422458001181156977144855 9633687001771735465717283)
                ·
                  refine ⟨14450530502657603198575925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9633687001771735465717283 14450530502657603198575925)
                  ·
                    refine ⟨1354737234624150299866493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14450530502657603198575925 1354737234624150299866493)
                    ·
                      rfl

theorem cell22_3957512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3957512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957512 prefixEnd_3957512 := by exact prefixLift 3957512
  have htrace : WordTrace (prefixWord ++ tailWord_3957512) baseStart_3957512 baseEnd_3957512 := by
    simpa [prefixWord, tailWord_3957512, baseEnd_3957512] using wordTrace_append hprefix tailTrace_3957512
  have hstable : (prefixWord ++ tailWord_3957512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957512).length < 2 ^ (prefixWord ++ tailWord_3957512).sum := by decide
  have hdescent : baseEnd_3957512 < baseStart_3957512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957525 : List Nat := [1, 3, 2, 1, 2, 2, 3, 8]
def baseStart_3957525 : Nat := 118140960795 + 3957525 * 2 ^ 59
def prefixEnd_3957525 : Nat := 4983230072969 + 3 ^ 40 * 3957525 * 2
def baseEnd_3957525 : Nat := 150526853865535844365717

theorem tailTrace_3957525 : CollatzResearch.WordTrace tailWord_3957525 prefixEnd_3957525 150526853865535844365717 := by
  unfold tailWord_3957525
  simp only [CollatzResearch.WordTrace]
  refine ⟨144342794987570291304642029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96228529991713527536428019 144342794987570291304642029)
  ·
    refine ⟨54128548120338859239240761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144342794987570291304642029 54128548120338859239240761)
    ·
      refine ⟨40596411090254144429430571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54128548120338859239240761 40596411090254144429430571)
      ·
        refine ⟨60894616635381216644145857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40596411090254144429430571 60894616635381216644145857)
        ·
          refine ⟨45670962476535912483109393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60894616635381216644145857 45670962476535912483109393)
          ·
            refine ⟨34253221857401934362332045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45670962476535912483109393 34253221857401934362332045)
            ·
              refine ⟨12844958196525725385874517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34253221857401934362332045 12844958196525725385874517)
              ·
                refine ⟨150526853865535844365717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12844958196525725385874517 150526853865535844365717)
                ·
                  rfl

theorem cell22_3957525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 8].length) (baseStart_3957525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957525 prefixEnd_3957525 := by exact prefixLift 3957525
  have htrace : WordTrace (prefixWord ++ tailWord_3957525) baseStart_3957525 baseEnd_3957525 := by
    simpa [prefixWord, tailWord_3957525, baseEnd_3957525] using wordTrace_append hprefix tailTrace_3957525
  have hstable : (prefixWord ++ tailWord_3957525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957525).length < 2 ^ (prefixWord ++ tailWord_3957525).sum := by decide
  have hdescent : baseEnd_3957525 < baseStart_3957525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957604 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3957604 : Nat := 118140960795 + 3957604 * 2 ^ 59
def prefixEnd_3957604 : Nat := 4983230072969 + 3 ^ 40 * 3957604 * 2
def baseEnd_3957604 : Nat := 451589576034764242188737

theorem tailTrace_3957604 : CollatzResearch.WordTrace tailWord_3957604 prefixEnd_3957604 451589576034764242188737 := by
  unfold tailWord_3957604
  simp only [CollatzResearch.WordTrace]
  refine ⟨72172838177142043898383933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96230450902856058531178577 72172838177142043898383933)
  ·
    refine ⟨27064814316428266461893975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72172838177142043898383933 27064814316428266461893975)
    ·
      refine ⟨40597221474642399692840963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27064814316428266461893975 40597221474642399692840963)
      ·
        refine ⟨60895832211963599539261445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40597221474642399692840963 60895832211963599539261445)
        ·
          refine ⟨11417968539743174913611521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60895832211963599539261445 11417968539743174913611521)
          ·
            refine ⟨8563476404807381185208641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11417968539743174913611521 8563476404807381185208641)
            ·
              refine ⟨6422607303605535888906481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8563476404807381185208641 6422607303605535888906481)
              ·
                refine ⟨4816955477704151916679861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6422607303605535888906481 4816955477704151916679861)
                ·
                  refine ⟨451589576034764242188737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4816955477704151916679861 451589576034764242188737)
                  ·
                    rfl

theorem cell22_3957604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3957604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957604 prefixEnd_3957604 := by exact prefixLift 3957604
  have htrace : WordTrace (prefixWord ++ tailWord_3957604) baseStart_3957604 baseEnd_3957604 := by
    simpa [prefixWord, tailWord_3957604, baseEnd_3957604] using wordTrace_append hprefix tailTrace_3957604
  have hstable : (prefixWord ++ tailWord_3957604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957604).length < 2 ^ (prefixWord ++ tailWord_3957604).sum := by decide
  have hdescent : baseEnd_3957604 < baseStart_3957604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957608 : List Nat := [2, 1, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3957608 : Nat := 118140960795 + 3957608 * 2 ^ 59
def prefixEnd_3957608 : Nat := 4983230072969 + 3 ^ 40 * 3957608 * 2
def baseEnd_3957608 : Nat := 1354770097386038049466199

theorem tailTrace_3957608 : CollatzResearch.WordTrace tailWord_3957608 prefixEnd_3957608 1354770097386038049466199 := by
  unfold tailWord_3957608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72172911123134798239956739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96230548164179730986608985 72172911123134798239956739)
  ·
    refine ⟨108259366684702197359935109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72172911123134798239956739 108259366684702197359935109)
    ·
      refine ⟨20298631253381662004987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108259366684702197359935109 20298631253381662004987833)
      ·
        refine ⟨15223973440036246503740875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20298631253381662004987833 15223973440036246503740875)
        ·
          refine ⟨22835960160054369755611313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15223973440036246503740875 22835960160054369755611313)
          ·
            refine ⟨17126970120040777316708485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22835960160054369755611313 17126970120040777316708485)
            ·
              refine ⟨3211306897507645746882841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17126970120040777316708485 3211306897507645746882841)
              ·
                refine ⟨2408480173130734310162131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211306897507645746882841 2408480173130734310162131)
                ·
                  refine ⟨3612720259696101465243197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408480173130734310162131 3612720259696101465243197)
                  ·
                    refine ⟨1354770097386038049466199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612720259696101465243197 1354770097386038049466199)
                    ·
                      rfl

theorem cell22_3957608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3957608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957608 prefixEnd_3957608 := by exact prefixLift 3957608
  have htrace : WordTrace (prefixWord ++ tailWord_3957608) baseStart_3957608 baseEnd_3957608 := by
    simpa [prefixWord, tailWord_3957608, baseEnd_3957608] using wordTrace_append hprefix tailTrace_3957608
  have hstable : (prefixWord ++ tailWord_3957608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957608).length < 2 ^ (prefixWord ++ tailWord_3957608).sum := by decide
  have hdescent : baseEnd_3957608 < baseStart_3957608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957615 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 10]
def baseStart_3957615 : Nat := 118140960795 + 3957615 * 2 ^ 59
def prefixEnd_3957615 : Nat := 4983230072969 + 3 ^ 40 * 3957615 * 2
def baseEnd_3957615 : Nat := 451590831209697454847059

theorem tailTrace_3957615 : CollatzResearch.WordTrace tailWord_3957615 prefixEnd_3957615 451590831209697454847059 := by
  unfold tailWord_3957615
  simp only [CollatzResearch.WordTrace]
  refine ⟨144346077557244236675418299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96230718371496157783612199 144346077557244236675418299)
  ·
    refine ⟨216519116335866355013127449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144346077557244236675418299 216519116335866355013127449)
    ·
      refine ⟨162389337251899766259845587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216519116335866355013127449 162389337251899766259845587)
      ·
        refine ⟨243584005877849649389768381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162389337251899766259845587 243584005877849649389768381)
        ·
          refine ⟨91344002204193618521163143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243584005877849649389768381 91344002204193618521163143)
          ·
            refine ⟨137016003306290427781744715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91344002204193618521163143 137016003306290427781744715)
            ·
              refine ⟨205524004959435641672617073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137016003306290427781744715 205524004959435641672617073)
              ·
                refine ⟨154143003719576731254462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205524004959435641672617073 154143003719576731254462805)
                ·
                  refine ⟨451590831209697454847059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 154143003719576731254462805 451590831209697454847059)
                  ·
                    rfl

theorem cell22_3957615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_3957615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957615 prefixEnd_3957615 := by exact prefixLift 3957615
  have htrace : WordTrace (prefixWord ++ tailWord_3957615) baseStart_3957615 baseEnd_3957615 := by
    simpa [prefixWord, tailWord_3957615, baseEnd_3957615] using wordTrace_append hprefix tailTrace_3957615
  have hstable : (prefixWord ++ tailWord_3957615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957615).length < 2 ^ (prefixWord ++ tailWord_3957615).sum := by decide
  have hdescent : baseEnd_3957615 < baseStart_3957615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957617 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_3957617 : Nat := 118140960795 + 3957617 * 2 ^ 59
def prefixEnd_3957617 : Nat := 4983230072969 + 3 ^ 40 * 3957617 * 2
def baseEnd_3957617 : Nat := 1354773178269965025991171

theorem tailTrace_3957617 : CollatzResearch.WordTrace tailWord_3957617 prefixEnd_3957617 1354773178269965025991171 := by
  unfold tailWord_3957617
  simp only [CollatzResearch.WordTrace]
  refine ⟨144346150503236991016991105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96230767002157994011327403 144346150503236991016991105)
  ·
    refine ⟨108259612877427743262743329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144346150503236991016991105 108259612877427743262743329)
    ·
      refine ⟨81194709658070807447057497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108259612877427743262743329 81194709658070807447057497)
      ·
        refine ⟨60896032243553105585293123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81194709658070807447057497 60896032243553105585293123)
        ·
          refine ⟨91344048365329658377939685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60896032243553105585293123 91344048365329658377939685)
          ·
            refine ⟨17127009068499310945863691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91344048365329658377939685 17127009068499310945863691)
            ·
              refine ⟨25690513602748966418795537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127009068499310945863691 25690513602748966418795537)
              ·
                refine ⟨19267885202061724814096653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25690513602748966418795537 19267885202061724814096653)
                ·
                  refine ⟨7225456950773146805286245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19267885202061724814096653 7225456950773146805286245)
                  ·
                    refine ⟨1354773178269965025991171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225456950773146805286245 1354773178269965025991171)
                    ·
                      rfl

theorem cell22_3957617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_3957617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957617 prefixEnd_3957617 := by exact prefixLift 3957617
  have htrace : WordTrace (prefixWord ++ tailWord_3957617) baseStart_3957617 baseEnd_3957617 := by
    simpa [prefixWord, tailWord_3957617, baseEnd_3957617] using wordTrace_append hprefix tailTrace_3957617
  have hstable : (prefixWord ++ tailWord_3957617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957617).length < 2 ^ (prefixWord ++ tailWord_3957617).sum := by decide
  have hdescent : baseEnd_3957617 < baseStart_3957617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957666 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3957666 : Nat := 118140960795 + 3957666 * 2 ^ 59
def prefixEnd_3957666 : Nat := 4983230072969 + 3 ^ 40 * 3957666 * 2
def baseEnd_3957666 : Nat := 451596650657115077172007

theorem tailTrace_3957666 : CollatzResearch.WordTrace tailWord_3957666 prefixEnd_3957666 451596650657115077172007 := by
  unfold tailWord_3957666
  simp only [CollatzResearch.WordTrace]
  refine ⟨36086984420014868096381213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96231958453372981590349901 36086984420014868096381213)
  ·
    refine ⟨13532619157505575536142955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36086984420014868096381213 13532619157505575536142955)
    ·
      refine ⟨20298928736258363304214433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13532619157505575536142955 20298928736258363304214433)
      ·
        refine ⟨15224196552193772478160825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20298928736258363304214433 15224196552193772478160825)
        ·
          refine ⟨11418147414145329358620619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224196552193772478160825 11418147414145329358620619)
          ·
            refine ⟨17127221121217994037930929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418147414145329358620619 17127221121217994037930929)
            ·
              refine ⟨12845415840913495528448197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17127221121217994037930929 12845415840913495528448197)
              ·
                refine ⟨2408515470171280411584037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12845415840913495528448197 2408515470171280411584037)
                ·
                  refine ⟨451596650657115077172007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408515470171280411584037 451596650657115077172007)
                  ·
                    rfl

theorem cell22_3957666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3957666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957666 prefixEnd_3957666 := by exact prefixLift 3957666
  have htrace : WordTrace (prefixWord ++ tailWord_3957666) baseStart_3957666 baseEnd_3957666 := by
    simpa [prefixWord, tailWord_3957666, baseEnd_3957666] using wordTrace_append hprefix tailTrace_3957666
  have hstable : (prefixWord ++ tailWord_3957666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957666).length < 2 ^ (prefixWord ++ tailWord_3957666).sum := by decide
  have hdescent : baseEnd_3957666 < baseStart_3957666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957681 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_3957681 : Nat := 118140960795 + 3957681 * 2 ^ 59
def prefixEnd_3957681 : Nat := 4983230072969 + 3 ^ 40 * 3957681 * 2
def baseEnd_3957681 : Nat := 1354795086777890192390975

theorem tailTrace_3957681 : CollatzResearch.WordTrace tailWord_3957681 prefixEnd_3957681 1354795086777890192390975 := by
  unfold tailWord_3957681
  simp only [CollatzResearch.WordTrace]
  refine ⟨144348484775005129947320897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96232323183336753298213931 144348484775005129947320897)
  ·
    refine ⟨108261363581253847460490673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144348484775005129947320897 108261363581253847460490673)
    ·
      refine ⟨81196022685940385595368005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108261363581253847460490673 81196022685940385595368005)
      ·
        refine ⟨15224254253613822299131501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81196022685940385595368005 15224254253613822299131501)
        ·
          refine ⟨5709095345105183362174313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15224254253613822299131501 5709095345105183362174313)
          ·
            refine ⟨4281821508828887521630735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709095345105183362174313 4281821508828887521630735)
            ·
              refine ⟨6422732263243331282446103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281821508828887521630735 6422732263243331282446103)
              ·
                refine ⟨9634098394864996923669155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422732263243331282446103 9634098394864996923669155)
                ·
                  refine ⟨14451147592297495385503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9634098394864996923669155 14451147592297495385503733)
                  ·
                    refine ⟨1354795086777890192390975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14451147592297495385503733 1354795086777890192390975)
                    ·
                      rfl

theorem cell22_3957681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_3957681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957681 prefixEnd_3957681 := by exact prefixLift 3957681
  have htrace : WordTrace (prefixWord ++ tailWord_3957681) baseStart_3957681 baseEnd_3957681 := by
    simpa [prefixWord, tailWord_3957681, baseEnd_3957681] using wordTrace_append hprefix tailTrace_3957681
  have hstable : (prefixWord ++ tailWord_3957681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957681).length < 2 ^ (prefixWord ++ tailWord_3957681).sum := by decide
  have hdescent : baseEnd_3957681 < baseStart_3957681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957700 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_3957700 : Nat := 118140960795 + 3957700 * 2 ^ 59
def prefixEnd_3957700 : Nat := 4983230072969 + 3 ^ 40 * 3957700 * 2
def baseEnd_3957700 : Nat := 451600530288726825388639

theorem tailTrace_3957700 : CollatzResearch.WordTrace tailWord_3957700 prefixEnd_3957700 451600530288726825388639 := by
  unfold tailWord_3957700
  simp only [CollatzResearch.WordTrace]
  refine ⟨72174588880968148096131277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96232785174624197461508369 72174588880968148096131277)
  ·
    refine ⟨27065470830363055536049229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72174588880968148096131277 27065470830363055536049229)
    ·
      refine ⟨10149551561386145826018461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27065470830363055536049229 10149551561386145826018461)
      ·
        refine ⟨3806081835519804684756923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10149551561386145826018461 3806081835519804684756923)
        ·
          refine ⟨5709122753279707027135385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806081835519804684756923 5709122753279707027135385)
          ·
            refine ⟨4281842064959780270351539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709122753279707027135385 4281842064959780270351539)
            ·
              refine ⟨6422763097439670405527309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281842064959780270351539 6422763097439670405527309)
              ·
                refine ⟨2408536161539876402072741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6422763097439670405527309 2408536161539876402072741)
                ·
                  refine ⟨451600530288726825388639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408536161539876402072741 451600530288726825388639)
                  ·
                    rfl

theorem cell22_3957700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_3957700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957700 prefixEnd_3957700 := by exact prefixLift 3957700
  have htrace : WordTrace (prefixWord ++ tailWord_3957700) baseStart_3957700 baseEnd_3957700 := by
    simpa [prefixWord, tailWord_3957700, baseEnd_3957700] using wordTrace_append hprefix tailTrace_3957700
  have hstable : (prefixWord ++ tailWord_3957700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957700).length < 2 ^ (prefixWord ++ tailWord_3957700).sum := by decide
  have hdescent : baseEnd_3957700 < baseStart_3957700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957769 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_3957769 : Nat := 118140960795 + 3957769 * 2 ^ 59
def prefixEnd_3957769 : Nat := 4983230072969 + 3 ^ 40 * 3957769 * 2
def baseEnd_3957769 : Nat := 1354825210976287296190705

theorem tailTrace_3957769 : CollatzResearch.WordTrace tailWord_3957769 prefixEnd_3957769 1354825210976287296190705 := by
  unfold tailWord_3957769
  simp only [CollatzResearch.WordTrace]
  refine ⟨144351694398686320976524361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96234462932457547317682907 144351694398686320976524361)
  ·
    refine ⟨108263770799014740732393271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144351694398686320976524361 108263770799014740732393271)
    ·
      refine ⟨162395656198522111098589907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108263770799014740732393271 162395656198522111098589907)
      ·
        refine ⟨243593484297783166647884861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162395656198522111098589907 243593484297783166647884861)
        ·
          refine ⟨91347556611668687492956823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243593484297783166647884861 91347556611668687492956823)
          ·
            refine ⟨137021334917503031239435235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91347556611668687492956823 137021334917503031239435235)
            ·
              refine ⟨205532002376254546859152853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137021334917503031239435235 205532002376254546859152853)
              ·
                refine ⟨4817156305693465942011395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 205532002376254546859152853 4817156305693465942011395)
                ·
                  refine ⟨7225734458540198913017093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4817156305693465942011395 7225734458540198913017093)
                  ·
                    refine ⟨1354825210976287296190705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7225734458540198913017093 1354825210976287296190705)
                    ·
                      rfl

theorem cell22_3957769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_3957769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957769 prefixEnd_3957769 := by exact prefixLift 3957769
  have htrace : WordTrace (prefixWord ++ tailWord_3957769) baseStart_3957769 baseEnd_3957769 := by
    simpa [prefixWord, tailWord_3957769, baseEnd_3957769] using wordTrace_append hprefix tailTrace_3957769
  have hstable : (prefixWord ++ tailWord_3957769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957769).length < 2 ^ (prefixWord ++ tailWord_3957769).sum := by decide
  have hdescent : baseEnd_3957769 < baseStart_3957769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957861 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_3957861 : Nat := 118140960795 + 3957861 * 2 ^ 59
def prefixEnd_3957861 : Nat := 4983230072969 + 3 ^ 40 * 3957861 * 2
def baseEnd_3957861 : Nat := 1354856704456429722890423

theorem tailTrace_3957861 : CollatzResearch.WordTrace tailWord_3957861 prefixEnd_3957861 1354856704456429722890423 := by
  unfold tailWord_3957861
  simp only [CollatzResearch.WordTrace]
  refine ⟨144355049914353020688873437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96236699942902013792582291 144355049914353020688873437)
  ·
    refine ⟨54133143717882382758327539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144355049914353020688873437 54133143717882382758327539)
    ·
      refine ⟨81199715576823574137491309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54133143717882382758327539 81199715576823574137491309)
      ·
        refine ⟨30449893341308840301559241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81199715576823574137491309 30449893341308840301559241)
        ·
          refine ⟨22837420005981630226169431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30449893341308840301559241 22837420005981630226169431)
          ·
            refine ⟨34256130008972445339254147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837420005981630226169431 34256130008972445339254147)
            ·
              refine ⟨51384195013458668008881221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34256130008972445339254147 51384195013458668008881221)
              ·
                refine ⟨9634536565023500251665229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51384195013458668008881221 9634536565023500251665229)
                ·
                  refine ⟨3612951211883812594374461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9634536565023500251665229 3612951211883812594374461)
                  ·
                    refine ⟨1354856704456429722890423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612951211883812594374461 1354856704456429722890423)
                    ·
                      rfl

theorem cell22_3957861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_3957861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957861 prefixEnd_3957861 := by exact prefixLift 3957861
  have htrace : WordTrace (prefixWord ++ tailWord_3957861) baseStart_3957861 baseEnd_3957861 := by
    simpa [prefixWord, tailWord_3957861, baseEnd_3957861] using wordTrace_append hprefix tailTrace_3957861
  have hstable : (prefixWord ++ tailWord_3957861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957861).length < 2 ^ (prefixWord ++ tailWord_3957861).sum := by decide
  have hdescent : baseEnd_3957861 < baseStart_3957861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957874 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3957874 : Nat := 118140960795 + 3957874 * 2 ^ 59
def prefixEnd_3957874 : Nat := 4983230072969 + 3 ^ 40 * 3957874 * 2
def baseEnd_3957874 : Nat := 451620384874034007438461

theorem tailTrace_3957874 : CollatzResearch.WordTrace tailWord_3957874 prefixEnd_3957874 451620384874034007438461 := by
  unfold tailWord_3957874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36088881015826480977274169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96237016042203949272731117 36088881015826480977274169)
  ·
    refine ⟨27066660761869860732955627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36088881015826480977274169 27066660761869860732955627)
    ·
      refine ⟨40599991142804791099433441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27066660761869860732955627 40599991142804791099433441)
      ·
        refine ⟨30449993357103593324575081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40599991142804791099433441 30449993357103593324575081)
        ·
          refine ⟨22837495017827694993431311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30449993357103593324575081 22837495017827694993431311)
          ·
            refine ⟨34256242526741542490146967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837495017827694993431311 34256242526741542490146967)
            ·
              refine ⟨51384363790112313735220451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34256242526741542490146967 51384363790112313735220451)
              ·
                refine ⟨77076545685168470602830677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51384363790112313735220451 77076545685168470602830677)
                ·
                  refine ⟨451620384874034007438461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77076545685168470602830677 451620384874034007438461)
                  ·
                    rfl

theorem cell22_3957874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3957874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957874 prefixEnd_3957874 := by exact prefixLift 3957874
  have htrace : WordTrace (prefixWord ++ tailWord_3957874) baseStart_3957874 baseEnd_3957874 := by
    simpa [prefixWord, tailWord_3957874, baseEnd_3957874] using wordTrace_append hprefix tailTrace_3957874
  have hstable : (prefixWord ++ tailWord_3957874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957874).length < 2 ^ (prefixWord ++ tailWord_3957874).sum := by decide
  have hdescent : baseEnd_3957874 < baseStart_3957874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957921 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3957921 : Nat := 118140960795 + 3957921 * 2 ^ 59
def prefixEnd_3957921 : Nat := 4983230072969 + 3 ^ 40 * 3957921 * 2
def baseEnd_3957921 : Nat := 1354877243682609566390239

theorem tailTrace_3957921 : CollatzResearch.WordTrace tailWord_3957921 prefixEnd_3957921 1354877243682609566390239 := by
  unfold tailWord_3957921
  simp only [CollatzResearch.WordTrace]
  refine ⟨144357238294135650936057617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96238158862757100624038411 144357238294135650936057617)
  ·
    refine ⟨108267928720601738202043213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144357238294135650936057617 108267928720601738202043213)
    ·
      refine ⟨40600473270225651825766205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108267928720601738202043213 40600473270225651825766205)
      ·
        refine ⟨15225177476334619434662327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40600473270225651825766205 15225177476334619434662327)
        ·
          refine ⟨22837766214501929151993491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15225177476334619434662327 22837766214501929151993491)
          ·
            refine ⟨34256649321752893727990237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22837766214501929151993491 34256649321752893727990237)
            ·
              refine ⟨12846243495657335147996339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34256649321752893727990237 12846243495657335147996339)
              ·
                refine ⟨19269365243486002721994509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846243495657335147996339 19269365243486002721994509)
                ·
                  refine ⟨7226011966307251020747941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19269365243486002721994509 7226011966307251020747941)
                  ·
                    refine ⟨1354877243682609566390239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7226011966307251020747941 1354877243682609566390239)
                    ·
                      rfl

theorem cell22_3957921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3957921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957921 prefixEnd_3957921 := by exact prefixLift 3957921
  have htrace : WordTrace (prefixWord ++ tailWord_3957921) baseStart_3957921 baseEnd_3957921 := by
    simpa [prefixWord, tailWord_3957921, baseEnd_3957921] using wordTrace_append hprefix tailTrace_3957921
  have hstable : (prefixWord ++ tailWord_3957921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957921).length < 2 ^ (prefixWord ++ tailWord_3957921).sum := by decide
  have hdescent : baseEnd_3957921 < baseStart_3957921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957942 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3957942 : Nat := 118140960795 + 3957942 * 2 ^ 59
def prefixEnd_3957942 : Nat := 4983230072969 + 3 ^ 40 * 3957942 * 2
def baseEnd_3957942 : Nat := 451628144137257503871725

theorem tailTrace_3957942 : CollatzResearch.WordTrace tailWord_3957942 prefixEnd_3957942 451628144137257503871725 := by
  unfold tailWord_3957942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022375264191223220160755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96238669484706381015048053 9022375264191223220160755)
  ·
    refine ⟨13533562896286834830241133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022375264191223220160755 13533562896286834830241133)
    ·
      refine ⟨5075086086107563061340425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13533562896286834830241133 5075086086107563061340425)
      ·
        refine ⟨3806314564580672296005319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5075086086107563061340425 3806314564580672296005319)
        ·
          refine ⟨5709471846871008444007979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806314564580672296005319 5709471846871008444007979)
          ·
            refine ⟨8564207770306512666011969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709471846871008444007979 8564207770306512666011969)
            ·
              refine ⟨6423155827729884499508977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8564207770306512666011969 6423155827729884499508977)
              ·
                refine ⟨4817366870797413374631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423155827729884499508977 4817366870797413374631733)
                ·
                  refine ⟨451628144137257503871725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4817366870797413374631733 451628144137257503871725)
                  ·
                    rfl

theorem cell22_3957942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3957942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957942 prefixEnd_3957942 := by exact prefixLift 3957942
  have htrace : WordTrace (prefixWord ++ tailWord_3957942) baseStart_3957942 baseEnd_3957942 := by
    simpa [prefixWord, tailWord_3957942, baseEnd_3957942] using wordTrace_append hprefix tailTrace_3957942
  have hstable : (prefixWord ++ tailWord_3957942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957942).length < 2 ^ (prefixWord ++ tailWord_3957942).sum := by decide
  have hdescent : baseEnd_3957942 < baseStart_3957942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3957951 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 4, 3]
def baseStart_3957951 : Nat := 118140960795 + 3957951 * 2 ^ 59
def prefixEnd_3957951 : Nat := 4983230072969 + 3 ^ 40 * 3957951 * 2
def baseEnd_3957951 : Nat := 1354887513295699488140147

theorem tailTrace_3957951 : CollatzResearch.WordTrace tailWord_3957951 prefixEnd_3957951 1354887513295699488140147 := by
  unfold tailWord_3957951
  simp only [CollatzResearch.WordTrace]
  refine ⟨144358332484026966059649707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96238888322684644039766471 144358332484026966059649707)
  ·
    refine ⟨216537498726040449089474561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144358332484026966059649707 216537498726040449089474561)
    ·
      refine ⟨162403124044530336817105921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216537498726040449089474561 162403124044530336817105921)
      ·
        refine ⟨121802343033397752612829441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162403124044530336817105921 121802343033397752612829441)
        ·
          refine ⟨91351757275048314459622081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121802343033397752612829441 91351757275048314459622081)
          ·
            refine ⟨68513817956286235844716561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91351757275048314459622081 68513817956286235844716561)
            ·
              refine ⟨51385363467214676883537421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68513817956286235844716561 51385363467214676883537421)
              ·
                refine ⟨19269511300205503831326533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51385363467214676883537421 19269511300205503831326533)
                ·
                  refine ⟨3613033368788531968373725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19269511300205503831326533 3613033368788531968373725)
                  ·
                    refine ⟨1354887513295699488140147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613033368788531968373725 1354887513295699488140147)
                    ·
                      rfl

theorem cell22_3957951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_3957951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3957951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3957951 prefixEnd_3957951 := by exact prefixLift 3957951
  have htrace : WordTrace (prefixWord ++ tailWord_3957951) baseStart_3957951 baseEnd_3957951 := by
    simpa [prefixWord, tailWord_3957951, baseEnd_3957951] using wordTrace_append hprefix tailTrace_3957951
  have hstable : (prefixWord ++ tailWord_3957951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3957951).length < 2 ^ (prefixWord ++ tailWord_3957951).sum := by decide
  have hdescent : baseEnd_3957951 < baseStart_3957951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3957951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958002 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3958002 : Nat := 118140960795 + 3958002 * 2 ^ 59
def prefixEnd_3958002 : Nat := 4983230072969 + 3 ^ 40 * 3958002 * 2
def baseEnd_3958002 : Nat := 1354904971637952355114991

theorem tailTrace_3958002 : CollatzResearch.WordTrace tailWord_3958002 prefixEnd_3958002 1354904971637952355114991 := by
  unfold tailWord_3958002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36090048151710550442439065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96240128404561467846504173 36090048151710550442439065)
  ·
    refine ⟨27067536113782912831829299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36090048151710550442439065 27067536113782912831829299)
    ·
      refine ⟨40601304170674369247743949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067536113782912831829299 40601304170674369247743949)
      ·
        refine ⟨15225489064002888467903981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40601304170674369247743949 15225489064002888467903981)
        ·
          refine ⟨5709558399001083175463993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15225489064002888467903981 5709558399001083175463993)
          ·
            refine ⟨4282168799250812381597995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709558399001083175463993 4282168799250812381597995)
            ·
              refine ⟨6423253198876218572396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282168799250812381597995 6423253198876218572396993)
              ·
                refine ⟨4817439899157163929297745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6423253198876218572396993 4817439899157163929297745)
                ·
                  refine ⟨3613079924367872946973309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817439899157163929297745 3613079924367872946973309)
                  ·
                    refine ⟨1354904971637952355114991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613079924367872946973309 1354904971637952355114991)
                    ·
                      rfl

theorem cell22_3958002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3958002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958002 prefixEnd_3958002 := by exact prefixLift 3958002
  have htrace : WordTrace (prefixWord ++ tailWord_3958002) baseStart_3958002 baseEnd_3958002 := by
    simpa [prefixWord, tailWord_3958002, baseEnd_3958002] using wordTrace_append hprefix tailTrace_3958002
  have hstable : (prefixWord ++ tailWord_3958002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958002).length < 2 ^ (prefixWord ++ tailWord_3958002).sum := by decide
  have hdescent : baseEnd_3958002 < baseStart_3958002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958103 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_3958103 : Nat := 118140960795 + 3958103 * 2 ^ 59
def prefixEnd_3958103 : Nat := 4983230072969 + 3 ^ 40 * 3958103 * 2
def baseEnd_3958103 : Nat := 1354939546002021758339681

theorem tailTrace_3958103 : CollatzResearch.WordTrace tailWord_3958103 prefixEnd_3958103 1354939546002021758339681 := by
  unfold tailWord_3958103
  simp only [CollatzResearch.WordTrace]
  refine ⟨144363876379476296019182963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96242584252984197346121975 144363876379476296019182963)
  ·
    refine ⟨216545814569214444028774445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144363876379476296019182963 216545814569214444028774445)
    ·
      refine ⟨81204680463455416510790417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216545814569214444028774445 81204680463455416510790417)
      ·
        refine ⟨60903510347591562383092813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81204680463455416510790417 60903510347591562383092813)
        ·
          refine ⟨22838816380346835893659805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60903510347591562383092813 22838816380346835893659805)
          ·
            refine ⟨8564556142630063460122427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22838816380346835893659805 8564556142630063460122427)
            ·
              refine ⟨12846834213945095190183641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564556142630063460122427 12846834213945095190183641)
              ·
                refine ⟨9635125660458821392637731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12846834213945095190183641 9635125660458821392637731)
                ·
                  refine ⟨14452688490688232088956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635125660458821392637731 14452688490688232088956597)
                  ·
                    refine ⟨1354939546002021758339681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14452688490688232088956597 1354939546002021758339681)
                    ·
                      rfl

theorem cell22_3958103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_3958103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958103 prefixEnd_3958103 := by exact prefixLift 3958103
  have htrace : WordTrace (prefixWord ++ tailWord_3958103) baseStart_3958103 baseEnd_3958103 := by
    simpa [prefixWord, tailWord_3958103, baseEnd_3958103] using wordTrace_append hprefix tailTrace_3958103
  have hstable : (prefixWord ++ tailWord_3958103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958103).length < 2 ^ (prefixWord ++ tailWord_3958103).sum := by decide
  have hdescent : baseEnd_3958103 < baseStart_3958103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958116 : List Nat := [2, 3, 1, 1, 3, 12]
def baseStart_3958116 : Nat := 118140960795 + 3958116 * 2 ^ 59
def prefixEnd_3958116 : Nat := 4983230072969 + 3 ^ 40 * 3958116 * 2
def baseEnd_3958116 : Nat := 16727703656391284663761

theorem tailTrace_3958116 : CollatzResearch.WordTrace tailWord_3958116 prefixEnd_3958116 16727703656391284663761 := by
  unfold tailWord_3958116
  simp only [CollatzResearch.WordTrace]
  refine ⟨72182175264214599619703101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96242900352286132826270801 72182175264214599619703101)
  ·
    refine ⟨27068315724080474857388663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72182175264214599619703101 27068315724080474857388663)
    ·
      refine ⟨40602473586120712286082995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27068315724080474857388663 40602473586120712286082995)
      ·
        refine ⟨60903710379181068429124493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40602473586120712286082995 60903710379181068429124493)
        ·
          refine ⟨22838891392192900660921685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60903710379181068429124493 22838891392192900660921685)
          ·
            refine ⟨16727703656391284663761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22838891392192900660921685 16727703656391284663761)
            ·
              rfl

theorem cell22_3958116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 12].length) (baseStart_3958116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958116 prefixEnd_3958116 := by exact prefixLift 3958116
  have htrace : WordTrace (prefixWord ++ tailWord_3958116) baseStart_3958116 baseEnd_3958116 := by
    simpa [prefixWord, tailWord_3958116, baseEnd_3958116] using wordTrace_append hprefix tailTrace_3958116
  have hstable : (prefixWord ++ tailWord_3958116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958116).length < 2 ^ (prefixWord ++ tailWord_3958116).sum := by decide
  have hdescent : baseEnd_3958116 < baseStart_3958116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958122 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_3958122 : Nat := 118140960795 + 3958122 * 2 ^ 59
def prefixEnd_3958122 : Nat := 4983230072969 + 3 ^ 40 * 3958122 * 2
def baseEnd_3958122 : Nat := 451648683363437347371541

theorem tailTrace_3958122 : CollatzResearch.WordTrace tailWord_3958122 prefixEnd_3958122 451648683363437347371541 := by
  unfold tailWord_3958122
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091142341601865566031155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96243046244271641509416413 36091142341601865566031155)
  ·
    refine ⟨54136713512402798349046733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091142341601865566031155 54136713512402798349046733)
    ·
      refine ⟨20301267567151049380892525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54136713512402798349046733 20301267567151049380892525)
      ·
        refine ⟨7612975337681643517834697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20301267567151049380892525 7612975337681643517834697)
        ·
          refine ⟨5709731503261232638376023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7612975337681643517834697 5709731503261232638376023)
          ·
            refine ⟨8564597254891848957564035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709731503261232638376023 8564597254891848957564035)
            ·
              refine ⟨12846895882337773436346053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564597254891848957564035 12846895882337773436346053)
              ·
                refine ⟨2408792977938332519314885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12846895882337773436346053 2408792977938332519314885)
                ·
                  refine ⟨451648683363437347371541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408792977938332519314885 451648683363437347371541)
                  ·
                    rfl

theorem cell22_3958122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_3958122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958122 prefixEnd_3958122 := by exact prefixLift 3958122
  have htrace : WordTrace (prefixWord ++ tailWord_3958122) baseStart_3958122 baseEnd_3958122 := by
    simpa [prefixWord, tailWord_3958122, baseEnd_3958122] using wordTrace_append hprefix tailTrace_3958122
  have hstable : (prefixWord ++ tailWord_3958122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958122).length < 2 ^ (prefixWord ++ tailWord_3958122).sum := by decide
  have hdescent : baseEnd_3958122 < baseStart_3958122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958161 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 9]
def baseStart_3958161 : Nat := 118140960795 + 3958161 * 2 ^ 59
def prefixEnd_3958161 : Nat := 4983230072969 + 3 ^ 40 * 3958161 * 2
def baseEnd_3958161 : Nat := 451653133529109646796501

theorem tailTrace_3958161 : CollatzResearch.WordTrace tailWord_3958161 prefixEnd_3958161 451653133529109646796501 := by
  unfold tailWord_3958161
  simp only [CollatzResearch.WordTrace]
  refine ⟨144365991813266171924794337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96243994542177447949862891 144365991813266171924794337)
  ·
    refine ⟨108274493859949628943595753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144365991813266171924794337 108274493859949628943595753)
    ·
      refine ⟨81205870394962221707696815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108274493859949628943595753 81205870394962221707696815)
      ·
        refine ⟨121808805592443332561545223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81205870394962221707696815 121808805592443332561545223)
        ·
          refine ⟨182713208388664998842317835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121808805592443332561545223 182713208388664998842317835)
          ·
            refine ⟨274069812582997498263476753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182713208388664998842317835 274069812582997498263476753)
            ·
              refine ⟨205552359437248123697607565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274069812582997498263476753 205552359437248123697607565)
              ·
                refine ⟨77082134788968046386602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205552359437248123697607565 77082134788968046386602837)
                ·
                  refine ⟨451653133529109646796501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77082134788968046386602837 451653133529109646796501)
                  ·
                    rfl

theorem cell22_3958161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_3958161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958161 prefixEnd_3958161 := by exact prefixLift 3958161
  have htrace : WordTrace (prefixWord ++ tailWord_3958161) baseStart_3958161 baseEnd_3958161 := by
    simpa [prefixWord, tailWord_3958161, baseEnd_3958161] using wordTrace_append hprefix tailTrace_3958161
  have hstable : (prefixWord ++ tailWord_3958161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958161).length < 2 ^ (prefixWord ++ tailWord_3958161).sum := by decide
  have hdescent : baseEnd_3958161 < baseStart_3958161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958193 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_3958193 : Nat := 118140960795 + 3958193 * 2 ^ 59
def prefixEnd_3958193 : Nat := 4983230072969 + 3 ^ 40 * 3958193 * 2
def baseEnd_3958193 : Nat := 1354970354841291523589405

theorem tailTrace_3958193 : CollatzResearch.WordTrace tailWord_3958193 prefixEnd_3958193 1354970354841291523589405 := by
  unfold tailWord_3958193
  simp only [CollatzResearch.WordTrace]
  refine ⟨144367158949150241389959233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96244772632766827593306155 144367158949150241389959233)
  ·
    refine ⟨108275369211862681042469425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144367158949150241389959233 108275369211862681042469425)
    ·
      refine ⟨81206526908897010781852069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108275369211862681042469425 81206526908897010781852069)
      ·
        refine ⟨15226223795418189521597263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81206526908897010781852069 15226223795418189521597263)
        ·
          refine ⟨22839335693127284282395895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15226223795418189521597263 22839335693127284282395895)
          ·
            refine ⟨34259003539690926423593843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22839335693127284282395895 34259003539690926423593843)
            ·
              refine ⟨51388505309536389635390765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34259003539690926423593843 51388505309536389635390765)
              ·
                refine ⟨19270689491076146113271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51388505309536389635390765 19270689491076146113271537)
                ·
                  refine ⟨14453017118307109584953653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19270689491076146113271537 14453017118307109584953653)
                  ·
                    refine ⟨1354970354841291523589405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14453017118307109584953653 1354970354841291523589405)
                    ·
                      rfl

theorem cell22_3958193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_3958193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958193 prefixEnd_3958193 := by exact prefixLift 3958193
  have htrace : WordTrace (prefixWord ++ tailWord_3958193) baseStart_3958193 baseEnd_3958193 := by
    simpa [prefixWord, tailWord_3958193, baseEnd_3958193] using wordTrace_append hprefix tailTrace_3958193
  have hstable : (prefixWord ++ tailWord_3958193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958193).length < 2 ^ (prefixWord ++ tailWord_3958193).sum := by decide
  have hdescent : baseEnd_3958193 < baseStart_3958193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958208 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_3958208 : Nat := 118140960795 + 3958208 * 2 ^ 59
def prefixEnd_3958208 : Nat := 4983230072969 + 3 ^ 40 * 3958208 * 2
def baseEnd_3958208 : Nat := 1354975489647836484464359

theorem tailTrace_3958208 : CollatzResearch.WordTrace tailWord_3958208 prefixEnd_3958208 1354975489647836484464359 := by
  unfold tailWord_3958208
  simp only [CollatzResearch.WordTrace]
  refine ⟨72183853022047949475877639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96245137362730599301170185 72183853022047949475877639)
  ·
    refine ⟨108275779533071924213816459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72183853022047949475877639 108275779533071924213816459)
    ·
      refine ⟨162413669299607886320724689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108275779533071924213816459 162413669299607886320724689)
      ·
        refine ⟨121810251974705914740543517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162413669299607886320724689 121810251974705914740543517)
        ·
          refine ⟨45678844490514718027703819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121810251974705914740543517 45678844490514718027703819)
          ·
            refine ⟨68518266735772077041555729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45678844490514718027703819 68518266735772077041555729)
            ·
              refine ⟨51388700051829057781166797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68518266735772077041555729 51388700051829057781166797)
              ·
                refine ⟨19270762519435896667937549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51388700051829057781166797 19270762519435896667937549)
                ·
                  refine ⟨7226535944788461250476581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19270762519435896667937549 7226535944788461250476581)
                  ·
                    refine ⟨1354975489647836484464359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7226535944788461250476581 1354975489647836484464359)
                    ·
                      rfl

theorem cell22_3958208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_3958208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958208 prefixEnd_3958208 := by exact prefixLift 3958208
  have htrace : WordTrace (prefixWord ++ tailWord_3958208) baseStart_3958208 baseEnd_3958208 := by
    simpa [prefixWord, tailWord_3958208, baseEnd_3958208] using wordTrace_append hprefix tailTrace_3958208
  have hstable : (prefixWord ++ tailWord_3958208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958208).length < 2 ^ (prefixWord ++ tailWord_3958208).sum := by decide
  have hdescent : baseEnd_3958208 < baseStart_3958208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958268 : List Nat := [2, 2, 2, 1, 2, 1, 4, 8]
def baseStart_3958268 : Nat := 118140960795 + 3958268 * 2 ^ 59
def prefixEnd_3958268 : Nat := 4983230072969 + 3 ^ 40 * 3958268 * 2
def baseEnd_3958268 : Nat := 150555114319335147551575

theorem tailTrace_3958268 : CollatzResearch.WordTrace tailWord_3958268 prefixEnd_3958268 150555114319335147551575 := by
  unfold tailWord_3958268
  simp only [CollatzResearch.WordTrace]
  refine ⟨72184947211939264599469729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96246596282585686132626305 72184947211939264599469729)
  ·
    refine ⟨54138710408954448449602297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72184947211939264599469729 54138710408954448449602297)
    ·
      refine ⟨40604032806715836337201723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54138710408954448449602297 40604032806715836337201723)
      ·
        refine ⟨60906049210073754505802585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40604032806715836337201723 60906049210073754505802585)
        ·
          refine ⟨45679536907555315879351939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60906049210073754505802585 45679536907555315879351939)
          ·
            refine ⟨68519305361332973819027909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45679536907555315879351939 68519305361332973819027909)
            ·
              refine ⟨12847369755249932591067733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68519305361332973819027909 12847369755249932591067733)
              ·
                refine ⟨150555114319335147551575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12847369755249932591067733 150555114319335147551575)
                ·
                  rfl

theorem cell22_3958268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_3958268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958268 prefixEnd_3958268 := by exact prefixLift 3958268
  have htrace : WordTrace (prefixWord ++ tailWord_3958268) baseStart_3958268 baseEnd_3958268 := by
    simpa [prefixWord, tailWord_3958268, baseEnd_3958268] using wordTrace_append hprefix tailTrace_3958268
  have hstable : (prefixWord ++ tailWord_3958268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958268).length < 2 ^ (prefixWord ++ tailWord_3958268).sum := by decide
  have hdescent : baseEnd_3958268 < baseStart_3958268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958364 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_3958364 : Nat := 118140960795 + 3958364 * 2 ^ 59
def prefixEnd_3958364 : Nat := 4983230072969 + 3 ^ 40 * 3958364 * 2
def baseEnd_3958364 : Nat := 451676297211968025854627

theorem tailTrace_3958364 : CollatzResearch.WordTrace tailWord_3958364 prefixEnd_3958364 451676297211968025854627 := by
  unfold tailWord_3958364
  simp only [CollatzResearch.WordTrace]
  refine ⟨72186697915765368797217073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96248930554353825062956097 72186697915765368797217073)
  ·
    refine ⟨54140023436824026597912805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72186697915765368797217073 54140023436824026597912805)
    ·
      refine ⟨10151254394404504987108651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54140023436824026597912805 10151254394404504987108651)
      ·
        refine ⟨15226881591606757480662977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151254394404504987108651 15226881591606757480662977)
        ·
          refine ⟨11420161193705068110497233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15226881591606757480662977 11420161193705068110497233)
          ·
            refine ⟨8565120895278801082872925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11420161193705068110497233 8565120895278801082872925)
            ·
              refine ⟨3211920335729550406077347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8565120895278801082872925 3211920335729550406077347)
              ·
                refine ⟨4817880503594325609116021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211920335729550406077347 4817880503594325609116021)
                ·
                  refine ⟨451676297211968025854627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4817880503594325609116021 451676297211968025854627)
                  ·
                    rfl

theorem cell22_3958364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_3958364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958364 prefixEnd_3958364 := by exact prefixLift 3958364
  have htrace : WordTrace (prefixWord ++ tailWord_3958364) baseStart_3958364 baseEnd_3958364 := by
    simpa [prefixWord, tailWord_3958364, baseEnd_3958364] using wordTrace_append hprefix tailTrace_3958364
  have hstable : (prefixWord ++ tailWord_3958364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958364).length < 2 ^ (prefixWord ++ tailWord_3958364).sum := by decide
  have hdescent : baseEnd_3958364 < baseStart_3958364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958375 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 6]
def baseStart_3958375 : Nat := 118140960795 + 3958375 * 2 ^ 59
def prefixEnd_3958375 : Nat := 4983230072969 + 3 ^ 40 * 3958375 * 2
def baseEnd_3958375 : Nat := 451677552386901238512949

theorem tailTrace_3958375 : CollatzResearch.WordTrace tailWord_3958375 prefixEnd_3958375 451677552386901238512949 := by
  unfold tailWord_3958375
  simp only [CollatzResearch.WordTrace]
  refine ⟨144373797034490886473084579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96249198022993924315389719 144373797034490886473084579)
  ·
    refine ⟨216560695551736329709626869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144373797034490886473084579 216560695551736329709626869)
    ·
      refine ⟨20302565207975280910277519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216560695551736329709626869 20302565207975280910277519)
      ·
        refine ⟨30453847811962921365416279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20302565207975280910277519 30453847811962921365416279)
        ·
          refine ⟨45680771717944382048124419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453847811962921365416279 45680771717944382048124419)
          ·
            refine ⟨68521157576916573072186629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45680771717944382048124419 68521157576916573072186629)
            ·
              refine ⟨12847717045671857451034993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68521157576916573072186629 12847717045671857451034993)
              ·
                refine ⟨9635787784253893088276245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12847717045671857451034993 9635787784253893088276245)
                ·
                  refine ⟨451677552386901238512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9635787784253893088276245 451677552386901238512949)
                  ·
                    rfl

theorem cell22_3958375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_3958375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958375 prefixEnd_3958375 := by exact prefixLift 3958375
  have htrace : WordTrace (prefixWord ++ tailWord_3958375) baseStart_3958375 baseEnd_3958375 := by
    simpa [prefixWord, tailWord_3958375, baseEnd_3958375] using wordTrace_append hprefix tailTrace_3958375
  have hstable : (prefixWord ++ tailWord_3958375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958375).length < 2 ^ (prefixWord ++ tailWord_3958375).sum := by decide
  have hdescent : baseEnd_3958375 < baseStart_3958375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958407 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 4, 3]
def baseStart_3958407 : Nat := 118140960795 + 3958407 * 2 ^ 59
def prefixEnd_3958407 : Nat := 4983230072969 + 3 ^ 40 * 3958407 * 2
def baseEnd_3958407 : Nat := 1355043611414666298738749

theorem tailTrace_3958407 : CollatzResearch.WordTrace tailWord_3958407 prefixEnd_3958407 1355043611414666298738749 := by
  unfold tailWord_3958407
  simp only [CollatzResearch.WordTrace]
  refine ⟨144374964170374955938249475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96249976113583303958832983 144374964170374955938249475)
  ·
    refine ⟨216562446255562433907374213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144374964170374955938249475 216562446255562433907374213)
    ·
      refine ⟨40605458672917956357632665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 216562446255562433907374213 40605458672917956357632665)
      ·
        refine ⟨30454094004688467268224499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40605458672917956357632665 30454094004688467268224499)
        ·
          refine ⟨45681141007032700902336749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30454094004688467268224499 45681141007032700902336749)
          ·
            refine ⟨17130427877637262838376281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45681141007032700902336749 17130427877637262838376281)
            ·
              refine ⟨12847820908227947128782211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130427877637262838376281 12847820908227947128782211)
              ·
                refine ⟨19271731362341920693173317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12847820908227947128782211 19271731362341920693173317)
                ·
                  refine ⟨3613449630439110129969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19271731362341920693173317 3613449630439110129969997)
                  ·
                    refine ⟨1355043611414666298738749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613449630439110129969997 1355043611414666298738749)
                    ·
                      rfl

theorem cell22_3958407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_3958407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958407 prefixEnd_3958407 := by exact prefixLift 3958407
  have htrace : WordTrace (prefixWord ++ tailWord_3958407) baseStart_3958407 baseEnd_3958407 := by
    simpa [prefixWord, tailWord_3958407, baseEnd_3958407] using wordTrace_append hprefix tailTrace_3958407
  have hstable : (prefixWord ++ tailWord_3958407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958407).length < 2 ^ (prefixWord ++ tailWord_3958407).sum := by decide
  have hdescent : baseEnd_3958407 < baseStart_3958407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958424 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_3958424 : Nat := 118140960795 + 3958424 * 2 ^ 59
def prefixEnd_3958424 : Nat := 4983230072969 + 3 ^ 40 * 3958424 * 2
def baseEnd_3958424 : Nat := 1355049430862083921063697

theorem tailTrace_3958424 : CollatzResearch.WordTrace tailWord_3958424 prefixEnd_3958424 1355049430862083921063697 := by
  unfold tailWord_3958424
  simp only [CollatzResearch.WordTrace]
  refine ⟨72187792105656683920809163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96250389474208911894412217 72187792105656683920809163)
  ·
    refine ⟨108281688158485025881213745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72187792105656683920809163 108281688158485025881213745)
    ·
      refine ⟨81211266118863769410910309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108281688158485025881213745 81211266118863769410910309)
      ·
        refine ⟨15227112397286956764545683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81211266118863769410910309 15227112397286956764545683)
        ·
          refine ⟨22840668595930435146818525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227112397286956764545683 22840668595930435146818525)
          ·
            refine ⟨8565250723473913180056947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22840668595930435146818525 8565250723473913180056947)
            ·
              refine ⟨12847876085210869770085421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565250723473913180056947 12847876085210869770085421)
              ·
                refine ⟨4817953531954076163782033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12847876085210869770085421 4817953531954076163782033)
                ·
                  refine ⟨3613465148965557122836525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817953531954076163782033 3613465148965557122836525)
                  ·
                    refine ⟨1355049430862083921063697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613465148965557122836525 1355049430862083921063697)
                    ·
                      rfl

theorem cell22_3958424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_3958424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958424 prefixEnd_3958424 := by exact prefixLift 3958424
  have htrace : WordTrace (prefixWord ++ tailWord_3958424) baseStart_3958424 baseEnd_3958424 := by
    simpa [prefixWord, tailWord_3958424, baseEnd_3958424] using wordTrace_append hprefix tailTrace_3958424
  have hstable : (prefixWord ++ tailWord_3958424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958424).length < 2 ^ (prefixWord ++ tailWord_3958424).sum := by decide
  have hdescent : baseEnd_3958424 < baseStart_3958424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958469 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_3958469 : Nat := 118140960795 + 3958469 * 2 ^ 59
def prefixEnd_3958469 : Nat := 4983230072969 + 3 ^ 40 * 3958469 * 2
def baseEnd_3958469 : Nat := 1355064835281718803688559

theorem tailTrace_3958469 : CollatzResearch.WordTrace tailWord_3958469 prefixEnd_3958469 1355064835281718803688559 := by
  unfold tailWord_3958469
  simp only [CollatzResearch.WordTrace]
  refine ⟨144377225496150340527006461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96251483664100227018004307 144377225496150340527006461)
  ·
    refine ⟨54141459561056377697627423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144377225496150340527006461 54141459561056377697627423)
    ·
      refine ⟨81212189341584566546441135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54141459561056377697627423 81212189341584566546441135)
      ·
        refine ⟨121818284012376849819661703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81212189341584566546441135 121818284012376849819661703)
        ·
          refine ⟨182727426018565274729492555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121818284012376849819661703 182727426018565274729492555)
          ·
            refine ⟨274091139027847912094238833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182727426018565274729492555 274091139027847912094238833)
            ·
              refine ⟨205568354270885934070679125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274091139027847912094238833 205568354270885934070679125)
              ·
                refine ⟨2409004151611944539890771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 205568354270885934070679125 2409004151611944539890771)
                ·
                  refine ⟨3613506227417916809836157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409004151611944539890771 3613506227417916809836157)
                  ·
                    refine ⟨1355064835281718803688559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3613506227417916809836157 1355064835281718803688559)
                    ·
                      rfl

theorem cell22_3958469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_3958469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958469 prefixEnd_3958469 := by exact prefixLift 3958469
  have htrace : WordTrace (prefixWord ++ tailWord_3958469) baseStart_3958469 baseEnd_3958469 := by
    simpa [prefixWord, tailWord_3958469, baseEnd_3958469] using wordTrace_append hprefix tailTrace_3958469
  have hstable : (prefixWord ++ tailWord_3958469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958469).length < 2 ^ (prefixWord ++ tailWord_3958469).sum := by decide
  have hdescent : baseEnd_3958469 < baseStart_3958469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958516 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3958516 : Nat := 118140960795 + 3958516 * 2 ^ 59
def prefixEnd_3958516 : Nat := 4983230072969 + 3 ^ 40 * 3958516 * 2
def baseEnd_3958516 : Nat := 451693641447408782587805

theorem tailTrace_3958516 : CollatzResearch.WordTrace tailWord_3958516 prefixEnd_3958516 451693641447408782587805 := by
  unfold tailWord_3958516
  simp only [CollatzResearch.WordTrace]
  refine ⟨72189469863490033776983701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96252626484653378369311601 72189469863490033776983701)
  ·
    refine ⟨3383881399851095333296111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72189469863490033776983701 3383881399851095333296111)
    ·
      refine ⟨5075822099776642999944167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383881399851095333296111 5075822099776642999944167)
      ·
        refine ⟨7613733149664964499916251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075822099776642999944167 7613733149664964499916251)
        ·
          refine ⟨11420599724497446749874377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613733149664964499916251 11420599724497446749874377)
          ·
            refine ⟨8565449793373085062405783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11420599724497446749874377 8565449793373085062405783)
            ·
              refine ⟨12848174690059627593608675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565449793373085062405783 12848174690059627593608675)
              ·
                refine ⟨19272262035089441390413013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848174690059627593608675 19272262035089441390413013)
                ·
                  refine ⟨451693641447408782587805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19272262035089441390413013 451693641447408782587805)
                  ·
                    rfl

theorem cell22_3958516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3958516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958516 prefixEnd_3958516 := by exact prefixLift 3958516
  have htrace : WordTrace (prefixWord ++ tailWord_3958516) baseStart_3958516 baseEnd_3958516 := by
    simpa [prefixWord, tailWord_3958516, baseEnd_3958516] using wordTrace_append hprefix tailTrace_3958516
  have hstable : (prefixWord ++ tailWord_3958516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958516).length < 2 ^ (prefixWord ++ tailWord_3958516).sum := by decide
  have hdescent : baseEnd_3958516 < baseStart_3958516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958546 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3958546 : Nat := 118140960795 + 3958546 * 2 ^ 59
def prefixEnd_3958546 : Nat := 4983230072969 + 3 ^ 40 * 3958546 * 2
def baseEnd_3958546 : Nat := 1355091193955316269513323

theorem tailTrace_3958546 : CollatzResearch.WordTrace tailWord_3958546 prefixEnd_3958546 1355091193955316269513323 := by
  unfold tailWord_3958546
  simp only [CollatzResearch.WordTrace]
  refine ⟨36095008479217845669389873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96253355944580921785039661 36095008479217845669389873)
  ·
    refine ⟨27071256359413384252042405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36095008479217845669389873 27071256359413384252042405)
    ·
      refine ⟨5075860567390009547257951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27071256359413384252042405 5075860567390009547257951)
      ·
        refine ⟨7613790851085014320886927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075860567390009547257951 7613790851085014320886927)
        ·
          refine ⟨11420686276627521481330391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613790851085014320886927 11420686276627521481330391)
          ·
            refine ⟨17131029414941282221995587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420686276627521481330391 17131029414941282221995587)
            ·
              refine ⟨25696544122411923332993381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131029414941282221995587 25696544122411923332993381)
              ·
                refine ⟨4818102022952235624936259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25696544122411923332993381 4818102022952235624936259)
                ·
                  refine ⟨7227153034428353437404389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818102022952235624936259 7227153034428353437404389)
                  ·
                    refine ⟨1355091193955316269513323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7227153034428353437404389 1355091193955316269513323)
                    ·
                      rfl

theorem cell22_3958546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3958546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958546 prefixEnd_3958546 := by exact prefixLift 3958546
  have htrace : WordTrace (prefixWord ++ tailWord_3958546) baseStart_3958546 baseEnd_3958546 := by
    simpa [prefixWord, tailWord_3958546, baseEnd_3958546] using wordTrace_append hprefix tailTrace_3958546
  have hstable : (prefixWord ++ tailWord_3958546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958546).length < 2 ^ (prefixWord ++ tailWord_3958546).sum := by decide
  have hdescent : baseEnd_3958546 < baseStart_3958546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958555 : List Nat := [1, 1, 1, 1, 1, 1, 4, 12]
def baseStart_3958555 : Nat := 118140960795 + 3958555 * 2 ^ 59
def prefixEnd_3958555 : Nat := 4983230072969 + 3 ^ 40 * 3958555 * 2
def baseEnd_3958555 : Nat := 150566030537693694004255

theorem tailTrace_3958555 : CollatzResearch.WordTrace tailWord_3958555 prefixEnd_3958555 150566030537693694004255 := by
  unfold tailWord_3958555
  simp only [CollatzResearch.WordTrace]
  refine ⟨144380362173838777214637119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96253574782559184809758079 144380362173838777214637119)
  ·
    refine ⟨216570543260758165821955679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144380362173838777214637119 216570543260758165821955679)
    ·
      refine ⟨324855814891137248732933519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216570543260758165821955679 324855814891137248732933519)
      ·
        refine ⟨487283722336705873099400279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324855814891137248732933519 487283722336705873099400279)
        ·
          refine ⟨730925583505058809649100419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487283722336705873099400279 730925583505058809649100419)
          ·
            refine ⟨1096388375257588214473650629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730925583505058809649100419 1096388375257588214473650629)
            ·
              refine ⟨205572820360797790213809493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096388375257588214473650629 205572820360797790213809493)
              ·
                refine ⟨150566030537693694004255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 205572820360797790213809493 150566030537693694004255)
                ·
                  rfl

theorem cell22_3958555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_3958555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958555 prefixEnd_3958555 := by exact prefixLift 3958555
  have htrace : WordTrace (prefixWord ++ tailWord_3958555) baseStart_3958555 baseEnd_3958555 := by
    simpa [prefixWord, tailWord_3958555, baseEnd_3958555] using wordTrace_append hprefix tailTrace_3958555
  have hstable : (prefixWord ++ tailWord_3958555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958555).length < 2 ^ (prefixWord ++ tailWord_3958555).sum := by decide
  have hdescent : baseEnd_3958555 < baseStart_3958555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958561 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 4]
def baseStart_3958561 : Nat := 118140960795 + 3958561 * 2 ^ 59
def prefixEnd_3958561 : Nat := 4983230072969 + 3 ^ 40 * 3958561 * 2
def baseEnd_3958561 : Nat := 451698776253953743462759

theorem tailTrace_3958561 : CollatzResearch.WordTrace tailWord_3958561 prefixEnd_3958561 451698776253953743462759 := by
  unfold tailWord_3958561
  simp only [CollatzResearch.WordTrace]
  refine ⟨144380581011817040239355537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96253720674544693492903691 144380581011817040239355537)
  ·
    refine ⟨108285435758862780179516653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144380581011817040239355537 108285435758862780179516653)
    ·
      refine ⟨40607038409573542567318745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108285435758862780179516653 40607038409573542567318745)
      ·
        refine ⟨30455278807180156925489059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40607038409573542567318745 30455278807180156925489059)
        ·
          refine ⟨45682918210770235388233589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30455278807180156925489059 45682918210770235388233589)
          ·
            refine ⟨4282773582259709567646899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45682918210770235388233589 4282773582259709567646899)
            ·
              refine ⟨6424160373389564351470349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282773582259709567646899 6424160373389564351470349)
              ·
                refine ⟨2409060140021086631801381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6424160373389564351470349 2409060140021086631801381)
                ·
                  refine ⟨451698776253953743462759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409060140021086631801381 451698776253953743462759)
                  ·
                    rfl

theorem cell22_3958561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_3958561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958561 prefixEnd_3958561 := by exact prefixLift 3958561
  have htrace : WordTrace (prefixWord ++ tailWord_3958561) baseStart_3958561 baseEnd_3958561 := by
    simpa [prefixWord, tailWord_3958561, baseEnd_3958561] using wordTrace_append hprefix tailTrace_3958561
  have hstable : (prefixWord ++ tailWord_3958561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958561).length < 2 ^ (prefixWord ++ tailWord_3958561).sum := by decide
  have hdescent : baseEnd_3958561 < baseStart_3958561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958572 : List Nat := [2, 2, 1, 1, 1, 7, 8]
def baseStart_3958572 : Nat := 118140960795 + 3958572 * 2 ^ 59
def prefixEnd_3958572 : Nat := 4983230072969 + 3 ^ 40 * 3958572 * 2
def baseEnd_3958572 : Nat := 50188892380987439569009

theorem tailTrace_3958572 : CollatzResearch.WordTrace tailWord_3958572 prefixEnd_3958572 50188892380987439569009 := by
  unfold tailWord_3958572
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190491107388594559002985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96253988143184792745337313 72190491107388594559002985)
  ·
    refine ⟨54142868330541445919252239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72190491107388594559002985 54142868330541445919252239)
    ·
      refine ⟨81214302495812168878878359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54142868330541445919252239 81214302495812168878878359)
      ·
        refine ⟨121821453743718253318317539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81214302495812168878878359 121821453743718253318317539)
        ·
          refine ⟨182732180615577379977476309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121821453743718253318317539 182732180615577379977476309)
          ·
            refine ⟨4282785483177594843222101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 182732180615577379977476309 4282785483177594843222101)
            ·
              refine ⟨50188892380987439569009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4282785483177594843222101 50188892380987439569009)
              ·
                rfl

theorem cell22_3958572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 8].length) (baseStart_3958572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958572 prefixEnd_3958572 := by exact prefixLift 3958572
  have htrace : WordTrace (prefixWord ++ tailWord_3958572) baseStart_3958572 baseEnd_3958572 := by
    simpa [prefixWord, tailWord_3958572, baseEnd_3958572] using wordTrace_append hprefix tailTrace_3958572
  have hstable : (prefixWord ++ tailWord_3958572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958572).length < 2 ^ (prefixWord ++ tailWord_3958572).sum := by decide
  have hdescent : baseEnd_3958572 < baseStart_3958572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958589 : List Nat := [1, 4, 1, 4, 1, 2, 2, 7]
def baseStart_3958589 : Nat := 118140960795 + 3958589 * 2 ^ 59
def prefixEnd_3958589 : Nat := 4983230072969 + 3 ^ 40 * 3958589 * 2
def baseEnd_3958589 : Nat := 150567323748230943409799

theorem tailTrace_3958589 : CollatzResearch.WordTrace tailWord_3958589 prefixEnd_3958589 150567323748230943409799 := by
  unfold tailWord_3958589
  simp only [CollatzResearch.WordTrace]
  refine ⟨144381602255715601021374821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96254401503810400680916547 144381602255715601021374821)
  ·
    refine ⟨27071550422946675191507779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144381602255715601021374821 27071550422946675191507779)
    ·
      refine ⟨40607325634420012787261669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27071550422946675191507779 40607325634420012787261669)
      ·
        refine ⟨7613873556453752397611563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40607325634420012787261669 7613873556453752397611563)
        ·
          refine ⟨11420810334680628596417345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613873556453752397611563 11420810334680628596417345)
          ·
            refine ⟨8565607751010471447313009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11420810334680628596417345 8565607751010471447313009)
            ·
              refine ⟨6424205813257853585484757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8565607751010471447313009 6424205813257853585484757)
              ·
                refine ⟨150567323748230943409799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6424205813257853585484757 150567323748230943409799)
                ·
                  rfl

theorem cell22_3958589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 7].length) (baseStart_3958589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958589 prefixEnd_3958589 := by exact prefixLift 3958589
  have htrace : WordTrace (prefixWord ++ tailWord_3958589) baseStart_3958589 baseEnd_3958589 := by
    simpa [prefixWord, tailWord_3958589, baseEnd_3958589] using wordTrace_append hprefix tailTrace_3958589
  have hstable : (prefixWord ++ tailWord_3958589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958589).length < 2 ^ (prefixWord ++ tailWord_3958589).sum := by decide
  have hdescent : baseEnd_3958589 < baseStart_3958589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958681 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_3958681 : Nat := 118140960795 + 3958681 * 2 ^ 59
def prefixEnd_3958681 : Nat := 4983230072969 + 3 ^ 40 * 3958681 * 2
def baseEnd_3958681 : Nat := 1355137407214220917387909

theorem tailTrace_3958681 : CollatzResearch.WordTrace tailWord_3958681 prefixEnd_3958681 1355137407214220917387909 := by
  unfold tailWord_3958681
  simp only [CollatzResearch.WordTrace]
  refine ⟨144384957771382300733723897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96256638514254867155815931 144384957771382300733723897)
  ·
    refine ⟨108288718328536725550292923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144384957771382300733723897 108288718328536725550292923)
    ·
      refine ⟨162433077492805088325439385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108288718328536725550292923 162433077492805088325439385)
      ·
        refine ⟨121824808119603816244079539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162433077492805088325439385 121824808119603816244079539)
        ·
          refine ⟨182737212179405724366119309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121824808119603816244079539 182737212179405724366119309)
          ·
            refine ⟨68526454567277146637294741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182737212179405724366119309 68526454567277146637294741)
            ·
              refine ⟨3212177557841116248623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68526454567277146637294741 3212177557841116248623191)
              ·
                refine ⟨4818266336761674372934787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212177557841116248623191 4818266336761674372934787)
                ·
                  refine ⟨7227399505142511559402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818266336761674372934787 7227399505142511559402181)
                  ·
                    refine ⟨1355137407214220917387909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7227399505142511559402181 1355137407214220917387909)
                    ·
                      rfl

theorem cell22_3958681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_3958681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958681 prefixEnd_3958681 := by exact prefixLift 3958681
  have htrace : WordTrace (prefixWord ++ tailWord_3958681) baseStart_3958681 baseEnd_3958681 := by
    simpa [prefixWord, tailWord_3958681, baseEnd_3958681] using wordTrace_append hprefix tailTrace_3958681
  have hstable : (prefixWord ++ tailWord_3958681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958681).length < 2 ^ (prefixWord ++ tailWord_3958681).sum := by decide
  have hdescent : baseEnd_3958681 < baseStart_3958681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958702 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3958702 : Nat := 118140960795 + 3958702 * 2 ^ 59
def prefixEnd_3958702 : Nat := 4983230072969 + 3 ^ 40 * 3958702 * 2
def baseEnd_3958702 : Nat := 451714865314461287537615

theorem tailTrace_3958702 : CollatzResearch.WordTrace tailWord_3958702 prefixEnd_3958702 451714865314461287537615 := by
  unfold tailWord_3958702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048215463038277665029795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96257149136204147546825573 18048215463038277665029795)
  ·
    refine ⟨27072323194557416497544693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048215463038277665029795 27072323194557416497544693)
    ·
      refine ⟨2538030299489757796644815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27072323194557416497544693 2538030299489757796644815)
      ·
        refine ⟨3807045449234636694967223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538030299489757796644815 3807045449234636694967223)
        ·
          refine ⟨5710568173851955042450835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807045449234636694967223 5710568173851955042450835)
          ·
            refine ⟨8565852260777932563676253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5710568173851955042450835 8565852260777932563676253)
            ·
              refine ⟨3212194597791724711378595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8565852260777932563676253 3212194597791724711378595)
              ·
                refine ⟨4818291896687587067067893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212194597791724711378595 4818291896687587067067893)
                ·
                  refine ⟨451714865314461287537615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4818291896687587067067893 451714865314461287537615)
                  ·
                    rfl

theorem cell22_3958702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3958702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958702 prefixEnd_3958702 := by exact prefixLift 3958702
  have htrace : WordTrace (prefixWord ++ tailWord_3958702) baseStart_3958702 baseEnd_3958702 := by
    simpa [prefixWord, tailWord_3958702, baseEnd_3958702] using wordTrace_append hprefix tailTrace_3958702
  have hstable : (prefixWord ++ tailWord_3958702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958702).length < 2 ^ (prefixWord ++ tailWord_3958702).sum := by decide
  have hdescent : baseEnd_3958702 < baseStart_3958702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3958707 : List Nat := [1, 1, 1, 2, 3, 1, 4, 9]
def baseStart_3958707 : Nat := 118140960795 + 3958707 * 2 ^ 59
def prefixEnd_3958707 : Nat := 4983230072969 + 3 ^ 40 * 3958707 * 2
def baseEnd_3958707 : Nat := 150571811949507279581981

theorem tailTrace_3958707 : CollatzResearch.WordTrace tailWord_3958707 prefixEnd_3958707 150571811949507279581981 := by
  unfold tailWord_3958707
  simp only [CollatzResearch.WordTrace]
  refine ⟨144385906069288107174170375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96257270712858738116113583 144385906069288107174170375)
  ·
    refine ⟨216578859103932160761255563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144385906069288107174170375 216578859103932160761255563)
    ·
      refine ⟨324868288655898241141883345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216578859103932160761255563 324868288655898241141883345)
      ·
        refine ⟨243651216491923680856412509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324868288655898241141883345 243651216491923680856412509)
        ·
          refine ⟨91369206184471380321154691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243651216491923680856412509 91369206184471380321154691)
          ·
            refine ⟨137053809276707070481732037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91369206184471380321154691 137053809276707070481732037)
            ·
              refine ⟨25697589239382575715324757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137053809276707070481732037 25697589239382575715324757)
              ·
                refine ⟨150571811949507279581981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25697589239382575715324757 150571811949507279581981)
                ·
                  rfl

theorem cell22_3958707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_3958707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3958707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3958707 prefixEnd_3958707 := by exact prefixLift 3958707
  have htrace : WordTrace (prefixWord ++ tailWord_3958707) baseStart_3958707 baseEnd_3958707 := by
    simpa [prefixWord, tailWord_3958707, baseEnd_3958707] using wordTrace_append hprefix tailTrace_3958707
  have hstable : (prefixWord ++ tailWord_3958707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3958707).length < 2 ^ (prefixWord ++ tailWord_3958707).sum := by decide
  have hdescent : baseEnd_3958707 < baseStart_3958707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3958707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
