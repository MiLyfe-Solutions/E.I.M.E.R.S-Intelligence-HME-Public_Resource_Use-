import V185TrunkScan23Chunk1102

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6531218 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 7]
def baseStart_6531218 : Nat := 118140960795 + 6531218 * 2 ^ 59
def prefixEnd_6531218 : Nat := 4983230072969 + 3 ^ 40 * 6531218 * 2
def baseEnd_6531218 : Nat := 372628232588525868137609

theorem tailTrace_6531218 : CollatzResearch.WordTrace tailWord_6531218 prefixEnd_6531218 372628232588525868137609 := by
  unfold tailWord_6531218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59553272613130026018634577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158808726968346736049692205 59553272613130026018634577)
  ·
    refine ⟨44664954459847519513975933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59553272613130026018634577 44664954459847519513975933)
    ·
      refine ⟨16749357922442819817740975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44664954459847519513975933 16749357922442819817740975)
      ·
        refine ⟨25124036883664229726611463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749357922442819817740975 25124036883664229726611463)
        ·
          refine ⟨37686055325496344589917195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25124036883664229726611463 37686055325496344589917195)
          ·
            refine ⟨56529082988244516884875793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37686055325496344589917195 56529082988244516884875793)
            ·
              refine ⟨42396812241183387663656845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56529082988244516884875793 42396812241183387663656845)
              ·
                refine ⟨15898804590443770373871317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42396812241183387663656845 15898804590443770373871317)
                ·
                  refine ⟨372628232588525868137609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15898804590443770373871317 372628232588525868137609)
                  ·
                    rfl

theorem cell23_6531218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_6531218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531218 prefixEnd_6531218 := by exact prefixLift 6531218
  have htrace : WordTrace (prefixWord ++ tailWord_6531218) baseStart_6531218 baseEnd_6531218 := by
    simpa [prefixWord, tailWord_6531218, baseEnd_6531218] using wordTrace_append hprefix tailTrace_6531218
  have hstable : (prefixWord ++ tailWord_6531218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531218).length < 2 ^ (prefixWord ++ tailWord_6531218).sum := by decide
  have hdescent : baseEnd_6531218 < baseStart_6531218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531291 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 10]
def baseStart_6531291 : Nat := 118140960795 + 6531291 * 2 ^ 59
def prefixEnd_6531291 : Nat := 4983230072969 + 3 ^ 40 * 6531291 * 2
def baseEnd_6531291 : Nat := 372632397487167891958405

theorem tailTrace_6531291 : CollatzResearch.WordTrace tailWord_6531291 prefixEnd_6531291 372632397487167891958405 := by
  unfold tailWord_6531291
  simp only [CollatzResearch.WordTrace]
  refine ⟨238215752981255637541945727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158810501987503758361297151 238215752981255637541945727)
  ·
    refine ⟨357323629471883456312918591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238215752981255637541945727 357323629471883456312918591)
    ·
      refine ⟨535985444207825184469377887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357323629471883456312918591 535985444207825184469377887)
      ·
        refine ⟨803978166311737776704066831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535985444207825184469377887 803978166311737776704066831)
        ·
          refine ⟨1205967249467606665056100247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803978166311737776704066831 1205967249467606665056100247)
          ·
            refine ⟨1808950874201409997584150371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205967249467606665056100247 1808950874201409997584150371)
            ·
              refine ⟨2713426311302114996376225557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808950874201409997584150371 2713426311302114996376225557)
              ·
                refine ⟨127191858342286640455135573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2713426311302114996376225557 127191858342286640455135573)
                ·
                  refine ⟨372632397487167891958405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127191858342286640455135573 372632397487167891958405)
                  ·
                    rfl

theorem cell23_6531291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_6531291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531291 prefixEnd_6531291 := by exact prefixLift 6531291
  have htrace : WordTrace (prefixWord ++ tailWord_6531291) baseStart_6531291 baseEnd_6531291 := by
    simpa [prefixWord, tailWord_6531291, baseEnd_6531291] using wordTrace_append hprefix tailTrace_6531291
  have hstable : (prefixWord ++ tailWord_6531291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531291).length < 2 ^ (prefixWord ++ tailWord_6531291).sum := by decide
  have hdescent : baseEnd_6531291 < baseStart_6531291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531329 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 1, 4]
def baseStart_6531329 : Nat := 118140960795 + 6531329 * 2 ^ 59
def prefixEnd_6531329 : Nat := 4983230072969 + 3 ^ 40 * 6531329 * 2
def baseEnd_6531329 : Nat := 1117903696549793959650157

theorem tailTrace_6531329 : CollatzResearch.WordTrace tailWord_6531329 prefixEnd_6531329 1117903696549793959650157 := by
  unfold tailWord_6531329
  simp only [CollatzResearch.WordTrace]
  refine ⟨238217138955117970031829041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158811425970078646687886027 238217138955117970031829041)
  ·
    refine ⟨178662854216338477523871781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238217138955117970031829041 178662854216338477523871781)
    ·
      refine ⟨33499285165563464535725959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178662854216338477523871781 33499285165563464535725959)
      ·
        refine ⟨50248927748345196803588939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33499285165563464535725959 50248927748345196803588939)
        ·
          refine ⟨75373391622517795205383409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50248927748345196803588939 75373391622517795205383409)
          ·
            refine ⟨56530043716888346404037557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75373391622517795205383409 56530043716888346404037557)
            ·
              refine ⟨5299691598458282475378521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56530043716888346404037557 5299691598458282475378521)
              ·
                refine ⟨3974768698843711856533891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299691598458282475378521 3974768698843711856533891)
                ·
                  refine ⟨5962153048265567784800837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974768698843711856533891 5962153048265567784800837)
                  ·
                    refine ⟨1117903696549793959650157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962153048265567784800837 1117903696549793959650157)
                    ·
                      rfl

theorem cell23_6531329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_6531329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531329 prefixEnd_6531329 := by exact prefixLift 6531329
  have htrace : WordTrace (prefixWord ++ tailWord_6531329) baseStart_6531329 baseEnd_6531329 := by
    simpa [prefixWord, tailWord_6531329, baseEnd_6531329] using wordTrace_append hprefix tailTrace_6531329
  have hstable : (prefixWord ++ tailWord_6531329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531329).length < 2 ^ (prefixWord ++ tailWord_6531329).sum := by decide
  have hdescent : baseEnd_6531329 < baseStart_6531329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531355 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 1, 5]
def baseStart_6531355 : Nat := 118140960795 + 6531355 * 2 ^ 59
def prefixEnd_6531355 : Nat := 4983230072969 + 3 ^ 40 * 6531355 * 2
def baseEnd_6531355 : Nat := 1117908146715466259075117

theorem tailTrace_6531355 : CollatzResearch.WordTrace tailWord_6531355 prefixEnd_6531355 1117908146715466259075117 := by
  unfold tailWord_6531355
  simp only [CollatzResearch.WordTrace]
  refine ⟨238218087253023776472275519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158812058168682517648183679 238218087253023776472275519)
  ·
    refine ⟨357327130879535664708413279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238218087253023776472275519 357327130879535664708413279)
    ·
      refine ⟨535990696319303497062619919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357327130879535664708413279 535990696319303497062619919)
      ·
        refine ⟨803986044478955245593929879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535990696319303497062619919 803986044478955245593929879)
        ·
          refine ⟨1205979066718432868390894819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803986044478955245593929879 1205979066718432868390894819)
          ·
            refine ⟨1808968600077649302586342229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205979066718432868390894819 1808968600077649302586342229)
            ·
              refine ⟨10599425391079976382341849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1808968600077649302586342229 10599425391079976382341849)
              ·
                refine ⟨7949569043309982286756387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599425391079976382341849 7949569043309982286756387)
                ·
                  refine ⟨11924353564964973430134581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949569043309982286756387 11924353564964973430134581)
                  ·
                    refine ⟨1117908146715466259075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11924353564964973430134581 1117908146715466259075117)
                    ·
                      rfl

theorem cell23_6531355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 5].length) (baseStart_6531355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531355 prefixEnd_6531355 := by exact prefixLift 6531355
  have htrace : WordTrace (prefixWord ++ tailWord_6531355) baseStart_6531355 baseEnd_6531355 := by
    simpa [prefixWord, tailWord_6531355, baseEnd_6531355] using wordTrace_append hprefix tailTrace_6531355
  have hstable : (prefixWord ++ tailWord_6531355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531355).length < 2 ^ (prefixWord ++ tailWord_6531355).sum := by decide
  have hdescent : baseEnd_6531355 < baseStart_6531355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531375 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 4]
def baseStart_6531375 : Nat := 118140960795 + 6531375 * 2 ^ 59
def prefixEnd_6531375 : Nat := 4983230072969 + 3 ^ 40 * 6531375 * 2
def baseEnd_6531375 : Nat := 3353734709759488698975259

theorem tailTrace_6531375 : CollatzResearch.WordTrace tailWord_6531375 prefixEnd_6531375 3353734709759488698975259 := by
  unfold tailWord_6531375
  simp only [CollatzResearch.WordTrace]
  refine ⟨238218816712951319888003579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158812544475300879925335719 238218816712951319888003579)
  ·
    refine ⟨357328225069426979832005369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238218816712951319888003579 357328225069426979832005369)
    ·
      refine ⟨267996168802070234874004027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357328225069426979832005369 267996168802070234874004027)
      ·
        refine ⟨401994253203105352311006041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267996168802070234874004027 401994253203105352311006041)
        ·
          refine ⟨301495689902329014233254531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401994253203105352311006041 301495689902329014233254531)
          ·
            refine ⟨452243534853493521349881797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301495689902329014233254531 452243534853493521349881797)
            ·
              refine ⟨84795662785030035253102837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452243534853493521349881797 84795662785030035253102837)
              ·
                refine ⟨7949593386096565804978391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84795662785030035253102837 7949593386096565804978391)
                ·
                  refine ⟨11924390079144848707467587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949593386096565804978391 11924390079144848707467587)
                  ·
                    refine ⟨17886585118717273061201381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11924390079144848707467587 17886585118717273061201381)
                    ·
                      refine ⟨3353734709759488698975259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17886585118717273061201381 3353734709759488698975259)
                      ·
                        rfl

theorem cell23_6531375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_6531375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531375 prefixEnd_6531375 := by exact prefixLift 6531375
  have htrace : WordTrace (prefixWord ++ tailWord_6531375) baseStart_6531375 baseEnd_6531375 := by
    simpa [prefixWord, tailWord_6531375, baseEnd_6531375] using wordTrace_append hprefix tailTrace_6531375
  have hstable : (prefixWord ++ tailWord_6531375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531375).length < 2 ^ (prefixWord ++ tailWord_6531375).sum := by decide
  have hdescent : baseEnd_6531375 < baseStart_6531375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531386 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3]
def baseStart_6531386 : Nat := 118140960795 + 6531386 * 2 ^ 59
def prefixEnd_6531386 : Nat := 4983230072969 + 3 ^ 40 * 6531386 * 2
def baseEnd_6531386 : Nat := 3353740358046688155937709

theorem tailTrace_6531386 : CollatzResearch.WordTrace tailWord_6531386 prefixEnd_6531386 3353740358046688155937709 := by
  unfold tailWord_6531386
  simp only [CollatzResearch.WordTrace]
  refine ⟨59554804478977867191663503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158812811943940979177769341 59554804478977867191663503)
  ·
    refine ⟨89332206718466800787495255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59554804478977867191663503 89332206718466800787495255)
    ·
      refine ⟨133998310077700201181242883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89332206718466800787495255 133998310077700201181242883)
      ·
        refine ⟨200997465116550301771864325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133998310077700201181242883 200997465116550301771864325)
        ·
          refine ⟨37687024709353181582224561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200997465116550301771864325 37687024709353181582224561)
          ·
            refine ⟨28265268532014886186668421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37687024709353181582224561 28265268532014886186668421)
            ·
              refine ⟨5299737849752791160000329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28265268532014886186668421 5299737849752791160000329)
              ·
                refine ⟨3974803387314593370000247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299737849752791160000329 3974803387314593370000247)
                ·
                  refine ⟨5962205080971890055000371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974803387314593370000247 5962205080971890055000371)
                  ·
                    refine ⟨8943307621457835082500557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962205080971890055000371 8943307621457835082500557)
                    ·
                      refine ⟨3353740358046688155937709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943307621457835082500557 3353740358046688155937709)
                      ·
                        rfl

theorem cell23_6531386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_6531386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531386 prefixEnd_6531386 := by exact prefixLift 6531386
  have htrace : WordTrace (prefixWord ++ tailWord_6531386) baseStart_6531386 baseEnd_6531386 := by
    simpa [prefixWord, tailWord_6531386, baseEnd_6531386] using wordTrace_append hprefix tailTrace_6531386
  have hstable : (prefixWord ++ tailWord_6531386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531386).length < 2 ^ (prefixWord ++ tailWord_6531386).sum := by decide
  have hdescent : baseEnd_6531386 < baseStart_6531386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531395 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3]
def baseStart_6531395 : Nat := 118140960795 + 6531395 * 2 ^ 59
def prefixEnd_6531395 : Nat := 4983230072969 + 3 ^ 40 * 6531395 * 2
def baseEnd_6531395 : Nat := 3353744979372578620725167

theorem tailTrace_6531395 : CollatzResearch.WordTrace tailWord_6531395 prefixEnd_6531395 3353744979372578620725167 := by
  unfold tailWord_6531395
  simp only [CollatzResearch.WordTrace]
  refine ⟨238219546172878863303731639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158813030781919242202487759 238219546172878863303731639)
  ·
    refine ⟨357329319259318294955597459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238219546172878863303731639 357329319259318294955597459)
    ·
      refine ⟨535993978888977442433396189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357329319259318294955597459 535993978888977442433396189)
      ·
        refine ⟨200997742083366540912523571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535993978888977442433396189 200997742083366540912523571)
        ·
          refine ⟨301496613125049811368785357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200997742083366540912523571 301496613125049811368785357)
          ·
            refine ⟨113061229921893679263294509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301496613125049811368785357 113061229921893679263294509)
            ·
              refine ⟨42397961220710129723735441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113061229921893679263294509 42397961220710129723735441)
              ·
                refine ⟨31798470915532597292801581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42397961220710129723735441 31798470915532597292801581)
                ·
                  refine ⟨11924426593324723984800593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31798470915532597292801581 11924426593324723984800593)
                  ·
                    refine ⟨8943319944993542988600445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924426593324723984800593 8943319944993542988600445)
                    ·
                      refine ⟨3353744979372578620725167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943319944993542988600445 3353744979372578620725167)
                      ·
                        rfl

theorem cell23_6531395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_6531395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531395 prefixEnd_6531395 := by exact prefixLift 6531395
  have htrace : WordTrace (prefixWord ++ tailWord_6531395) baseStart_6531395 baseEnd_6531395 := by
    simpa [prefixWord, tailWord_6531395, baseEnd_6531395] using wordTrace_append hprefix tailTrace_6531395
  have hstable : (prefixWord ++ tailWord_6531395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531395).length < 2 ^ (prefixWord ++ tailWord_6531395).sum := by decide
  have hdescent : baseEnd_6531395 < baseStart_6531395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531409 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_6531409 : Nat := 118140960795 + 6531409 * 2 ^ 59
def prefixEnd_6531409 : Nat := 4983230072969 + 3 ^ 40 * 6531409 * 2
def baseEnd_6531409 : Nat := 3353752168101741565950103

theorem tailTrace_6531409 : CollatzResearch.WordTrace tailWord_6531409 prefixEnd_6531409 3353752168101741565950103 := by
  unfold tailWord_6531409
  simp only [CollatzResearch.WordTrace]
  refine ⟨238220056794828143694741281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158813371196552095796494187 238220056794828143694741281)
  ·
    refine ⟨178665042596121107771055961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238220056794828143694741281 178665042596121107771055961)
    ·
      refine ⟨133998781947090830828291971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178665042596121107771055961 133998781947090830828291971)
      ·
        refine ⟨200998172920636246242437957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133998781947090830828291971 200998172920636246242437957)
        ·
          refine ⟨37687157422619296170457117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200998172920636246242437957 37687157422619296170457117)
          ·
            refine ⟨14132684033482236063921419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37687157422619296170457117 14132684033482236063921419)
            ·
              refine ⟨21199026050223354095882129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14132684033482236063921419 21199026050223354095882129)
              ·
                refine ⟨15899269537667515571911597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21199026050223354095882129 15899269537667515571911597)
                ·
                  refine ⟨5962226076625318339466849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15899269537667515571911597 5962226076625318339466849)
                  ·
                    refine ⟨4471669557468988754600137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5962226076625318339466849 4471669557468988754600137)
                    ·
                      refine ⟨3353752168101741565950103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471669557468988754600137 3353752168101741565950103)
                      ·
                        rfl

theorem cell23_6531409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_6531409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531409 prefixEnd_6531409 := by exact prefixLift 6531409
  have htrace : WordTrace (prefixWord ++ tailWord_6531409) baseStart_6531409 baseEnd_6531409 := by
    simpa [prefixWord, tailWord_6531409, baseEnd_6531409] using wordTrace_append hprefix tailTrace_6531409
  have hstable : (prefixWord ++ tailWord_6531409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531409).length < 2 ^ (prefixWord ++ tailWord_6531409).sum := by decide
  have hdescent : baseEnd_6531409 < baseStart_6531409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531412 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_6531412 : Nat := 118140960795 + 6531412 * 2 ^ 59
def prefixEnd_6531412 : Nat := 4983230072969 + 3 ^ 40 * 6531412 * 2
def baseEnd_6531412 : Nat := 3353753708543705054212589

theorem tailTrace_6531412 : CollatzResearch.WordTrace tailWord_6531412 prefixEnd_6531412 3353753708543705054212589 := by
  unfold tailWord_6531412
  simp only [CollatzResearch.WordTrace]
  refine ⟨119110083106908637603550245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158813444142544850138066993 119110083106908637603550245)
  ·
    refine ⟨22333140582545369550665671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119110083106908637603550245 22333140582545369550665671)
    ·
      refine ⟨33499710873818054325998507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22333140582545369550665671 33499710873818054325998507)
      ·
        refine ⟨50249566310727081488997761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33499710873818054325998507 50249566310727081488997761)
        ·
          refine ⟨37687174733045311116748321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50249566310727081488997761 37687174733045311116748321)
          ·
            refine ⟨28265381049783983337561241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37687174733045311116748321 28265381049783983337561241)
            ·
              refine ⟨21199035787337987503170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28265381049783983337561241 21199035787337987503170931)
              ·
                refine ⟨31798553681006981254756397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199035787337987503170931 31798553681006981254756397)
                ·
                  refine ⟨11924457630377617970533649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31798553681006981254756397 11924457630377617970533649)
                  ·
                    refine ⟨8943343222783213477900237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924457630377617970533649 8943343222783213477900237)
                    ·
                      refine ⟨3353753708543705054212589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943343222783213477900237 3353753708543705054212589)
                      ·
                        rfl

theorem cell23_6531412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_6531412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531412 prefixEnd_6531412 := by exact prefixLift 6531412
  have htrace : WordTrace (prefixWord ++ tailWord_6531412) baseStart_6531412 baseEnd_6531412 := by
    simpa [prefixWord, tailWord_6531412, baseEnd_6531412] using wordTrace_append hprefix tailTrace_6531412
  have hstable : (prefixWord ++ tailWord_6531412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531412).length < 2 ^ (prefixWord ++ tailWord_6531412).sum := by decide
  have hdescent : baseEnd_6531412 < baseStart_6531412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531415 : List Nat := [1, 1, 3, 2, 3, 1, 5, 7]
def baseStart_6531415 : Nat := 118140960795 + 6531415 * 2 ^ 59
def prefixEnd_6531415 : Nat := 4983230072969 + 3 ^ 40 * 6531415 * 2
def baseEnd_6531415 : Nat := 124213157369839575647225

theorem tailTrace_6531415 : CollatzResearch.WordTrace tailWord_6531415 prefixEnd_6531415 124213157369839575647225 := by
  unfold tailWord_6531415
  simp only [CollatzResearch.WordTrace]
  refine ⟨238220275632806406719459699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158813517088537604479639799 238220275632806406719459699)
  ·
    refine ⟨357330413449209610079189549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238220275632806406719459699 357330413449209610079189549)
    ·
      refine ⟨133998905043453603779696081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357330413449209610079189549 133998905043453603779696081)
      ·
        refine ⟨100499178782590202834772061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133998905043453603779696081 100499178782590202834772061)
        ·
          refine ⟨37687192043471326063039523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100499178782590202834772061 37687192043471326063039523)
          ·
            refine ⟨56530788065206989094559285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37687192043471326063039523 56530788065206989094559285)
            ·
              refine ⟨5299761381113155227614933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56530788065206989094559285 5299761381113155227614933)
              ·
                refine ⟨124213157369839575647225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5299761381113155227614933 124213157369839575647225)
                ·
                  rfl

theorem cell23_6531415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 7].length) (baseStart_6531415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531415 prefixEnd_6531415 := by exact prefixLift 6531415
  have htrace : WordTrace (prefixWord ++ tailWord_6531415) baseStart_6531415 baseEnd_6531415 := by
    simpa [prefixWord, tailWord_6531415, baseEnd_6531415] using wordTrace_append hprefix tailTrace_6531415
  have hstable : (prefixWord ++ tailWord_6531415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531415).length < 2 ^ (prefixWord ++ tailWord_6531415).sum := by decide
  have hdescent : baseEnd_6531415 < baseStart_6531415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531426 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6531426 : Nat := 118140960795 + 6531426 * 2 ^ 59
def prefixEnd_6531426 : Nat := 4983230072969 + 3 ^ 40 * 6531426 * 2
def baseEnd_6531426 : Nat := 3353760897272867999437525

theorem tailTrace_6531426 : CollatzResearch.WordTrace tailWord_6531426 prefixEnd_6531426 3353760897272867999437525 := by
  unfold tailWord_6531426
  simp only [CollatzResearch.WordTrace]
  refine ⟨59555169208941638899527533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158813784557177703732073421 59555169208941638899527533)
  ·
    refine ⟨22333188453353114587322825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59555169208941638899527533 22333188453353114587322825)
    ·
      refine ⟨16749891340014835940492119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22333188453353114587322825 16749891340014835940492119)
      ·
        refine ⟨25124837010022253910738179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749891340014835940492119 25124837010022253910738179)
        ·
          refine ⟨37687255515033380866107269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25124837010022253910738179 37687255515033380866107269)
          ·
            refine ⟨7066360409068758912395113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37687255515033380866107269 7066360409068758912395113)
            ·
              refine ⟨5299770306801569184296335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066360409068758912395113 5299770306801569184296335)
              ·
                refine ⟨7949655460202353776444503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299770306801569184296335 7949655460202353776444503)
                ·
                  refine ⟨11924483190303530664666755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949655460202353776444503 11924483190303530664666755)
                  ·
                    refine ⟨17886724785455295997000133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11924483190303530664666755 17886724785455295997000133)
                    ·
                      refine ⟨3353760897272867999437525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17886724785455295997000133 3353760897272867999437525)
                      ·
                        rfl

theorem cell23_6531426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6531426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531426 prefixEnd_6531426 := by exact prefixLift 6531426
  have htrace : WordTrace (prefixWord ++ tailWord_6531426) baseStart_6531426 baseEnd_6531426 := by
    simpa [prefixWord, tailWord_6531426, baseEnd_6531426] using wordTrace_append hprefix tailTrace_6531426
  have hstable : (prefixWord ++ tailWord_6531426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531426).length < 2 ^ (prefixWord ++ tailWord_6531426).sum := by decide
  have hdescent : baseEnd_6531426 < baseStart_6531426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531429 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_6531429 : Nat := 118140960795 + 6531429 * 2 ^ 59
def prefixEnd_6531429 : Nat := 4983230072969 + 3 ^ 40 * 6531429 * 2
def baseEnd_6531429 : Nat := 3353762437714831487700011

theorem tailTrace_6531429 : CollatzResearch.WordTrace tailWord_6531429 prefixEnd_6531429 3353762437714831487700011 := by
  unfold tailWord_6531429
  simp only [CollatzResearch.WordTrace]
  refine ⟨238220786254755687110469341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158813857503170458073646227 238220786254755687110469341)
  ·
    refine ⟨89332794845533382666426003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238220786254755687110469341 89332794845533382666426003)
    ·
      refine ⟨133999192268300073999639005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89332794845533382666426003 133999192268300073999639005)
      ·
        refine ⟨50249697100612527749864627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133999192268300073999639005 50249697100612527749864627)
        ·
          refine ⟨75374545650918791624796941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50249697100612527749864627 75374545650918791624796941)
          ·
            refine ⟨28265454619094546859298853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75374545650918791624796941 28265454619094546859298853)
            ·
              refine ⟨5299772741080227536118535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28265454619094546859298853 5299772741080227536118535)
              ·
                refine ⟨7949659111620341304177803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299772741080227536118535 7949659111620341304177803)
                ·
                  refine ⟨11924488667430511956266705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949659111620341304177803 11924488667430511956266705)
                  ·
                    refine ⟨8943366500572883967200029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924488667430511956266705 8943366500572883967200029)
                    ·
                      refine ⟨3353762437714831487700011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943366500572883967200029 3353762437714831487700011)
                      ·
                        rfl

theorem cell23_6531429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_6531429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531429 prefixEnd_6531429 := by exact prefixLift 6531429
  have htrace : WordTrace (prefixWord ++ tailWord_6531429) baseStart_6531429 baseEnd_6531429 := by
    simpa [prefixWord, tailWord_6531429, baseEnd_6531429] using wordTrace_append hprefix tailTrace_6531429
  have hstable : (prefixWord ++ tailWord_6531429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531429).length < 2 ^ (prefixWord ++ tailWord_6531429).sum := by decide
  have hdescent : baseEnd_6531429 < baseStart_6531429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531436 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_6531436 : Nat := 118140960795 + 6531436 * 2 ^ 59
def prefixEnd_6531436 : Nat := 4983230072969 + 3 ^ 40 * 6531436 * 2
def baseEnd_6531436 : Nat := 1117922010693137653437493

theorem tailTrace_6531436 : CollatzResearch.WordTrace tailWord_6531436 prefixEnd_6531436 1117922010693137653437493 := by
  unfold tailWord_6531436
  simp only [CollatzResearch.WordTrace]
  refine ⟨119110520782865163652987081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158814027710486884870649441 119110520782865163652987081)
  ·
    refine ⟨89332890587148872739740311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119110520782865163652987081 89332890587148872739740311)
    ·
      refine ⟨133999335880723309109610467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89332890587148872739740311 133999335880723309109610467)
      ·
        refine ⟨200999003821084963664415701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133999335880723309109610467 200999003821084963664415701)
        ·
          refine ⟨4710914152056678835884743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 200999003821084963664415701 4710914152056678835884743)
          ·
            refine ⟨7066371228085018253827115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710914152056678835884743 7066371228085018253827115)
            ·
              refine ⟨10599556842127527380740673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066371228085018253827115 10599556842127527380740673)
              ·
                refine ⟨7949667631595645535555505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599556842127527380740673 7949667631595645535555505)
                ·
                  refine ⟨5962250723696734151666629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949667631595645535555505 5962250723696734151666629)
                  ·
                    refine ⟨1117922010693137653437493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962250723696734151666629 1117922010693137653437493)
                    ·
                      rfl

theorem cell23_6531436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_6531436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531436 prefixEnd_6531436 := by exact prefixLift 6531436
  have htrace : WordTrace (prefixWord ++ tailWord_6531436) baseStart_6531436 baseEnd_6531436 := by
    simpa [prefixWord, tailWord_6531436, baseEnd_6531436] using wordTrace_append hprefix tailTrace_6531436
  have hstable : (prefixWord ++ tailWord_6531436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531436).length < 2 ^ (prefixWord ++ tailWord_6531436).sum := by decide
  have hdescent : baseEnd_6531436 < baseStart_6531436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531452 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 3, 3, 2]
def baseStart_6531452 : Nat := 118140960795 + 6531452 * 2 ^ 59
def prefixEnd_6531452 : Nat := 4983230072969 + 3 ^ 40 * 6531452 * 2
def baseEnd_6531452 : Nat := 3353774247769884897712405

theorem tailTrace_6531452 : CollatzResearch.WordTrace tailWord_6531452 prefixEnd_6531452 3353774247769884897712405 := by
  unfold tailWord_6531452
  simp only [CollatzResearch.WordTrace]
  refine ⟨119110812566836181019278305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158814416755781574692371073 119110812566836181019278305)
  ·
    refine ⟨89333109425127135764458729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119110812566836181019278305 89333109425127135764458729)
    ·
      refine ⟨66999832068845351823344047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89333109425127135764458729 66999832068845351823344047)
      ·
        refine ⟨100499748103268027735016071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66999832068845351823344047 100499748103268027735016071)
        ·
          refine ⟨150749622154902041602524107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100499748103268027735016071 150749622154902041602524107)
          ·
            refine ⟨226124433232353062403786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150749622154902041602524107 226124433232353062403786161)
            ·
              refine ⟨169593324924264796802839621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226124433232353062403786161 169593324924264796802839621)
              ·
                refine ⟨31798748423299649400532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169593324924264796802839621 31798748423299649400532429)
                ·
                  refine ⟨11924530658737368525199661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31798748423299649400532429 11924530658737368525199661)
                  ·
                    refine ⟨4471698997026513196949873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11924530658737368525199661 4471698997026513196949873)
                    ·
                      refine ⟨3353774247769884897712405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471698997026513196949873 3353774247769884897712405)
                      ·
                        rfl

theorem cell23_6531452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_6531452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531452 prefixEnd_6531452 := by exact prefixLift 6531452
  have htrace : WordTrace (prefixWord ++ tailWord_6531452) baseStart_6531452 baseEnd_6531452 := by
    simpa [prefixWord, tailWord_6531452, baseEnd_6531452] using wordTrace_append hprefix tailTrace_6531452
  have hstable : (prefixWord ++ tailWord_6531452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531452).length < 2 ^ (prefixWord ++ tailWord_6531452).sum := by decide
  have hdescent : baseEnd_6531452 < baseStart_6531452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531459 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 3]
def baseStart_6531459 : Nat := 118140960795 + 6531459 * 2 ^ 59
def prefixEnd_6531459 : Nat := 4983230072969 + 3 ^ 40 * 6531459 * 2
def baseEnd_6531459 : Nat := 3353777842134466370324873

theorem tailTrace_6531459 : CollatzResearch.WordTrace tailWord_6531459 prefixEnd_6531459 3353777842134466370324873 := by
  unfold tailWord_6531459
  simp only [CollatzResearch.WordTrace]
  refine ⟨238221880444647002234061431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158814586963098001489374287 238221880444647002234061431)
  ·
    refine ⟨357332820666970503351092147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238221880444647002234061431 357332820666970503351092147)
    ·
      refine ⟨535999231000455755026638221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357332820666970503351092147 535999231000455755026638221)
      ·
        refine ⟨200999711625170908134989333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535999231000455755026638221 200999711625170908134989333)
        ·
          refine ⟨9421861482429886318827625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200999711625170908134989333 9421861482429886318827625)
          ·
            refine ⟨7066396111822414739120719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9421861482429886318827625 7066396111822414739120719)
            ·
              refine ⟨10599594167733622108681079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066396111822414739120719 10599594167733622108681079)
              ·
                refine ⟨15899391251600433163021619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10599594167733622108681079 15899391251600433163021619)
                ·
                  refine ⟨23849086877400649744532429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15899391251600433163021619 23849086877400649744532429)
                  ·
                    refine ⟨8943407579025243654199661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23849086877400649744532429 8943407579025243654199661)
                    ·
                      refine ⟨3353777842134466370324873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943407579025243654199661 3353777842134466370324873)
                      ·
                        rfl

theorem cell23_6531459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_6531459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531459 prefixEnd_6531459 := by exact prefixLift 6531459
  have htrace : WordTrace (prefixWord ++ tailWord_6531459) baseStart_6531459 baseEnd_6531459 := by
    simpa [prefixWord, tailWord_6531459, baseEnd_6531459] using wordTrace_append hprefix tailTrace_6531459
  have hstable : (prefixWord ++ tailWord_6531459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531459).length < 2 ^ (prefixWord ++ tailWord_6531459).sum := by decide
  have hdescent : baseEnd_6531459 < baseStart_6531459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531466 : List Nat := [3, 1, 2, 5, 2, 1, 2, 7]
def baseStart_6531466 : Nat := 118140960795 + 6531466 * 2 ^ 59
def prefixEnd_6531466 : Nat := 4983230072969 + 3 ^ 40 * 6531466 * 2
def baseEnd_6531466 : Nat := 124214127277742512701383

theorem tailTrace_6531466 : CollatzResearch.WordTrace tailWord_6531466 prefixEnd_6531466 124214127277742512701383 := by
  unfold tailWord_6531466
  simp only [CollatzResearch.WordTrace]
  refine ⟨59555533938905410607391563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158814757170414428286377501 59555533938905410607391563)
  ·
    refine ⟨89333300908358115911087345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59555533938905410607391563 89333300908358115911087345)
    ·
      refine ⟨66999975681268586933315509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89333300908358115911087345 66999975681268586933315509)
      ·
        refine ⟨6281247720118930024998329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66999975681268586933315509 6281247720118930024998329)
        ·
          refine ⟨4710935790089197518748747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6281247720118930024998329 4710935790089197518748747)
          ·
            refine ⟨7066403685133796278123121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710935790089197518748747 7066403685133796278123121)
            ·
              refine ⟨5299802763850347208592341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066403685133796278123121 5299802763850347208592341)
              ·
                refine ⟨124214127277742512701383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5299802763850347208592341 124214127277742512701383)
                ·
                  rfl

theorem cell23_6531466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_6531466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531466 prefixEnd_6531466 := by exact prefixLift 6531466
  have htrace : WordTrace (prefixWord ++ tailWord_6531466) baseStart_6531466 baseEnd_6531466 := by
    simpa [prefixWord, tailWord_6531466, baseEnd_6531466] using wordTrace_append hprefix tailTrace_6531466
  have hstable : (prefixWord ++ tailWord_6531466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531466).length < 2 ^ (prefixWord ++ tailWord_6531466).sum := by decide
  have hdescent : baseEnd_6531466 < baseStart_6531466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531545 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_6531545 : Nat := 118140960795 + 6531545 * 2 ^ 59
def prefixEnd_6531545 : Nat := 4983230072969 + 3 ^ 40 * 6531545 * 2
def baseEnd_6531545 : Nat := 3353822001470753033849477

theorem tailTrace_6531545 : CollatzResearch.WordTrace tailWord_6531545 prefixEnd_6531545 3353822001470753033849477 := by
  unfold tailWord_6531545
  simp only [CollatzResearch.WordTrace]
  refine ⟨238225017122335438921692089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158816678081556959281128059 238225017122335438921692089)
  ·
    refine ⟨178668762841751579191269067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238225017122335438921692089 178668762841751579191269067)
    ·
      refine ⟨268003144262627368786903601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178668762841751579191269067 268003144262627368786903601)
      ·
        refine ⟨201002358196970526590177701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268003144262627368786903601 201002358196970526590177701)
        ·
          refine ⟨37687942161931973735658319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201002358196970526590177701 37687942161931973735658319)
          ·
            refine ⟨56531913242897960603487479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37687942161931973735658319 56531913242897960603487479)
            ·
              refine ⟨84797869864346940905231219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56531913242897960603487479 84797869864346940905231219)
              ·
                refine ⟨127196804796520411357846829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84797869864346940905231219 127196804796520411357846829)
                ·
                  refine ⟨47698801798695154259192561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127196804796520411357846829 47698801798695154259192561)
                  ·
                    refine ⟨35774101349021365694394421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47698801798695154259192561 35774101349021365694394421)
                    ·
                      refine ⟨3353822001470753033849477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35774101349021365694394421 3353822001470753033849477)
                      ·
                        rfl

theorem cell23_6531545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_6531545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531545 prefixEnd_6531545 := by exact prefixLift 6531545
  have htrace : WordTrace (prefixWord ++ tailWord_6531545) baseStart_6531545 baseEnd_6531545 := by
    simpa [prefixWord, tailWord_6531545, baseEnd_6531545] using wordTrace_append hprefix tailTrace_6531545
  have hstable : (prefixWord ++ tailWord_6531545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531545).length < 2 ^ (prefixWord ++ tailWord_6531545).sum := by decide
  have hdescent : baseEnd_6531545 < baseStart_6531545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531562 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6531562 : Nat := 118140960795 + 6531562 * 2 ^ 59
def prefixEnd_6531562 : Nat := 4983230072969 + 3 ^ 40 * 6531562 * 2
def baseEnd_6531562 : Nat := 3353830730641879467336899

theorem tailTrace_6531562 : CollatzResearch.WordTrace tailWord_6531562 prefixEnd_6531562 3353830730641879467336899 := by
  unfold tailWord_6531562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59556409290818462706265235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158817091442182567216707293 59556409290818462706265235)
  ·
    refine ⟨89334613936227694059397853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59556409290818462706265235 89334613936227694059397853)
    ·
      refine ⟨33500480226085385272274195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89334613936227694059397853 33500480226085385272274195)
      ·
        refine ⟨50250720339128077908411293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33500480226085385272274195 50250720339128077908411293)
        ·
          refine ⟨18844020127173029215654235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50250720339128077908411293 18844020127173029215654235)
          ·
            refine ⟨28266030190759543823481353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844020127173029215654235 28266030190759543823481353)
            ·
              refine ⟨21199522643069657867611015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28266030190759543823481353 21199522643069657867611015)
              ·
                refine ⟨31799283964604486801416523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199522643069657867611015 31799283964604486801416523)
                ·
                  refine ⟨47698925946906730202124785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31799283964604486801416523 47698925946906730202124785)
                  ·
                    refine ⟨35774194460180047651593589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47698925946906730202124785 35774194460180047651593589)
                    ·
                      refine ⟨3353830730641879467336899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35774194460180047651593589 3353830730641879467336899)
                      ·
                        rfl

theorem cell23_6531562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6531562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531562 prefixEnd_6531562 := by exact prefixLift 6531562
  have htrace : WordTrace (prefixWord ++ tailWord_6531562) baseStart_6531562 baseEnd_6531562 := by
    simpa [prefixWord, tailWord_6531562, baseEnd_6531562] using wordTrace_append hprefix tailTrace_6531562
  have hstable : (prefixWord ++ tailWord_6531562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531562).length < 2 ^ (prefixWord ++ tailWord_6531562).sum := by decide
  have hdescent : baseEnd_6531562 < baseStart_6531562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531590 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6531590 : Nat := 118140960795 + 6531590 * 2 ^ 59
def prefixEnd_6531590 : Nat := 4983230072969 + 3 ^ 40 * 6531590 * 2
def baseEnd_6531590 : Nat := 372649456455578373087419

theorem tailTrace_6531590 : CollatzResearch.WordTrace tailWord_6531590 prefixEnd_6531590 372649456455578373087419 := by
  unfold tailWord_6531590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444583075224137862721257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158817772271448274404720149 7444583075224137862721257)
  ·
    refine ⟨5583437306418103397040943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7444583075224137862721257 5583437306418103397040943)
    ·
      refine ⟨8375155959627155095561415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583437306418103397040943 8375155959627155095561415)
      ·
        refine ⟨12562733939440732643342123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375155959627155095561415 12562733939440732643342123)
        ·
          refine ⟨18844100909161098965013185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562733939440732643342123 18844100909161098965013185)
          ·
            refine ⟨14133075681870824223759889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18844100909161098965013185 14133075681870824223759889)
            ·
              refine ⟨10599806761403118167819917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14133075681870824223759889 10599806761403118167819917)
              ·
                refine ⟨3974927535526169312932469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10599806761403118167819917 3974927535526169312932469)
                ·
                  refine ⟨372649456455578373087419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974927535526169312932469 372649456455578373087419)
                  ·
                    rfl

theorem cell23_6531590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6531590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531590 prefixEnd_6531590 := by exact prefixLift 6531590
  have htrace : WordTrace (prefixWord ++ tailWord_6531590) baseStart_6531590 baseEnd_6531590 := by
    simpa [prefixWord, tailWord_6531590, baseEnd_6531590] using wordTrace_append hprefix tailTrace_6531590
  have hstable : (prefixWord ++ tailWord_6531590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531590).length < 2 ^ (prefixWord ++ tailWord_6531590).sum := by decide
  have hdescent : baseEnd_6531590 < baseStart_6531590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531599 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 1, 4]
def baseStart_6531599 : Nat := 118140960795 + 6531599 * 2 ^ 59
def prefixEnd_6531599 : Nat := 4983230072969 + 3 ^ 40 * 6531599 * 2
def baseEnd_6531599 : Nat := 1117949909808698607524743

theorem tailTrace_6531599 : CollatzResearch.WordTrace tailWord_6531599 prefixEnd_6531599 1117949909808698607524743 := by
  unfold tailWord_6531599
  simp only [CollatzResearch.WordTrace]
  refine ⟨238226986664139806144157851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158817991109426537429438567 238226986664139806144157851)
  ·
    refine ⟨357340479996209709216236777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238226986664139806144157851 357340479996209709216236777)
    ·
      refine ⟨268005359997157281912177583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357340479996209709216236777 268005359997157281912177583)
      ·
        refine ⟨402008039995735922868266375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268005359997157281912177583 402008039995735922868266375)
        ·
          refine ⟨603012059993603884302399563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402008039995735922868266375 603012059993603884302399563)
          ·
            refine ⟨904518089990405826453599345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603012059993603884302399563 904518089990405826453599345)
            ·
              refine ⟨678388567492804369840199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904518089990405826453599345 678388567492804369840199509)
              ·
                refine ⟨3974933012653150604532419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 678388567492804369840199509 3974933012653150604532419)
                ·
                  refine ⟨5962399518979725906798629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974933012653150604532419 5962399518979725906798629)
                  ·
                    refine ⟨1117949909808698607524743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962399518979725906798629 1117949909808698607524743)
                    ·
                      rfl

theorem cell23_6531599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_6531599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531599 prefixEnd_6531599 := by exact prefixLift 6531599
  have htrace : WordTrace (prefixWord ++ tailWord_6531599) baseStart_6531599 baseEnd_6531599 := by
    simpa [prefixWord, tailWord_6531599, baseEnd_6531599] using wordTrace_append hprefix tailTrace_6531599
  have hstable : (prefixWord ++ tailWord_6531599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531599).length < 2 ^ (prefixWord ++ tailWord_6531599).sum := by decide
  have hdescent : baseEnd_6531599 < baseStart_6531599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531612 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 8]
def baseStart_6531612 : Nat := 118140960795 + 6531612 * 2 ^ 59
def prefixEnd_6531612 : Nat := 4983230072969 + 3 ^ 40 * 6531612 * 2
def baseEnd_6531612 : Nat := 372650711630511585745741

theorem tailTrace_6531612 : CollatzResearch.WordTrace tailWord_6531612 prefixEnd_6531612 372650711630511585745741 := by
  unfold tailWord_6531612
  simp only [CollatzResearch.WordTrace]
  refine ⟨119113730406546354682190545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158818307208728472909587393 119113730406546354682190545)
  ·
    refine ⟨89335297804909766011642909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119113730406546354682190545 89335297804909766011642909)
    ·
      refine ⟨33500736676841162254366091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89335297804909766011642909 33500736676841162254366091)
      ·
        refine ⟨50251105015261743381549137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33500736676841162254366091 50251105015261743381549137)
        ·
          refine ⟨37688328761446307536161853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50251105015261743381549137 37688328761446307536161853)
          ·
            refine ⟨14133123285542365326060695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37688328761446307536161853 14133123285542365326060695)
            ·
              refine ⟨21199684928313547989091043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133123285542365326060695 21199684928313547989091043)
              ·
                refine ⟨31799527392470321983636565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199684928313547989091043 31799527392470321983636565)
                ·
                  refine ⟨372650711630511585745741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31799527392470321983636565 372650711630511585745741)
                  ·
                    rfl

theorem cell23_6531612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_6531612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531612 prefixEnd_6531612 := by exact prefixLift 6531612
  have htrace : WordTrace (prefixWord ++ tailWord_6531612) baseStart_6531612 baseEnd_6531612 := by
    simpa [prefixWord, tailWord_6531612, baseEnd_6531612] using wordTrace_append hprefix tailTrace_6531612
  have hstable : (prefixWord ++ tailWord_6531612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531612).length < 2 ^ (prefixWord ++ tailWord_6531612).sum := by decide
  have hdescent : baseEnd_6531612 < baseStart_6531612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531616 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_6531616 : Nat := 118140960795 + 6531616 * 2 ^ 59
def prefixEnd_6531616 : Nat := 4983230072969 + 3 ^ 40 * 6531616 * 2
def baseEnd_6531616 : Nat := 1117952819532407418687217

theorem tailTrace_6531616 : CollatzResearch.WordTrace tailWord_6531616 prefixEnd_6531616 1117952819532407418687217 := by
  unfold tailWord_6531616
  simp only [CollatzResearch.WordTrace]
  refine ⟨119113803352539109023763351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158818404470052145365017801 119113803352539109023763351)
  ·
    refine ⟨178670705028808663535645027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119113803352539109023763351 178670705028808663535645027)
    ·
      refine ⟨268006057543212995303467541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178670705028808663535645027 268006057543212995303467541)
      ·
        refine ⟨12562783947338109154850041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 268006057543212995303467541 12562783947338109154850041)
        ·
          refine ⟨9422087960503581866137531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12562783947338109154850041 9422087960503581866137531)
          ·
            refine ⟨14133131940755372799206297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422087960503581866137531 14133131940755372799206297)
            ·
              refine ⟨10599848955566529599404723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14133131940755372799206297 10599848955566529599404723)
              ·
                refine ⟨15899773433349794399107085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10599848955566529599404723 15899773433349794399107085)
                ·
                  refine ⟨5962415037506172899665157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15899773433349794399107085 5962415037506172899665157)
                  ·
                    refine ⟨1117952819532407418687217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962415037506172899665157 1117952819532407418687217)
                    ·
                      rfl

theorem cell23_6531616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_6531616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531616 prefixEnd_6531616 := by exact prefixLift 6531616
  have htrace : WordTrace (prefixWord ++ tailWord_6531616) baseStart_6531616 baseEnd_6531616 := by
    simpa [prefixWord, tailWord_6531616, baseEnd_6531616] using wordTrace_append hprefix tailTrace_6531616
  have hstable : (prefixWord ++ tailWord_6531616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531616).length < 2 ^ (prefixWord ++ tailWord_6531616).sum := by decide
  have hdescent : baseEnd_6531616 < baseStart_6531616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531639 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_6531639 : Nat := 118140960795 + 6531639 * 2 ^ 59
def prefixEnd_6531639 : Nat := 4983230072969 + 3 ^ 40 * 6531639 * 2
def baseEnd_6531639 : Nat := 3353870268652275666074045

theorem tailTrace_6531639 : CollatzResearch.WordTrace tailWord_6531639 prefixEnd_6531639 3353870268652275666074045 := by
  unfold tailWord_6531639
  simp only [CollatzResearch.WordTrace]
  refine ⟨238228445583994892975613971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158818963722663261983742647 238228445583994892975613971)
  ·
    refine ⟨357342668375992339463420957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238228445583994892975613971 357342668375992339463420957)
    ·
      refine ⟨134003500640997127298782859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357342668375992339463420957 134003500640997127298782859)
      ·
        refine ⟨201005250961495690948174289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134003500640997127298782859 201005250961495690948174289)
        ·
          refine ⟨150753938221121768211130717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201005250961495690948174289 150753938221121768211130717)
          ·
            refine ⟨56532726832920663079174019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150753938221121768211130717 56532726832920663079174019)
            ·
              refine ⟨84799090249380994618761029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56532726832920663079174019 84799090249380994618761029)
              ·
                refine ⟨15899829421758936491017693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84799090249380994618761029 15899829421758936491017693)
                ·
                  refine ⟨5962436033159601184131635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15899829421758936491017693 5962436033159601184131635)
                  ·
                    refine ⟨8943654049739401776197453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962436033159601184131635 8943654049739401776197453)
                    ·
                      refine ⟨3353870268652275666074045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943654049739401776197453 3353870268652275666074045)
                      ·
                        rfl

theorem cell23_6531639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_6531639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531639 prefixEnd_6531639 := by exact prefixLift 6531639
  have htrace : WordTrace (prefixWord ++ tailWord_6531639) baseStart_6531639 baseEnd_6531639 := by
    simpa [prefixWord, tailWord_6531639, baseEnd_6531639] using wordTrace_append hprefix tailTrace_6531639
  have hstable : (prefixWord ++ tailWord_6531639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531639).length < 2 ^ (prefixWord ++ tailWord_6531639).sum := by decide
  have hdescent : baseEnd_6531639 < baseStart_6531639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531666 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_6531666 : Nat := 118140960795 + 6531666 * 2 ^ 59
def prefixEnd_6531666 : Nat := 4983230072969 + 3 ^ 40 * 6531666 * 2
def baseEnd_6531666 : Nat := 3353884132629947060436421

theorem tailTrace_6531666 : CollatzResearch.WordTrace tailWord_6531666 prefixEnd_6531666 3353884132629947060436421 := by
  unfold tailWord_6531666
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557357588724269146711713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158819620236598051057897901 59557357588724269146711713)
  ·
    refine ⟨44668018191543201860033785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59557357588724269146711713 44668018191543201860033785)
    ·
      refine ⟨33501013643657401395025339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44668018191543201860033785 33501013643657401395025339)
      ·
        refine ⟨50251520465486102092538009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33501013643657401395025339 50251520465486102092538009)
        ·
          refine ⟨37688640349114576569403507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50251520465486102092538009 37688640349114576569403507)
          ·
            refine ⟨56532960523671864854105261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37688640349114576569403507 56532960523671864854105261)
            ·
              refine ⟨21199860196376949320289473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56532960523671864854105261 21199860196376949320289473)
              ·
                refine ⟨15899895147282711990217105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21199860196376949320289473 15899895147282711990217105)
                ·
                  refine ⟨11924921360462033992662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15899895147282711990217105 11924921360462033992662829)
                  ·
                    refine ⟨4471845510173262747248561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11924921360462033992662829 4471845510173262747248561)
                    ·
                      refine ⟨3353884132629947060436421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471845510173262747248561 3353884132629947060436421)
                      ·
                        rfl

theorem cell23_6531666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_6531666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531666 prefixEnd_6531666 := by exact prefixLift 6531666
  have htrace : WordTrace (prefixWord ++ tailWord_6531666) baseStart_6531666 baseEnd_6531666 := by
    simpa [prefixWord, tailWord_6531666, baseEnd_6531666] using wordTrace_append hprefix tailTrace_6531666
  have hstable : (prefixWord ++ tailWord_6531666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531666).length < 2 ^ (prefixWord ++ tailWord_6531666).sum := by decide
  have hdescent : baseEnd_6531666 < baseStart_6531666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531692 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_6531692 : Nat := 118140960795 + 6531692 * 2 ^ 59
def prefixEnd_6531692 : Nat := 4983230072969 + 3 ^ 40 * 6531692 * 2
def baseEnd_6531692 : Nat := 3353897483126963958711301

theorem tailTrace_6531692 : CollatzResearch.WordTrace tailWord_6531692 prefixEnd_6531692 3353897483126963958711301 := by
  unfold tailWord_6531692
  simp only [CollatzResearch.WordTrace]
  refine ⟨119115189326401441513646665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158820252435201922018195553 119115189326401441513646665)
  ·
    refine ⟨89336391994801081135234999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119115189326401441513646665 89336391994801081135234999)
    ·
      refine ⟨134004587992201621702852499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89336391994801081135234999 134004587992201621702852499)
      ·
        refine ⟨201006881988302432554278749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134004587992201621702852499 201006881988302432554278749)
        ·
          refine ⟨75377580745613412207854531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201006881988302432554278749 75377580745613412207854531)
          ·
            refine ⟨113066371118420118311781797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75377580745613412207854531 113066371118420118311781797)
            ·
              refine ⟨21199944584703772183459087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113066371118420118311781797 21199944584703772183459087)
              ·
                refine ⟨31799916877055658275188631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21199944584703772183459087 31799916877055658275188631)
                ·
                  refine ⟨47699875315583487412782947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31799916877055658275188631 47699875315583487412782947)
                  ·
                    refine ⟨71549812973375231119174421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47699875315583487412782947 71549812973375231119174421)
                    ·
                      refine ⟨3353897483126963958711301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71549812973375231119174421 3353897483126963958711301)
                      ·
                        rfl

theorem cell23_6531692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_6531692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531692 prefixEnd_6531692 := by exact prefixLift 6531692
  have htrace : WordTrace (prefixWord ++ tailWord_6531692) baseStart_6531692 baseEnd_6531692 := by
    simpa [prefixWord, tailWord_6531692, baseEnd_6531692] using wordTrace_append hprefix tailTrace_6531692
  have hstable : (prefixWord ++ tailWord_6531692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531692).length < 2 ^ (prefixWord ++ tailWord_6531692).sum := by decide
  have hdescent : baseEnd_6531692 < baseStart_6531692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531699 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 3]
def baseStart_6531699 : Nat := 118140960795 + 6531699 * 2 ^ 59
def prefixEnd_6531699 : Nat := 4983230072969 + 3 ^ 40 * 6531699 * 2
def baseEnd_6531699 : Nat := 3353901077491545431323769

theorem tailTrace_6531699 : CollatzResearch.WordTrace tailWord_6531699 prefixEnd_6531699 3353901077491545431323769 := by
  unfold tailWord_6531699
  simp only [CollatzResearch.WordTrace]
  refine ⟨238230633963777523222798151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158820422642518348815198767 238230633963777523222798151)
  ·
    refine ⟨357345950945666284834197227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238230633963777523222798151 357345950945666284834197227)
    ·
      refine ⟨536018926418499427251295841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357345950945666284834197227 536018926418499427251295841)
      ·
        refine ⟨402014194813874570438471881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536018926418499427251295841 402014194813874570438471881)
        ·
          refine ⟨301510646110405927828853911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402014194813874570438471881 301510646110405927828853911)
          ·
            refine ⟨452265969165608891743280867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301510646110405927828853911 452265969165608891743280867)
            ·
              refine ⟨678398953748413337614921301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452265969165608891743280867 678398953748413337614921301)
              ·
                refine ⟨7949987739239218800174859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 678398953748413337614921301 7949987739239218800174859)
                ·
                  refine ⟨11924981608858828200262289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949987739239218800174859 11924981608858828200262289)
                  ·
                    refine ⟨8943736206644121150196717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11924981608858828200262289 8943736206644121150196717)
                    ·
                      refine ⟨3353901077491545431323769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943736206644121150196717 3353901077491545431323769)
                      ·
                        rfl

theorem cell23_6531699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_6531699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531699 prefixEnd_6531699 := by exact prefixLift 6531699
  have htrace : WordTrace (prefixWord ++ tailWord_6531699) baseStart_6531699 baseEnd_6531699 := by
    simpa [prefixWord, tailWord_6531699, baseEnd_6531699] using wordTrace_append hprefix tailTrace_6531699
  have hstable : (prefixWord ++ tailWord_6531699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531699).length < 2 ^ (prefixWord ++ tailWord_6531699).sum := by decide
  have hdescent : baseEnd_6531699 < baseStart_6531699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531716 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6531716 : Nat := 118140960795 + 6531716 * 2 ^ 59
def prefixEnd_6531716 : Nat := 4983230072969 + 3 ^ 40 * 6531716 * 2
def baseEnd_6531716 : Nat := 3353909806662671864811191

theorem tailTrace_6531716 : CollatzResearch.WordTrace tailWord_6531716 prefixEnd_6531716 3353909806662671864811191 := by
  unfold tailWord_6531716
  simp only [CollatzResearch.WordTrace]
  refine ⟨119115627002357967563083501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158820836003143956750778001 119115627002357967563083501)
  ·
    refine ⟨44668360125884237836156313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119115627002357967563083501 44668360125884237836156313)
    ·
      refine ⟨33501270094413178377117235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44668360125884237836156313 33501270094413178377117235)
      ·
        refine ⟨50251905141619767565675853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33501270094413178377117235 50251905141619767565675853)
        ·
          refine ⟨18844464428107412837128445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50251905141619767565675853 18844464428107412837128445)
          ·
            refine ⟨7066674160540279813923167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18844464428107412837128445 7066674160540279813923167)
            ·
              refine ⟨10600011240810419720884751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066674160540279813923167 10600011240810419720884751)
              ·
                refine ⟨15900016861215629581327127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10600011240810419720884751 15900016861215629581327127)
                ·
                  refine ⟨23850025291823444371990691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15900016861215629581327127 23850025291823444371990691)
                  ·
                    refine ⟨35775037937735166557986037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23850025291823444371990691 35775037937735166557986037)
                    ·
                      refine ⟨3353909806662671864811191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35775037937735166557986037 3353909806662671864811191)
                      ·
                        rfl

theorem cell23_6531716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6531716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531716 prefixEnd_6531716 := by exact prefixLift 6531716
  have htrace : WordTrace (prefixWord ++ tailWord_6531716) baseStart_6531716 baseEnd_6531716 := by
    simpa [prefixWord, tailWord_6531716, baseEnd_6531716] using wordTrace_append hprefix tailTrace_6531716
  have hstable : (prefixWord ++ tailWord_6531716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531716).length < 2 ^ (prefixWord ++ tailWord_6531716).sum := by decide
  have hdescent : baseEnd_6531716 < baseStart_6531716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531729 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_6531729 : Nat := 118140960795 + 6531729 * 2 ^ 59
def prefixEnd_6531729 : Nat := 4983230072969 + 3 ^ 40 * 6531729 * 2
def baseEnd_6531729 : Nat := 3353916481911180313948631

theorem tailTrace_6531729 : CollatzResearch.WordTrace tailWord_6531729 prefixEnd_6531729 3353916481911180313948631 := by
  unfold tailWord_6531729
  simp only [CollatzResearch.WordTrace]
  refine ⟨238231728153668838346390241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158821152102445892230926827 238231728153668838346390241)
  ·
    refine ⟨178673796115251628759792681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238231728153668838346390241 178673796115251628759792681)
    ·
      refine ⟨134005347086438721569844511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178673796115251628759792681 134005347086438721569844511)
      ·
        refine ⟨201008020629658082354766767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134005347086438721569844511 201008020629658082354766767)
        ·
          refine ⟨301512030944487123532150151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201008020629658082354766767 301512030944487123532150151)
          ·
            refine ⟨452268046416730685298225227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301512030944487123532150151 452268046416730685298225227)
            ·
              refine ⟨678402069625096027947337841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452268046416730685298225227 678402069625096027947337841)
              ·
                refine ⟨508801552218822020960503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678402069625096027947337841 508801552218822020960503381)
                ·
                  refine ⟨5962518190064320558130899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 508801552218822020960503381 5962518190064320558130899)
                  ·
                    refine ⟨8943777285096480837196349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962518190064320558130899 8943777285096480837196349)
                    ·
                      refine ⟨3353916481911180313948631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943777285096480837196349 3353916481911180313948631)
                      ·
                        rfl

theorem cell23_6531729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_6531729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531729 prefixEnd_6531729 := by exact prefixLift 6531729
  have htrace : WordTrace (prefixWord ++ tailWord_6531729) baseStart_6531729 baseEnd_6531729 := by
    simpa [prefixWord, tailWord_6531729, baseEnd_6531729] using wordTrace_append hprefix tailTrace_6531729
  have hstable : (prefixWord ++ tailWord_6531729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531729).length < 2 ^ (prefixWord ++ tailWord_6531729).sum := by decide
  have hdescent : baseEnd_6531729 < baseStart_6531729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531762 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_6531762 : Nat := 118140960795 + 6531762 * 2 ^ 59
def prefixEnd_6531762 : Nat := 4983230072969 + 3 ^ 40 * 6531762 * 2
def baseEnd_6531762 : Nat := 1117977808924259561611993

theorem tailTrace_6531762 : CollatzResearch.WordTrace tailWord_6531762 prefixEnd_6531762 1117977808924259561611993 := by
  unfold tailWord_6531762
  simp only [CollatzResearch.WordTrace]
  refine ⟨59558232940637321245585385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158821954508366189988227693 59558232940637321245585385)
  ·
    refine ⟨44668674705477990934189039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59558232940637321245585385 44668674705477990934189039)
    ·
      refine ⟨67003012058216986401283559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44668674705477990934189039 67003012058216986401283559)
      ·
        refine ⟨100504518087325479601925339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67003012058216986401283559 100504518087325479601925339)
        ·
          refine ⟨150756777130988219402888009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100504518087325479601925339 150756777130988219402888009)
          ·
            refine ⟨113067582848241164552166007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150756777130988219402888009 113067582848241164552166007)
            ·
              refine ⟨169601374272361746828249011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113067582848241164552166007 169601374272361746828249011)
              ·
                refine ⟨254402061408542620242373517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169601374272361746828249011 254402061408542620242373517)
                ·
                  refine ⟨95400773028203482590890069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254402061408542620242373517 95400773028203482590890069)
                  ·
                    refine ⟨1117977808924259561611993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95400773028203482590890069 1117977808924259561611993)
                    ·
                      rfl

theorem cell23_6531762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_6531762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531762 prefixEnd_6531762 := by exact prefixLift 6531762
  have htrace : WordTrace (prefixWord ++ tailWord_6531762) baseStart_6531762 baseEnd_6531762 := by
    simpa [prefixWord, tailWord_6531762, baseEnd_6531762] using wordTrace_append hprefix tailTrace_6531762
  have hstable : (prefixWord ++ tailWord_6531762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531762).length < 2 ^ (prefixWord ++ tailWord_6531762).sum := by decide
  have hdescent : baseEnd_6531762 < baseStart_6531762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531773 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6531773 : Nat := 118140960795 + 6531773 * 2 ^ 59
def prefixEnd_6531773 : Nat := 4983230072969 + 3 ^ 40 * 6531773 * 2
def baseEnd_6531773 : Nat := 3353939075059978141798429

theorem tailTrace_6531773 : CollatzResearch.WordTrace tailWord_6531773 prefixEnd_6531773 3353939075059978141798429 := by
  unfold tailWord_6531773
  simp only [CollatzResearch.WordTrace]
  refine ⟨238233332965509433860991973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158822221977006289240661315 238233332965509433860991973)
  ·
    refine ⟨44668749931033018848935995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238233332965509433860991973 44668749931033018848935995)
    ·
      refine ⟨67003124896549528273403993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44668749931033018848935995 67003124896549528273403993)
      ·
        refine ⟨50252343672412146205052995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67003124896549528273403993 50252343672412146205052995)
        ·
          refine ⟨75378515508618219307579493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50252343672412146205052995 75378515508618219307579493)
          ·
            refine ⟨14133471657865916120171155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75378515508618219307579493 14133471657865916120171155)
            ·
              refine ⟨21200207486798874180256733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133471657865916120171155 21200207486798874180256733)
              ·
                refine ⟨7950077807549577817596275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21200207486798874180256733 7950077807549577817596275)
                ·
                  refine ⟨11925116711324366726394413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950077807549577817596275 11925116711324366726394413)
                  ·
                    refine ⟨4471918766746637522397905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11925116711324366726394413 4471918766746637522397905)
                    ·
                      refine ⟨3353939075059978141798429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471918766746637522397905 3353939075059978141798429)
                      ·
                        rfl

theorem cell23_6531773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6531773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531773 prefixEnd_6531773 := by exact prefixLift 6531773
  have htrace : WordTrace (prefixWord ++ tailWord_6531773) baseStart_6531773 baseEnd_6531773 := by
    simpa [prefixWord, tailWord_6531773, baseEnd_6531773] using wordTrace_append hprefix tailTrace_6531773
  have hstable : (prefixWord ++ tailWord_6531773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531773).length < 2 ^ (prefixWord ++ tailWord_6531773).sum := by decide
  have hdescent : baseEnd_6531773 < baseStart_6531773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531780 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_6531780 : Nat := 118140960795 + 6531780 * 2 ^ 59
def prefixEnd_6531780 : Nat := 4983230072969 + 3 ^ 40 * 6531780 * 2
def baseEnd_6531780 : Nat := 3353942669424559614410897

theorem tailTrace_6531780 : CollatzResearch.WordTrace tailWord_6531780 prefixEnd_6531780 3353942669424559614410897 := by
  unfold tailWord_6531780
  simp only [CollatzResearch.WordTrace]
  refine ⟨119116794138242037028248397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158822392184322716037664529 119116794138242037028248397)
  ·
    refine ⟨44668797801840763885593149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119116794138242037028248397 44668797801840763885593149)
    ·
      refine ⟨16750799175690286457097431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44668797801840763885593149 16750799175690286457097431)
      ·
        refine ⟨25126198763535429685646147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16750799175690286457097431 25126198763535429685646147)
        ·
          refine ⟨37689298145303144528469221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25126198763535429685646147 37689298145303144528469221)
          ·
            refine ⟨7066743402244339599087979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37689298145303144528469221 7066743402244339599087979)
            ·
              refine ⟨10600115103366509398631969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066743402244339599087979 10600115103366509398631969)
              ·
                refine ⟨7950086327524882048973977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10600115103366509398631969 7950086327524882048973977)
                ·
                  refine ⟨5962564745643661536730483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950086327524882048973977 5962564745643661536730483)
                  ·
                    refine ⟨8943847118465492305095725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962564745643661536730483 8943847118465492305095725)
                    ·
                      refine ⟨3353942669424559614410897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943847118465492305095725 3353942669424559614410897)
                      ·
                        rfl

theorem cell23_6531780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_6531780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531780 prefixEnd_6531780 := by exact prefixLift 6531780
  have htrace : WordTrace (prefixWord ++ tailWord_6531780) baseStart_6531780 baseEnd_6531780 := by
    simpa [prefixWord, tailWord_6531780, baseEnd_6531780] using wordTrace_append hprefix tailTrace_6531780
  have hstable : (prefixWord ++ tailWord_6531780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531780).length < 2 ^ (prefixWord ++ tailWord_6531780).sum := by decide
  have hdescent : baseEnd_6531780 < baseStart_6531780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531797 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6531797 : Nat := 118140960795 + 6531797 * 2 ^ 59
def prefixEnd_6531797 : Nat := 4983230072969 + 3 ^ 40 * 6531797 * 2
def baseEnd_6531797 : Nat := 3353951398595686047898319

theorem tailTrace_6531797 : CollatzResearch.WordTrace tailWord_6531797 prefixEnd_6531797 3353951398595686047898319 := by
  unfold tailWord_6531797
  simp only [CollatzResearch.WordTrace]
  refine ⟨238234208317422485959865645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158822805544948323973243763 238234208317422485959865645)
  ·
    refine ⟨89337828119033432234949617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238234208317422485959865645 89337828119033432234949617)
    ·
      refine ⟨67003371089275074176212213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89337828119033432234949617 67003371089275074176212213)
      ·
        refine ⟨6281566039619538204019895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67003371089275074176212213 6281566039619538204019895)
        ·
          refine ⟨9422349059429307306029843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281566039619538204019895 9422349059429307306029843)
          ·
            refine ⟨14133523589143960959044765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422349059429307306029843 14133523589143960959044765)
            ·
              refine ⟨5300071345928985359641787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14133523589143960959044765 5300071345928985359641787)
              ·
                refine ⟨7950107018893478039462681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300071345928985359641787 7950107018893478039462681)
                ·
                  refine ⟨5962580264170108529597011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950107018893478039462681 5962580264170108529597011)
                  ·
                    refine ⟨8943870396255162794395517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962580264170108529597011 8943870396255162794395517)
                    ·
                      refine ⟨3353951398595686047898319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943870396255162794395517 3353951398595686047898319)
                      ·
                        rfl

theorem cell23_6531797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6531797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531797 prefixEnd_6531797 := by exact prefixLift 6531797
  have htrace : WordTrace (prefixWord ++ tailWord_6531797) baseStart_6531797 baseEnd_6531797 := by
    simpa [prefixWord, tailWord_6531797, baseEnd_6531797] using wordTrace_append hprefix tailTrace_6531797
  have hstable : (prefixWord ++ tailWord_6531797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531797).length < 2 ^ (prefixWord ++ tailWord_6531797).sum := by decide
  have hdescent : baseEnd_6531797 < baseStart_6531797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531799 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_6531799 : Nat := 118140960795 + 6531799 * 2 ^ 59
def prefixEnd_6531799 : Nat := 4983230072969 + 3 ^ 40 * 6531799 * 2
def baseEnd_6531799 : Nat := 3353952425556995040073309

theorem tailTrace_6531799 : CollatzResearch.WordTrace tailWord_6531799 prefixEnd_6531799 3353952425556995040073309 := by
  unfold tailWord_6531799
  simp only [CollatzResearch.WordTrace]
  refine ⟨238234281263415240301438451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158822854175610160200958967 238234281263415240301438451)
  ·
    refine ⟨357351421895122860452157677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238234281263415240301438451 357351421895122860452157677)
    ·
      refine ⟨134006783210671072669559129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357351421895122860452157677 134006783210671072669559129)
      ·
        refine ⟨100505087408003304502169347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134006783210671072669559129 100505087408003304502169347)
        ·
          refine ⟨150757631112004956753254021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100505087408003304502169347 150757631112004956753254021)
          ·
            refine ⟨28267055833500929391235129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150757631112004956753254021 28267055833500929391235129)
            ·
              refine ⟨21200291875125697043426347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28267055833500929391235129 21200291875125697043426347)
              ·
                refine ⟨31800437812688545565139521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21200291875125697043426347 31800437812688545565139521)
                ·
                  refine ⟨23850328359516409173854641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31800437812688545565139521 23850328359516409173854641)
                  ·
                    refine ⟨17887746269637306880390981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23850328359516409173854641 17887746269637306880390981)
                    ·
                      refine ⟨3353952425556995040073309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17887746269637306880390981 3353952425556995040073309)
                      ·
                        rfl

theorem cell23_6531799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_6531799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531799 prefixEnd_6531799 := by exact prefixLift 6531799
  have htrace : WordTrace (prefixWord ++ tailWord_6531799) baseStart_6531799 baseEnd_6531799 := by
    simpa [prefixWord, tailWord_6531799, baseEnd_6531799] using wordTrace_append hprefix tailTrace_6531799
  have hstable : (prefixWord ++ tailWord_6531799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531799).length < 2 ^ (prefixWord ++ tailWord_6531799).sum := by decide
  have hdescent : baseEnd_6531799 < baseStart_6531799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531809 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 7]
def baseStart_6531809 : Nat := 118140960795 + 6531809 * 2 ^ 59
def prefixEnd_6531809 : Nat := 4983230072969 + 3 ^ 40 * 6531809 * 2
def baseEnd_6531809 : Nat := 372661951151504444549807

theorem tailTrace_6531809 : CollatzResearch.WordTrace tailWord_6531809 prefixEnd_6531809 372661951151504444549807 := by
  unfold tailWord_6531809
  simp only [CollatzResearch.WordTrace]
  refine ⟨238234645993379012009302481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158823097328919341339534987 238234645993379012009302481)
  ·
    refine ⟨178675984495034259006976861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238234645993379012009302481 178675984495034259006976861)
    ·
      refine ⟨67003494185637847127616323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178675984495034259006976861 67003494185637847127616323)
      ·
        refine ⟨100505241278456770691424485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67003494185637847127616323 100505241278456770691424485)
        ·
          refine ⟨18844732739710644504642091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100505241278456770691424485 18844732739710644504642091)
          ·
            refine ⟨28267099109565966756963137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18844732739710644504642091 28267099109565966756963137)
            ·
              refine ⟨21200324332174475067722353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28267099109565966756963137 21200324332174475067722353)
              ·
                refine ⟨15900243249130856300791765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21200324332174475067722353 15900243249130856300791765)
                ·
                  refine ⟨372661951151504444549807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15900243249130856300791765 372661951151504444549807)
                  ·
                    rfl

theorem cell23_6531809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_6531809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531809 prefixEnd_6531809 := by exact prefixLift 6531809
  have htrace : WordTrace (prefixWord ++ tailWord_6531809) baseStart_6531809 baseEnd_6531809 := by
    simpa [prefixWord, tailWord_6531809, baseEnd_6531809] using wordTrace_append hprefix tailTrace_6531809
  have hstable : (prefixWord ++ tailWord_6531809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531809).length < 2 ^ (prefixWord ++ tailWord_6531809).sum := by decide
  have hdescent : baseEnd_6531809 < baseStart_6531809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531859 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4]
def baseStart_6531859 : Nat := 118140960795 + 6531859 * 2 ^ 59
def prefixEnd_6531859 : Nat := 4983230072969 + 3 ^ 40 * 6531859 * 2
def baseEnd_6531859 : Nat := 3353983234396264805323033

theorem tailTrace_6531859 : CollatzResearch.WordTrace tailWord_6531859 prefixEnd_6531859 3353983234396264805323033 := by
  unfold tailWord_6531859
  simp only [CollatzResearch.WordTrace]
  refine ⟨238236469643197870548622631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158824313095465247032415087 238236469643197870548622631)
  ·
    refine ⟨357354704464796805822933947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238236469643197870548622631 357354704464796805822933947)
    ·
      refine ⟨536032056697195208734400921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357354704464796805822933947 536032056697195208734400921)
      ·
        refine ⟨402024042522896406550800691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536032056697195208734400921 402024042522896406550800691)
        ·
          refine ⟨603036063784344609826201037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402024042522896406550800691 603036063784344609826201037)
          ·
            refine ⟨226138523919129228684825389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603036063784344609826201037 226138523919129228684825389)
            ·
              refine ⟨84801946469673460756809521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226138523919129228684825389 84801946469673460756809521)
              ·
                refine ⟨63601459852255095567607141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84801946469673460756809521 63601459852255095567607141)
                ·
                  refine ⟨11925273722297830418926339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63601459852255095567607141 11925273722297830418926339)
                  ·
                    refine ⟨17887910583446745628389509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11925273722297830418926339 17887910583446745628389509)
                    ·
                      refine ⟨3353983234396264805323033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17887910583446745628389509 3353983234396264805323033)
                      ·
                        rfl

theorem cell23_6531859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_6531859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531859 prefixEnd_6531859 := by exact prefixLift 6531859
  have htrace : WordTrace (prefixWord ++ tailWord_6531859) baseStart_6531859 baseEnd_6531859 := by
    simpa [prefixWord, tailWord_6531859, baseEnd_6531859] using wordTrace_append hprefix tailTrace_6531859
  have hstable : (prefixWord ++ tailWord_6531859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531859).length < 2 ^ (prefixWord ++ tailWord_6531859).sum := by decide
  have hdescent : baseEnd_6531859 < baseStart_6531859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531889 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6531889 : Nat := 118140960795 + 6531889 * 2 ^ 59
def prefixEnd_6531889 : Nat := 4983230072969 + 3 ^ 40 * 6531889 * 2
def baseEnd_6531889 : Nat := 3353998638815899687947895

theorem tailTrace_6531889 : CollatzResearch.WordTrace tailWord_6531889 prefixEnd_6531889 3353998638815899687947895 := by
  unfold tailWord_6531889
  simp only [CollatzResearch.WordTrace]
  refine ⟨238237563833089185672214721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158825042555392790448143147 238237563833089185672214721)
  ·
    refine ⟨178678172874816889254161041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238237563833089185672214721 178678172874816889254161041)
    ·
      refine ⟨134008629656112666940620781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178678172874816889254161041 134008629656112666940620781)
      ·
        refine ⟨50253236121042250102732793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134008629656112666940620781 50253236121042250102732793)
        ·
          refine ⟨37689927090781687577049595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50253236121042250102732793 37689927090781687577049595)
          ·
            refine ⟨56534890636172531365574393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37689927090781687577049595 56534890636172531365574393)
            ·
              refine ⟨42401167977129398524180795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56534890636172531365574393 42401167977129398524180795)
              ·
                refine ⟨63601751965694097786271193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42401167977129398524180795 63601751965694097786271193)
                ·
                  refine ⟨47701313974270573339703395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63601751965694097786271193 47701313974270573339703395)
                  ·
                    refine ⟨71551970961405860009555093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47701313974270573339703395 71551970961405860009555093)
                    ·
                      refine ⟨3353998638815899687947895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71551970961405860009555093 3353998638815899687947895)
                      ·
                        rfl

theorem cell23_6531889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6531889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531889 prefixEnd_6531889 := by exact prefixLift 6531889
  have htrace : WordTrace (prefixWord ++ tailWord_6531889) baseStart_6531889 baseEnd_6531889 := by
    simpa [prefixWord, tailWord_6531889, baseEnd_6531889] using wordTrace_append hprefix tailTrace_6531889
  have hstable : (prefixWord ++ tailWord_6531889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531889).length < 2 ^ (prefixWord ++ tailWord_6531889).sum := by decide
  have hdescent : baseEnd_6531889 < baseStart_6531889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531894 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_6531894 : Nat := 118140960795 + 6531894 * 2 ^ 59
def prefixEnd_6531894 : Nat := 4983230072969 + 3 ^ 40 * 6531894 * 2
def baseEnd_6531894 : Nat := 372666800691019129820597

theorem tailTrace_6531894 : CollatzResearch.WordTrace tailWord_6531894 prefixEnd_6531894 372666800691019129820597 := by
  unfold tailWord_6531894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889859137379441970384171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158825164132047381017431157 14889859137379441970384171)
  ·
    refine ⟨22334788706069162955576257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889859137379441970384171 22334788706069162955576257)
    ·
      refine ⟨16751091529551872216682193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22334788706069162955576257 16751091529551872216682193)
      ·
        refine ⟨12563318647163904162511645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16751091529551872216682193 12563318647163904162511645)
        ·
          refine ⟨4711244492686464060941867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12563318647163904162511645 4711244492686464060941867)
          ·
            refine ⟨7066866739029696091412801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711244492686464060941867 7066866739029696091412801)
            ·
              refine ⟨5300150054272272068559601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066866739029696091412801 5300150054272272068559601)
              ·
                refine ⟨3975112540704204051419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300150054272272068559601 3975112540704204051419701)
                ·
                  refine ⟨372666800691019129820597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975112540704204051419701 372666800691019129820597)
                  ·
                    rfl

theorem cell23_6531894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_6531894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531894 prefixEnd_6531894 := by exact prefixLift 6531894
  have htrace : WordTrace (prefixWord ++ tailWord_6531894) baseStart_6531894 baseEnd_6531894 := by
    simpa [prefixWord, tailWord_6531894, baseEnd_6531894] using wordTrace_append hprefix tailTrace_6531894
  have hstable : (prefixWord ++ tailWord_6531894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531894).length < 2 ^ (prefixWord ++ tailWord_6531894).sum := by decide
  have hdescent : baseEnd_6531894 < baseStart_6531894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531896 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_6531896 : Nat := 118140960795 + 6531896 * 2 ^ 59
def prefixEnd_6531896 : Nat := 4983230072969 + 3 ^ 40 * 6531896 * 2
def baseEnd_6531896 : Nat := 3354002233180481160560363

theorem tailTrace_6531896 : CollatzResearch.WordTrace tailWord_6531896 prefixEnd_6531896 3354002233180481160560363 := by
  unfold tailWord_6531896
  simp only [CollatzResearch.WordTrace]
  refine ⟨119118909572031912933859771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158825212762709217245146361 119118909572031912933859771)
  ·
    refine ⟨178678364358047869400789657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119118909572031912933859771 178678364358047869400789657)
    ·
      refine ⟨134008773268535902050592243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178678364358047869400789657 134008773268535902050592243)
      ·
        refine ⟨201013159902803853075888365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134008773268535902050592243 201013159902803853075888365)
        ·
          refine ⟨75379934963551444903458137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201013159902803853075888365 75379934963551444903458137)
          ·
            refine ⟨56534951222663583677593603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75379934963551444903458137 56534951222663583677593603)
            ·
              refine ⟨84802426833995375516390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56534951222663583677593603 84802426833995375516390405)
              ·
                refine ⟨15900455031374132909323201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84802426833995375516390405 15900455031374132909323201)
                ·
                  refine ⟨11925341273530599681992401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15900455031374132909323201 11925341273530599681992401)
                  ·
                    refine ⟨8944005955147949761494301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11925341273530599681992401 8944005955147949761494301)
                    ·
                      refine ⟨3354002233180481160560363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944005955147949761494301 3354002233180481160560363)
                      ·
                        rfl

theorem cell23_6531896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_6531896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531896 prefixEnd_6531896 := by exact prefixLift 6531896
  have htrace : WordTrace (prefixWord ++ tailWord_6531896) baseStart_6531896 baseEnd_6531896 := by
    simpa [prefixWord, tailWord_6531896, baseEnd_6531896] using wordTrace_append hprefix tailTrace_6531896
  have hstable : (prefixWord ++ tailWord_6531896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531896).length < 2 ^ (prefixWord ++ tailWord_6531896).sum := by decide
  have hdescent : baseEnd_6531896 < baseStart_6531896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531916 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 6]
def baseStart_6531916 : Nat := 118140960795 + 6531916 * 2 ^ 59
def prefixEnd_6531916 : Nat := 4983230072969 + 3 ^ 40 * 6531916 * 2
def baseEnd_6531916 : Nat := 372668055865952342478919

theorem tailTrace_6531916 : CollatzResearch.WordTrace tailWord_6531916 prefixEnd_6531916 372668055865952342478919 := by
  unfold tailWord_6531916
  simp only [CollatzResearch.WordTrace]
  refine ⟨119119274301995684641723801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158825699069327579522298401 119119274301995684641723801)
  ·
    refine ⟨89339455726496763481292851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119119274301995684641723801 89339455726496763481292851)
    ·
      refine ⟨134009183589745145221939277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89339455726496763481292851 134009183589745145221939277)
      ·
        refine ⟨50253443846154429458227229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134009183589745145221939277 50253443846154429458227229)
        ·
          refine ⟨18845041442307911046835211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50253443846154429458227229 18845041442307911046835211)
          ·
            refine ⟨28267562163461866570252817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18845041442307911046835211 28267562163461866570252817)
            ·
              refine ⟨21200671622596399927689613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28267562163461866570252817 21200671622596399927689613)
              ·
                refine ⟨7950251858473649972883605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21200671622596399927689613 7950251858473649972883605)
                ·
                  refine ⟨372668055865952342478919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7950251858473649972883605 372668055865952342478919)
                  ·
                    rfl

theorem cell23_6531916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_6531916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531916 prefixEnd_6531916 := by exact prefixLift 6531916
  have htrace : WordTrace (prefixWord ++ tailWord_6531916) baseStart_6531916 baseEnd_6531916 := by
    simpa [prefixWord, tailWord_6531916, baseEnd_6531916] using wordTrace_append hprefix tailTrace_6531916
  have hstable : (prefixWord ++ tailWord_6531916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531916).length < 2 ^ (prefixWord ++ tailWord_6531916).sum := by decide
  have hdescent : baseEnd_6531916 < baseStart_6531916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531950 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 6]
def baseStart_6531950 : Nat := 118140960795 + 6531950 * 2 ^ 59
def prefixEnd_6531950 : Nat := 4983230072969 + 3 ^ 40 * 6531950 * 2
def baseEnd_6531950 : Nat := 372669995681758216587235

theorem tailTrace_6531950 : CollatzResearch.WordTrace tailWord_6531950 prefixEnd_6531950 372669995681758216587235 := by
  unfold tailWord_6531950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29779973585733524136273163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158826525790578795393456869 29779973585733524136273163)
  ·
    refine ⟨44669960378600286204409745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29779973585733524136273163 44669960378600286204409745)
    ·
      refine ⟨33502470283950214653307309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44669960378600286204409745 33502470283950214653307309)
      ·
        refine ⟨12563426356481330494990241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33502470283950214653307309 12563426356481330494990241)
        ·
          refine ⟨9422569767360997871242681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12563426356481330494990241 9422569767360997871242681)
          ·
            refine ⟨7066927325520748403432011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9422569767360997871242681 7066927325520748403432011)
            ·
              refine ⟨10600390988281122605148017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066927325520748403432011 10600390988281122605148017)
              ·
                refine ⟨7950293241210841953861013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10600390988281122605148017 7950293241210841953861013)
                ·
                  refine ⟨372669995681758216587235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7950293241210841953861013 372669995681758216587235)
                  ·
                    rfl

theorem cell23_6531950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_6531950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531950 prefixEnd_6531950 := by exact prefixLift 6531950
  have htrace : WordTrace (prefixWord ++ tailWord_6531950) baseStart_6531950 baseEnd_6531950 := by
    simpa [prefixWord, tailWord_6531950, baseEnd_6531950] using wordTrace_append hprefix tailTrace_6531950
  have hstable : (prefixWord ++ tailWord_6531950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531950).length < 2 ^ (prefixWord ++ tailWord_6531950).sum := by decide
  have hdescent : baseEnd_6531950 < baseStart_6531950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531959 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 6]
def baseStart_6531959 : Nat := 118140960795 + 6531959 * 2 ^ 59
def prefixEnd_6531959 : Nat := 4983230072969 + 3 ^ 40 * 6531959 * 2
def baseEnd_6531959 : Nat := 1118011527487238138024191

theorem tailTrace_6531959 : CollatzResearch.WordTrace tailWord_6531959 prefixEnd_6531959 1118011527487238138024191 := by
  unfold tailWord_6531959
  simp only [CollatzResearch.WordTrace]
  refine ⟨238240116942835587627262931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158826744628557058418175287 238240116942835587627262931)
  ·
    refine ⟨357360175414253381440894397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238240116942835587627262931 357360175414253381440894397)
    ·
      refine ⟨134010065780345018040335399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357360175414253381440894397 134010065780345018040335399)
      ·
        refine ⟨201015098670517527060503099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134010065780345018040335399 201015098670517527060503099)
        ·
          refine ⟨301522648005776290590754649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201015098670517527060503099 301522648005776290590754649)
          ·
            refine ⟨226141986004332217943065987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301522648005776290590754649 226141986004332217943065987)
            ·
              refine ⟨339212979006498326914598981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226141986004332217943065987 339212979006498326914598981)
              ·
                refine ⟨63602433563718436296487309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339212979006498326914598981 63602433563718436296487309)
                ·
                  refine ⟨23850912586394413611182741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63602433563718436296487309 23850912586394413611182741)
                  ·
                    refine ⟨1118011527487238138024191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23850912586394413611182741 1118011527487238138024191)
                    ·
                      rfl

theorem cell23_6531959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_6531959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531959 prefixEnd_6531959 := by exact prefixLift 6531959
  have htrace : WordTrace (prefixWord ++ tailWord_6531959) baseStart_6531959 baseEnd_6531959 := by
    simpa [prefixWord, tailWord_6531959, baseEnd_6531959] using wordTrace_append hprefix tailTrace_6531959
  have hstable : (prefixWord ++ tailWord_6531959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531959).length < 2 ^ (prefixWord ++ tailWord_6531959).sum := by decide
  have hdescent : baseEnd_6531959 < baseStart_6531959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531994 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6531994 : Nat := 118140960795 + 6531994 * 2 ^ 59
def prefixEnd_6531994 : Nat := 4983230072969 + 3 ^ 40 * 6531994 * 2
def baseEnd_6531994 : Nat := 3354052554284621777134913

theorem tailTrace_6531994 : CollatzResearch.WordTrace tailWord_6531994 prefixEnd_6531994 3354052554284621777134913 := by
  unfold tailWord_6531994
  simp only [CollatzResearch.WordTrace]
  refine ⟨59560348374427197151196759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158827595665139192403191357 59560348374427197151196759)
  ·
    refine ⟨89340522561640795726795139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59560348374427197151196759 89340522561640795726795139)
    ·
      refine ⟨134010783842461193590192709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89340522561640795726795139 134010783842461193590192709)
      ·
        refine ⟨25127021970461473798161133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134010783842461193590192709 25127021970461473798161133)
        ·
          refine ⟨9422633238923052674310425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25127021970461473798161133 9422633238923052674310425)
          ·
            refine ⟨7066974929192289505732819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9422633238923052674310425 7066974929192289505732819)
            ·
              refine ⟨10600462393788434258599229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7066974929192289505732819 10600462393788434258599229)
              ·
                refine ⟨3975173397670662846974711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10600462393788434258599229 3975173397670662846974711)
                ·
                  refine ⟨5962760096505994270462067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975173397670662846974711 5962760096505994270462067)
                  ·
                    refine ⟨8944140144758991405693101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962760096505994270462067 8944140144758991405693101)
                    ·
                      refine ⟨3354052554284621777134913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944140144758991405693101 3354052554284621777134913)
                      ·
                        rfl

theorem cell23_6531994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6531994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531994 prefixEnd_6531994 := by exact prefixLift 6531994
  have htrace : WordTrace (prefixWord ++ tailWord_6531994) baseStart_6531994 baseEnd_6531994 := by
    simpa [prefixWord, tailWord_6531994, baseEnd_6531994] using wordTrace_append hprefix tailTrace_6531994
  have hstable : (prefixWord ++ tailWord_6531994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531994).length < 2 ^ (prefixWord ++ tailWord_6531994).sum := by decide
  have hdescent : baseEnd_6531994 < baseStart_6531994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532003 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 3]
def baseStart_6532003 : Nat := 118140960795 + 6532003 * 2 ^ 59
def prefixEnd_6532003 : Nat := 4983230072969 + 3 ^ 40 * 6532003 * 2
def baseEnd_6532003 : Nat := 3354057175610512241922371

theorem tailTrace_6532003 : CollatzResearch.WordTrace tailWord_6532003 prefixEnd_6532003 3354057175610512241922371 := by
  unfold tailWord_6532003
  simp only [CollatzResearch.WordTrace]
  refine ⟨238241721754676183141864663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158827814503117455427909775 238241721754676183141864663)
  ·
    refine ⟨357362582632014274712796995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238241721754676183141864663 357362582632014274712796995)
    ·
      refine ⟨536043873948021412069195493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357362582632014274712796995 536043873948021412069195493)
      ·
        refine ⟨100508226365254014762974155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536043873948021412069195493 100508226365254014762974155)
        ·
          refine ⟨150762339547881022144461233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100508226365254014762974155 150762339547881022144461233)
          ·
            refine ⟨113071754660910766608345925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150762339547881022144461233 113071754660910766608345925)
            ·
              refine ⟨21200953998920768739064861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113071754660910766608345925 21200953998920768739064861)
              ·
                refine ⟨7950357749595288277149323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21200953998920768739064861 7950357749595288277149323)
                ·
                  refine ⟨11925536624392932415723985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950357749595288277149323 11925536624392932415723985)
                  ·
                    refine ⟨8944152468294699311792989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11925536624392932415723985 8944152468294699311792989)
                    ·
                      refine ⟨3354057175610512241922371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944152468294699311792989 3354057175610512241922371)
                      ·
                        rfl

theorem cell23_6532003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_6532003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532003 prefixEnd_6532003 := by exact prefixLift 6532003
  have htrace : WordTrace (prefixWord ++ tailWord_6532003) baseStart_6532003 baseEnd_6532003 := by
    simpa [prefixWord, tailWord_6532003, baseEnd_6532003] using wordTrace_append hprefix tailTrace_6532003
  have hstable : (prefixWord ++ tailWord_6532003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532003).length < 2 ^ (prefixWord ++ tailWord_6532003).sum := by decide
  have hdescent : baseEnd_6532003 < baseStart_6532003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532020 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6532020 : Nat := 118140960795 + 6532020 * 2 ^ 59
def prefixEnd_6532020 : Nat := 4983230072969 + 3 ^ 40 * 6532020 * 2
def baseEnd_6532020 : Nat := 3354065904781638675409793

theorem tailTrace_6532020 : CollatzResearch.WordTrace tailWord_6532020 prefixEnd_6532020 3354065904781638675409793 := by
  unfold tailWord_6532020
  simp only [CollatzResearch.WordTrace]
  refine ⟨119121170897807297522616757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158828227863743063363489009 119121170897807297522616757)
  ·
    refine ⟨11167609771669434142745321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119121170897807297522616757 11167609771669434142745321)
    ·
      refine ⟨8375707328752075607058991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11167609771669434142745321 8375707328752075607058991)
      ·
        refine ⟨12563560993128113410588487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375707328752075607058991 12563560993128113410588487)
        ·
          refine ⟨18845341489692170115882731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12563560993128113410588487 18845341489692170115882731)
          ·
            refine ⟨28268012234538255173824097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18845341489692170115882731 28268012234538255173824097)
            ·
              refine ⟨21201009175903691380368073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28268012234538255173824097 21201009175903691380368073)
              ·
                refine ⟨15900756881927768535276055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21201009175903691380368073 15900756881927768535276055)
                ·
                  refine ⟨23851135322891652802914083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15900756881927768535276055 23851135322891652802914083)
                  ·
                    refine ⟨35776702984337479204371125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23851135322891652802914083 35776702984337479204371125)
                    ·
                      refine ⟨3354065904781638675409793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35776702984337479204371125 3354065904781638675409793)
                      ·
                        rfl

theorem cell23_6532020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6532020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532020 prefixEnd_6532020 := by exact prefixLift 6532020
  have htrace : WordTrace (prefixWord ++ tailWord_6532020) baseStart_6532020 baseEnd_6532020 := by
    simpa [prefixWord, tailWord_6532020, baseEnd_6532020] using wordTrace_append hprefix tailTrace_6532020
  have hstable : (prefixWord ++ tailWord_6532020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532020).length < 2 ^ (prefixWord ++ tailWord_6532020).sum := by decide
  have hdescent : baseEnd_6532020 < baseStart_6532020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532038 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6532038 : Nat := 118140960795 + 6532038 * 2 ^ 59
def prefixEnd_6532038 : Nat := 4983230072969 + 3 ^ 40 * 6532038 * 2
def baseEnd_6532038 : Nat := 3354075147433419604984711

theorem tailTrace_6532038 : CollatzResearch.WordTrace tailWord_6532038 prefixEnd_6532038 3354075147433419604984711 := by
  unfold tailWord_6532038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7445093697173418253730899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158828665539699589412925845 7445093697173418253730899)
  ·
    refine ⟨11167640545760127380596349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7445093697173418253730899 11167640545760127380596349)
    ·
      refine ⟨4187865204660047767723631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11167640545760127380596349 4187865204660047767723631)
      ·
        refine ⟨6281797806990071651585447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187865204660047767723631 6281797806990071651585447)
        ·
          refine ⟨9422696710485107477378171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281797806990071651585447 9422696710485107477378171)
          ·
            refine ⟨14134045065727661216067257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422696710485107477378171 14134045065727661216067257)
            ·
              refine ⟨10600533799295745912050443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14134045065727661216067257 10600533799295745912050443)
              ·
                refine ⟨15900800698943618868075665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10600533799295745912050443 15900800698943618868075665)
                ·
                  refine ⟨11925600524207714151056749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15900800698943618868075665 11925600524207714151056749)
                  ·
                    refine ⟨4472100196577892806646281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11925600524207714151056749 4472100196577892806646281)
                    ·
                      refine ⟨3354075147433419604984711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472100196577892806646281 3354075147433419604984711)
                      ·
                        rfl

theorem cell23_6532038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6532038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532038 prefixEnd_6532038 := by exact prefixLift 6532038
  have htrace : WordTrace (prefixWord ++ tailWord_6532038) baseStart_6532038 baseEnd_6532038 := by
    simpa [prefixWord, tailWord_6532038, baseEnd_6532038] using wordTrace_append hprefix tailTrace_6532038
  have hstable : (prefixWord ++ tailWord_6532038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532038).length < 2 ^ (prefixWord ++ tailWord_6532038).sum := by decide
  have hdescent : baseEnd_6532038 < baseStart_6532038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532050 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6532050 : Nat := 118140960795 + 6532050 * 2 ^ 59
def prefixEnd_6532050 : Nat := 4983230072969 + 3 ^ 40 * 6532050 * 2
def baseEnd_6532050 : Nat := 3354081309201273558034655

theorem tailTrace_6532050 : CollatzResearch.WordTrace tailWord_6532050 prefixEnd_6532050 3354081309201273558034655 := by
  unfold tailWord_6532050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59560858996376477542206401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158828957323670606779217069 59560858996376477542206401)
  ·
    refine ⟨44670644247282358156654801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59560858996376477542206401 44670644247282358156654801)
    ·
      refine ⟨33502983185461768617491101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44670644247282358156654801 33502983185461768617491101)
      ·
        refine ⟨12563618694548163231559163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33502983185461768617491101 12563618694548163231559163)
        ·
          refine ⟨18845428041822244847338745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12563618694548163231559163 18845428041822244847338745)
          ·
            refine ⟨14134071031366683635504059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18845428041822244847338745 14134071031366683635504059)
            ·
              refine ⟨21201106547050025453256089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14134071031366683635504059 21201106547050025453256089)
              ·
                refine ⟨15900829910287519089942067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21201106547050025453256089 15900829910287519089942067)
                ·
                  refine ⟨23851244865431278634913101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15900829910287519089942067 23851244865431278634913101)
                  ·
                    refine ⟨8944216824536729488092413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23851244865431278634913101 8944216824536729488092413)
                    ·
                      refine ⟨3354081309201273558034655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944216824536729488092413 3354081309201273558034655)
                      ·
                        rfl

theorem cell23_6532050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6532050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532050 prefixEnd_6532050 := by exact prefixLift 6532050
  have htrace : WordTrace (prefixWord ++ tailWord_6532050) baseStart_6532050 baseEnd_6532050 := by
    simpa [prefixWord, tailWord_6532050, baseEnd_6532050] using wordTrace_append hprefix tailTrace_6532050
  have hstable : (prefixWord ++ tailWord_6532050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532050).length < 2 ^ (prefixWord ++ tailWord_6532050).sum := by decide
  have hdescent : baseEnd_6532050 < baseStart_6532050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532054 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6532054 : Nat := 118140960795 + 6532054 * 2 ^ 59
def prefixEnd_6532054 : Nat := 4983230072969 + 3 ^ 40 * 6532054 * 2
def baseEnd_6532054 : Nat := 3354083363123891542384637

theorem tailTrace_6532054 : CollatzResearch.WordTrace tailWord_6532054 prefixEnd_6532054 3354083363123891542384637 := by
  unfold tailWord_6532054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890223867343213678248201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158829054584994279234647477 14890223867343213678248201)
  ·
    refine ⟨11167667900507410258686151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14890223867343213678248201 11167667900507410258686151)
    ·
      refine ⟨16751501850761115388029227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11167667900507410258686151 16751501850761115388029227)
      ·
        refine ⟨25127252776141673082043841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16751501850761115388029227 25127252776141673082043841)
        ·
          refine ⟨18845439582106254811532881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25127252776141673082043841 18845439582106254811532881)
          ·
            refine ⟨14134079686579691108649661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18845439582106254811532881 14134079686579691108649661)
            ·
              refine ⟨5300279882467384165743623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14134079686579691108649661 5300279882467384165743623)
              ·
                refine ⟨7950419823701076248615435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300279882467384165743623 7950419823701076248615435)
                ·
                  refine ⟨11925629735551614372923153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950419823701076248615435 11925629735551614372923153)
                  ·
                    refine ⟨8944222301663710779692365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11925629735551614372923153 8944222301663710779692365)
                    ·
                      refine ⟨3354083363123891542384637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944222301663710779692365 3354083363123891542384637)
                      ·
                        rfl

theorem cell23_6532054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6532054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532054 prefixEnd_6532054 := by exact prefixLift 6532054
  have htrace : WordTrace (prefixWord ++ tailWord_6532054) baseStart_6532054 baseEnd_6532054 := by
    simpa [prefixWord, tailWord_6532054, baseEnd_6532054] using wordTrace_append hprefix tailTrace_6532054
  have hstable : (prefixWord ++ tailWord_6532054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532054).length < 2 ^ (prefixWord ++ tailWord_6532054).sum := by decide
  have hdescent : baseEnd_6532054 < baseStart_6532054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532130 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 5]
def baseStart_6532130 : Nat := 118140960795 + 6532130 * 2 ^ 59
def prefixEnd_6532130 : Nat := 4983230072969 + 3 ^ 40 * 6532130 * 2
def baseEnd_6532130 : Nat := 372680265294848138337143

theorem tailTrace_6532130 : CollatzResearch.WordTrace tailWord_6532130 prefixEnd_6532130 372680265294848138337143 := by
  unfold tailWord_6532130
  simp only [CollatzResearch.WordTrace]
  refine ⟨59561588456304020957934461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158830902550144055887825229 59561588456304020957934461)
  ·
    refine ⟨22335595671114007859225423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59561588456304020957934461 22335595671114007859225423)
    ·
      refine ⟨33503393506671011788838135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22335595671114007859225423 33503393506671011788838135)
      ·
        refine ⟨50255090260006517683257203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33503393506671011788838135 50255090260006517683257203)
        ·
          refine ⟨75382635390009776524885805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50255090260006517683257203 75382635390009776524885805)
          ·
            refine ⟨28268488271253666196832177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75382635390009776524885805 28268488271253666196832177)
            ·
              refine ⟨21201366203440249647624133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28268488271253666196832177 21201366203440249647624133)
              ·
                refine ⟨3975256163145046808929525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21201366203440249647624133 3975256163145046808929525)
                ·
                  refine ⟨372680265294848138337143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975256163145046808929525 372680265294848138337143)
                  ·
                    rfl

theorem cell23_6532130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_6532130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532130 prefixEnd_6532130 := by exact prefixLift 6532130
  have htrace : WordTrace (prefixWord ++ tailWord_6532130) baseStart_6532130 baseEnd_6532130 := by
    simpa [prefixWord, tailWord_6532130, baseEnd_6532130] using wordTrace_append hprefix tailTrace_6532130
  have hstable : (prefixWord ++ tailWord_6532130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532130).length < 2 ^ (prefixWord ++ tailWord_6532130).sum := by decide
  have hdescent : baseEnd_6532130 < baseStart_6532130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532163 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4]
def baseStart_6532163 : Nat := 118140960795 + 6532163 * 2 ^ 59
def prefixEnd_6532163 : Nat := 4983230072969 + 3 ^ 40 * 6532163 * 2
def baseEnd_6532163 : Nat := 3354139332515231615921635

theorem tailTrace_6532163 : CollatzResearch.WordTrace tailWord_6532163 prefixEnd_6532163 3354139332515231615921635 := by
  unfold tailWord_6532163
  simp only [CollatzResearch.WordTrace]
  refine ⟨238247557434096530467689143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158831704956064353645126095 238247557434096530467689143)
  ·
    refine ⟨357371336151144795701533715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238247557434096530467689143 357371336151144795701533715)
    ·
      refine ⟨536057004226717193552300573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357371336151144795701533715 536057004226717193552300573)
      ·
        refine ⟨201021376585018947582112715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536057004226717193552300573 201021376585018947582112715)
        ·
          refine ⟨301532064877528421373169073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201021376585018947582112715 301532064877528421373169073)
          ·
            refine ⟨226149048658146316029876805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301532064877528421373169073 226149048658146316029876805)
            ·
              refine ⟨42402946623402434255601901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226149048658146316029876805 42402946623402434255601901)
              ·
                refine ⟨15901104983775912845850713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42402946623402434255601901 15901104983775912845850713)
                ·
                  refine ⟨11925828737831934634388035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15901104983775912845850713 11925828737831934634388035)
                  ·
                    refine ⟨17888743106747901951582053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11925828737831934634388035 17888743106747901951582053)
                    ·
                      refine ⟨3354139332515231615921635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17888743106747901951582053 3354139332515231615921635)
                      ·
                        rfl

theorem cell23_6532163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_6532163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532163 prefixEnd_6532163 := by exact prefixLift 6532163
  have htrace : WordTrace (prefixWord ++ tailWord_6532163) baseStart_6532163 baseEnd_6532163 := by
    simpa [prefixWord, tailWord_6532163, baseEnd_6532163] using wordTrace_append hprefix tailTrace_6532163
  have hstable : (prefixWord ++ tailWord_6532163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532163).length < 2 ^ (prefixWord ++ tailWord_6532163).sum := by decide
  have hdescent : baseEnd_6532163 < baseStart_6532163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532176 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_6532176 : Nat := 118140960795 + 6532176 * 2 ^ 59
def prefixEnd_6532176 : Nat := 4983230072969 + 3 ^ 40 * 6532176 * 2
def baseEnd_6532176 : Nat := 3354146007763740065059075

theorem tailTrace_6532176 : CollatzResearch.WordTrace tailWord_6532176 prefixEnd_6532176 3354146007763740065059075 := by
  unfold tailWord_6532176
  simp only [CollatzResearch.WordTrace]
  refine ⟨119124015791524716843956191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158832021055366289125274921 119124015791524716843956191)
  ·
    refine ⟨178686023687287075265934287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119124015791524716843956191 178686023687287075265934287)
    ·
      refine ⟨268029035530930612898901431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178686023687287075265934287 268029035530930612898901431)
      ·
        refine ⟨402043553296395919348352147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268029035530930612898901431 402043553296395919348352147)
        ·
          refine ⟨603065329944593879022528221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402043553296395919348352147 603065329944593879022528221)
          ·
            refine ⟨226149498729222704633448083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603065329944593879022528221 226149498729222704633448083)
            ·
              refine ⟨339224248093834056950172125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226149498729222704633448083 339224248093834056950172125)
              ·
                refine ⟨127209093035187771356314547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339224248093834056950172125 127209093035187771356314547)
                ·
                  refine ⟨190813639552781657034471821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127209093035187771356314547 190813639552781657034471821)
                  ·
                    refine ⟨71555114832293121387926933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190813639552781657034471821 71555114832293121387926933)
                    ·
                      refine ⟨3354146007763740065059075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71555114832293121387926933 3354146007763740065059075)
                      ·
                        rfl

theorem cell23_6532176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_6532176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532176 prefixEnd_6532176 := by exact prefixLift 6532176
  have htrace : WordTrace (prefixWord ++ tailWord_6532176) baseStart_6532176 baseEnd_6532176 := by
    simpa [prefixWord, tailWord_6532176, baseEnd_6532176] using wordTrace_append hprefix tailTrace_6532176
  have hstable : (prefixWord ++ tailWord_6532176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532176).length < 2 ^ (prefixWord ++ tailWord_6532176).sum := by decide
  have hdescent : baseEnd_6532176 < baseStart_6532176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532180 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_6532180 : Nat := 118140960795 + 6532180 * 2 ^ 59
def prefixEnd_6532180 : Nat := 4983230072969 + 3 ^ 40 * 6532180 * 2
def baseEnd_6532180 : Nat := 3354148061686358049409057

theorem tailTrace_6532180 : CollatzResearch.WordTrace tailWord_6532180 prefixEnd_6532180 3354148061686358049409057 := by
  unfold tailWord_6532180
  simp only [CollatzResearch.WordTrace]
  refine ⟨119124088737517471185528997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158832118316689961580705329 119124088737517471185528997)
  ·
    refine ⟨22335766638284525847286687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119124088737517471185528997 22335766638284525847286687)
    ·
      refine ⟨33503649957426788770930031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22335766638284525847286687 33503649957426788770930031)
      ·
        refine ⟨50255474936140183156395047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33503649957426788770930031 50255474936140183156395047)
        ·
          refine ⟨75383212404210274734592571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50255474936140183156395047 75383212404210274734592571)
          ·
            refine ⟨113074818606315412101888857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75383212404210274734592571 113074818606315412101888857)
            ·
              refine ⟨84806113954736559076416643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113074818606315412101888857 84806113954736559076416643)
              ·
                refine ⟨127209170932104838614624965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84806113954736559076416643 127209170932104838614624965)
                ·
                  refine ⟨23851719549769657240242181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127209170932104838614624965 23851719549769657240242181)
                  ·
                    refine ⟨4472197415581810732545409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23851719549769657240242181 4472197415581810732545409)
                    ·
                      refine ⟨3354148061686358049409057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472197415581810732545409 3354148061686358049409057)
                      ·
                        rfl

theorem cell23_6532180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_6532180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532180 prefixEnd_6532180 := by exact prefixLift 6532180
  have htrace : WordTrace (prefixWord ++ tailWord_6532180) baseStart_6532180 baseEnd_6532180 := by
    simpa [prefixWord, tailWord_6532180, baseEnd_6532180] using wordTrace_append hprefix tailTrace_6532180
  have hstable : (prefixWord ++ tailWord_6532180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532180).length < 2 ^ (prefixWord ++ tailWord_6532180).sum := by decide
  have hdescent : baseEnd_6532180 < baseStart_6532180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532217 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6532217 : Nat := 118140960795 + 6532217 * 2 ^ 59
def prefixEnd_6532217 : Nat := 4983230072969 + 3 ^ 40 * 6532217 * 2
def baseEnd_6532217 : Nat := 3354167060470574404646387

theorem tailTrace_6532217 : CollatzResearch.WordTrace tailWord_6532217 prefixEnd_6532217 3354167060470574404646387 := by
  unfold tailWord_6532217
  simp only [CollatzResearch.WordTrace]
  refine ⟨238249526975900897690154905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158833017983933931793436603 238249526975900897690154905)
  ·
    refine ⟨178687145231925673267616179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238249526975900897690154905 178687145231925673267616179)
    ·
      refine ⟨268030717847888509901424269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178687145231925673267616179 268030717847888509901424269)
      ·
        refine ⟨100511519192958191213034101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268030717847888509901424269 100511519192958191213034101)
        ·
          refine ⟨9422954924339830426221947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100511519192958191213034101 9422954924339830426221947)
          ·
            refine ⟨14134432386509745639332921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422954924339830426221947 14134432386509745639332921)
            ·
              refine ⟨10600824289882309229499691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14134432386509745639332921 10600824289882309229499691)
              ·
                refine ⟨15901236434823463844249537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10600824289882309229499691 15901236434823463844249537)
                ·
                  refine ⟨11925927326117597883187153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15901236434823463844249537 11925927326117597883187153)
                  ·
                    refine ⟨8944445494588198412390365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11925927326117597883187153 8944445494588198412390365)
                    ·
                      refine ⟨3354167060470574404646387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944445494588198412390365 3354167060470574404646387)
                      ·
                        rfl

theorem cell23_6532217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6532217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532217 prefixEnd_6532217 := by exact prefixLift 6532217
  have htrace : WordTrace (prefixWord ++ tailWord_6532217) baseStart_6532217 baseEnd_6532217 := by
    simpa [prefixWord, tailWord_6532217, baseEnd_6532217] using wordTrace_append hprefix tailTrace_6532217
  have hstable : (prefixWord ++ tailWord_6532217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532217).length < 2 ^ (prefixWord ++ tailWord_6532217).sum := by decide
  have hdescent : baseEnd_6532217 < baseStart_6532217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532240 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2]
def baseStart_6532240 : Nat := 118140960795 + 6532240 * 2 ^ 59
def prefixEnd_6532240 : Nat := 4983230072969 + 3 ^ 40 * 6532240 * 2
def baseEnd_6532240 : Nat := 3354178870525627814658781

theorem tailTrace_6532240 : CollatzResearch.WordTrace tailWord_6532240 prefixEnd_6532240 3354178870525627814658781 := by
  unfold tailWord_6532240
  simp only [CollatzResearch.WordTrace]
  refine ⟨119125182927408786309121087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158833577236545048412161449 119125182927408786309121087)
  ·
    refine ⟨178687774391113179463681631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119125182927408786309121087 178687774391113179463681631)
    ·
      refine ⟨268031661586669769195522447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178687774391113179463681631 268031661586669769195522447)
      ·
        refine ⟨402047492380004653793283671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268031661586669769195522447 402047492380004653793283671)
        ·
          refine ⟨603071238570006980689925507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402047492380004653793283671 603071238570006980689925507)
          ·
            refine ⟨904606857855010471034888261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603071238570006980689925507 904606857855010471034888261)
            ·
              refine ⟨169613785847814463319041549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904606857855010471034888261 169613785847814463319041549)
              ·
                refine ⟨63605169692930423744640581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169613785847814463319041549 63605169692930423744640581)
                ·
                  refine ⟨11925969317424454452120109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63605169692930423744640581 11925969317424454452120109)
                  ·
                    refine ⟨4472238494034170419545041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11925969317424454452120109 4472238494034170419545041)
                    ·
                      refine ⟨3354178870525627814658781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472238494034170419545041 3354178870525627814658781)
                      ·
                        rfl

theorem cell23_6532240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 3, 2].length) (baseStart_6532240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532240 prefixEnd_6532240 := by exact prefixLift 6532240
  have htrace : WordTrace (prefixWord ++ tailWord_6532240) baseStart_6532240 baseEnd_6532240 := by
    simpa [prefixWord, tailWord_6532240, baseEnd_6532240] using wordTrace_append hprefix tailTrace_6532240
  have hstable : (prefixWord ++ tailWord_6532240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532240).length < 2 ^ (prefixWord ++ tailWord_6532240).sum := by decide
  have hdescent : baseEnd_6532240 < baseStart_6532240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532250 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_6532250 : Nat := 118140960795 + 6532250 * 2 ^ 59
def prefixEnd_6532250 : Nat := 4983230072969 + 3 ^ 40 * 6532250 * 2
def baseEnd_6532250 : Nat := 1118061335110724258511245

theorem tailTrace_6532250 : CollatzResearch.WordTrace tailWord_6532250 prefixEnd_6532250 1118061335110724258511245 := by
  unfold tailWord_6532250
  simp only [CollatzResearch.WordTrace]
  refine ⟨59562682646195336081526551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158833820389854229550737469 59562682646195336081526551)
  ·
    refine ⟨89344023969293004122289827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59562682646195336081526551 89344023969293004122289827)
    ·
      refine ⟨134016035953939506183434741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89344023969293004122289827 134016035953939506183434741)
      ·
        refine ⟨12564003370681828704697007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134016035953939506183434741 12564003370681828704697007)
        ·
          refine ⟨18846005056022743057045511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12564003370681828704697007 18846005056022743057045511)
          ·
            refine ⟨28269007584034114585568267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18846005056022743057045511 28269007584034114585568267)
            ·
              refine ⟨42403511376051171878352401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28269007584034114585568267 42403511376051171878352401)
              ·
                refine ⟨31802633532038378908764301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42403511376051171878352401 31802633532038378908764301)
                ·
                  refine ⟨11925987574514392090786613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31802633532038378908764301 11925987574514392090786613)
                  ·
                    refine ⟨1118061335110724258511245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11925987574514392090786613 1118061335110724258511245)
                    ·
                      rfl

theorem cell23_6532250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_6532250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532250 prefixEnd_6532250 := by exact prefixLift 6532250
  have htrace : WordTrace (prefixWord ++ tailWord_6532250) baseStart_6532250 baseEnd_6532250 := by
    simpa [prefixWord, tailWord_6532250, baseEnd_6532250] using wordTrace_append hprefix tailTrace_6532250
  have hstable : (prefixWord ++ tailWord_6532250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532250).length < 2 ^ (prefixWord ++ tailWord_6532250).sum := by decide
  have hdescent : baseEnd_6532250 < baseStart_6532250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532274 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_6532274 : Nat := 118140960795 + 6532274 * 2 ^ 59
def prefixEnd_6532274 : Nat := 4983230072969 + 3 ^ 40 * 6532274 * 2
def baseEnd_6532274 : Nat := 3354196328867880681633625

theorem tailTrace_6532274 : CollatzResearch.WordTrace tailWord_6532274 prefixEnd_6532274 3354196328867880681633625 := by
  unfold tailWord_6532274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59562901484173599106244969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158834403957796264283319917 59562901484173599106244969)
  ·
    refine ⟨44672176113130199329683727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59562901484173599106244969 44672176113130199329683727)
    ·
      refine ⟨67008264169695298994525591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44672176113130199329683727 67008264169695298994525591)
      ·
        refine ⟨100512396254542948491788387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67008264169695298994525591 100512396254542948491788387)
        ·
          refine ⟨150768594381814422737682581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100512396254542948491788387 150768594381814422737682581)
          ·
            refine ⟨7067277861647551065828871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150768594381814422737682581 7067277861647551065828871)
            ·
              refine ⟨10600916792471326598743307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067277861647551065828871 10600916792471326598743307)
              ·
                refine ⟨15901375188706989898114961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10600916792471326598743307 15901375188706989898114961)
                ·
                  refine ⟨11926031391530242423586221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15901375188706989898114961 11926031391530242423586221)
                  ·
                    refine ⟨4472261771823840908844833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11926031391530242423586221 4472261771823840908844833)
                    ·
                      refine ⟨3354196328867880681633625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472261771823840908844833 3354196328867880681633625)
                      ·
                        rfl

theorem cell23_6532274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_6532274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532274 prefixEnd_6532274 := by exact prefixLift 6532274
  have htrace : WordTrace (prefixWord ++ tailWord_6532274) baseStart_6532274 baseEnd_6532274 := by
    simpa [prefixWord, tailWord_6532274, baseEnd_6532274] using wordTrace_append hprefix tailTrace_6532274
  have hstable : (prefixWord ++ tailWord_6532274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532274).length < 2 ^ (prefixWord ++ tailWord_6532274).sum := by decide
  have hdescent : baseEnd_6532274 < baseStart_6532274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532283 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_6532283 : Nat := 118140960795 + 6532283 * 2 ^ 59
def prefixEnd_6532283 : Nat := 4983230072969 + 3 ^ 40 * 6532283 * 2
def baseEnd_6532283 : Nat := 3354200950193771146421083

theorem tailTrace_6532283 : CollatzResearch.WordTrace tailWord_6532283 prefixEnd_6532283 3354200950193771146421083 := by
  unfold tailWord_6532283
  simp only [CollatzResearch.WordTrace]
  refine ⟨238251934193661790962057503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158834622795774527308038335 238251934193661790962057503)
  ·
    refine ⟨357377901290492686443086255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238251934193661790962057503 357377901290492686443086255)
    ·
      refine ⟨536066851935739029664629383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357377901290492686443086255 536066851935739029664629383)
      ·
        refine ⟨804100277903608544496944075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536066851935739029664629383 804100277903608544496944075)
        ·
          refine ⟨1206150416855412816745416113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804100277903608544496944075 1206150416855412816745416113)
          ·
            refine ⟨904612812641559612559062085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206150416855412816745416113 904612812641559612559062085)
            ·
              refine ⟨169614902370292427354824141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904612812641559612559062085 169614902370292427354824141)
              ·
                refine ⟨63605588388859660258059053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169614902370292427354824141 63605588388859660258059053)
                ·
                  refine ⟨23852095645822372596772145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63605588388859660258059053 23852095645822372596772145)
                  ·
                    refine ⟨17889071734366779447579109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23852095645822372596772145 17889071734366779447579109)
                    ·
                      refine ⟨3354200950193771146421083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17889071734366779447579109 3354200950193771146421083)
                      ·
                        rfl

theorem cell23_6532283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_6532283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532283 prefixEnd_6532283 := by exact prefixLift 6532283
  have htrace : WordTrace (prefixWord ++ tailWord_6532283) baseStart_6532283 baseEnd_6532283 := by
    simpa [prefixWord, tailWord_6532283, baseEnd_6532283] using wordTrace_append hprefix tailTrace_6532283
  have hstable : (prefixWord ++ tailWord_6532283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532283).length < 2 ^ (prefixWord ++ tailWord_6532283).sum := by decide
  have hdescent : baseEnd_6532283 < baseStart_6532283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532284 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_6532284 : Nat := 118140960795 + 6532284 * 2 ^ 59
def prefixEnd_6532284 : Nat := 4983230072969 + 3 ^ 40 * 6532284 * 2
def baseEnd_6532284 : Nat := 1118067154558141880836193

theorem tailTrace_6532284 : CollatzResearch.WordTrace tailWord_6532284 prefixEnd_6532284 1118067154558141880836193 := by
  unfold tailWord_6532284
  simp only [CollatzResearch.WordTrace]
  refine ⟨119125985333329084066421953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158834647111105445421895937 119125985333329084066421953)
  ·
    refine ⟨89344488999996813049816465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119125985333329084066421953 89344488999996813049816465)
    ·
      refine ⟨67008366749997609787362349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89344488999996813049816465 67008366749997609787362349)
      ·
        refine ⟨25128137531249103670260881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67008366749997609787362349 25128137531249103670260881)
        ·
          refine ⟨18846103148436827752695661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25128137531249103670260881 18846103148436827752695661)
          ·
            refine ⟨7067288680663810407260873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18846103148436827752695661 7067288680663810407260873)
            ·
              refine ⟨5300466510497857805445655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7067288680663810407260873 5300466510497857805445655)
              ·
                refine ⟨7950699765746786708168483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300466510497857805445655 7950699765746786708168483)
                ·
                  refine ⟨11926049648620180062252725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950699765746786708168483 11926049648620180062252725)
                  ·
                    refine ⟨1118067154558141880836193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11926049648620180062252725 1118067154558141880836193)
                    ·
                      rfl

theorem cell23_6532284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_6532284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532284 prefixEnd_6532284 := by exact prefixLift 6532284
  have htrace : WordTrace (prefixWord ++ tailWord_6532284) baseStart_6532284 baseEnd_6532284 := by
    simpa [prefixWord, tailWord_6532284, baseEnd_6532284] using wordTrace_append hprefix tailTrace_6532284
  have hstable : (prefixWord ++ tailWord_6532284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532284).length < 2 ^ (prefixWord ++ tailWord_6532284).sum := by decide
  have hdescent : baseEnd_6532284 < baseStart_6532284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532287 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 1, 1, 4]
def baseStart_6532287 : Nat := 118140960795 + 6532287 * 2 ^ 59
def prefixEnd_6532287 : Nat := 4983230072969 + 3 ^ 40 * 6532287 * 2
def baseEnd_6532287 : Nat := 3354203004116389130771065

theorem tailTrace_6532287 : CollatzResearch.WordTrace tailWord_6532287 prefixEnd_6532287 3354203004116389130771065 := by
  unfold tailWord_6532287
  simp only [CollatzResearch.WordTrace]
  refine ⟨238252080085647299645203115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158834720057098199763468743 238252080085647299645203115)
  ·
    refine ⟨357378120128470949467804673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238252080085647299645203115 357378120128470949467804673)
    ·
      refine ⟨268033590096353212100853505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357378120128470949467804673 268033590096353212100853505)
      ·
        refine ⟨201025192572264909075640129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268033590096353212100853505 201025192572264909075640129)
        ·
          refine ⟨150768894429198681806730097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201025192572264909075640129 150768894429198681806730097)
          ·
            refine ⟨113076670821899011355047573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150768894429198681806730097 113076670821899011355047573)
            ·
              refine ⟨5300468944776516157267855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113076670821899011355047573 5300468944776516157267855)
              ·
                refine ⟨7950703417164774235901783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5300468944776516157267855 7950703417164774235901783)
                ·
                  refine ⟨11926055125747161353852675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950703417164774235901783 11926055125747161353852675)
                  ·
                    refine ⟨17889082688620742030779013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11926055125747161353852675 17889082688620742030779013)
                    ·
                      refine ⟨3354203004116389130771065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17889082688620742030779013 3354203004116389130771065)
                      ·
                        rfl

theorem cell23_6532287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_6532287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532287 prefixEnd_6532287 := by exact prefixLift 6532287
  have htrace : WordTrace (prefixWord ++ tailWord_6532287) baseStart_6532287 baseEnd_6532287 := by
    simpa [prefixWord, tailWord_6532287, baseEnd_6532287] using wordTrace_append hprefix tailTrace_6532287
  have hstable : (prefixWord ++ tailWord_6532287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532287).length < 2 ^ (prefixWord ++ tailWord_6532287).sum := by decide
  have hdescent : baseEnd_6532287 < baseStart_6532287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532317 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_6532317 : Nat := 118140960795 + 6532317 * 2 ^ 59
def prefixEnd_6532317 : Nat := 4983230072969 + 3 ^ 40 * 6532317 * 2
def baseEnd_6532317 : Nat := 3354218408536024013395927

theorem tailTrace_6532317 : CollatzResearch.WordTrace tailWord_6532317 prefixEnd_6532317 3354218408536024013395927 := by
  unfold tailWord_6532317
  simp only [CollatzResearch.WordTrace]
  refine ⟨238253174275538614768795205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158835449517025743179196803 238253174275538614768795205)
  ·
    refine ⟨44672470176663490269149101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238253174275538614768795205 44672470176663490269149101)
    ·
      refine ⟨16752176316248808850930913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44672470176663490269149101 16752176316248808850930913)
      ·
        refine ⟨12564132237186606638198185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16752176316248808850930913 12564132237186606638198185)
        ·
          refine ⟨9423099177889954978648639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12564132237186606638198185 9423099177889954978648639)
          ·
            refine ⟨14134648766834932467972959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423099177889954978648639 14134648766834932467972959)
            ·
              refine ⟨21201973150252398701959439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14134648766834932467972959 21201973150252398701959439)
              ·
                refine ⟨31802959725378598052939159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21201973150252398701959439 31802959725378598052939159)
                ·
                  refine ⟨47704439588067897079408739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31802959725378598052939159 47704439588067897079408739)
                  ·
                    refine ⟨71556659382101845619113109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47704439588067897079408739 71556659382101845619113109)
                    ·
                      refine ⟨3354218408536024013395927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71556659382101845619113109 3354218408536024013395927)
                      ·
                        rfl

theorem cell23_6532317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_6532317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532317 prefixEnd_6532317 := by exact prefixLift 6532317
  have htrace : WordTrace (prefixWord ++ tailWord_6532317) baseStart_6532317 baseEnd_6532317 := by
    simpa [prefixWord, tailWord_6532317, baseEnd_6532317] using wordTrace_append hprefix tailTrace_6532317
  have hstable : (prefixWord ++ tailWord_6532317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532317).length < 2 ^ (prefixWord ++ tailWord_6532317).sum := by decide
  have hdescent : baseEnd_6532317 < baseStart_6532317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532380 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6532380 : Nat := 118140960795 + 6532380 * 2 ^ 59
def prefixEnd_6532380 : Nat := 4983230072969 + 3 ^ 40 * 6532380 * 2
def baseEnd_6532380 : Nat := 3354250757817257266908137

theorem tailTrace_6532380 : CollatzResearch.WordTrace tailWord_6532380 prefixEnd_6532380 3354250757817257266908137 := by
  unfold tailWord_6532380
  simp only [CollatzResearch.WordTrace]
  refine ⟨119127736037155188264169297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158836981382873584352225729 119127736037155188264169297)
  ·
    refine ⟨89345802027866391198126973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119127736037155188264169297 89345802027866391198126973)
    ·
      refine ⟨33504675760449896699297615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89345802027866391198126973 33504675760449896699297615)
      ·
        refine ⟨50257013640674845048946423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33504675760449896699297615 50257013640674845048946423)
        ·
          refine ⟨75385520461012267573419635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50257013640674845048946423 75385520461012267573419635)
          ·
            refine ⟨113078280691518401360129453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75385520461012267573419635 113078280691518401360129453)
            ·
              refine ⟨42404355259319400510048545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113078280691518401360129453 42404355259319400510048545)
              ·
                refine ⟨31803266444489550382536409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42404355259319400510048545 31803266444489550382536409)
                ·
                  refine ⟨23852449833367162786902307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31803266444489550382536409 23852449833367162786902307)
                  ·
                    refine ⟨35778674750050744180353461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23852449833367162786902307 35778674750050744180353461)
                    ·
                      refine ⟨3354250757817257266908137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35778674750050744180353461 3354250757817257266908137)
                      ·
                        rfl

theorem cell23_6532380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6532380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532380 prefixEnd_6532380 := by exact prefixLift 6532380
  have htrace : WordTrace (prefixWord ++ tailWord_6532380) baseStart_6532380 baseEnd_6532380 := by
    simpa [prefixWord, tailWord_6532380, baseEnd_6532380] using wordTrace_append hprefix tailTrace_6532380
  have hstable : (prefixWord ++ tailWord_6532380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532380).length < 2 ^ (prefixWord ++ tailWord_6532380).sum := by decide
  have hdescent : baseEnd_6532380 < baseStart_6532380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532381 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6532381 : Nat := 118140960795 + 6532381 * 2 ^ 59
def prefixEnd_6532381 : Nat := 4983230072969 + 3 ^ 40 * 6532381 * 2
def baseEnd_6532381 : Nat := 3354251271297911762995633

theorem tailTrace_6532381 : CollatzResearch.WordTrace tailWord_6532381 prefixEnd_6532381 3354251271297911762995633 := by
  unfold tailWord_6532381
  simp only [CollatzResearch.WordTrace]
  refine ⟨238255508547306753699124997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158837005698204502466083331 238255508547306753699124997)
  ·
    refine ⟨44672907852620016318585937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238255508547306753699124997 44672907852620016318585937)
    ·
      refine ⟨33504680889465012238939453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44672907852620016318585937 33504680889465012238939453)
      ·
        refine ⟨12564255333549379589602295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33504680889465012238939453 12564255333549379589602295)
        ·
          refine ⟨18846383000324069384403443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12564255333549379589602295 18846383000324069384403443)
          ·
            refine ⟨28269574500486104076605165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18846383000324069384403443 28269574500486104076605165)
            ·
              refine ⟨10601090437682289028726937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28269574500486104076605165 10601090437682289028726937)
              ·
                refine ⟨7950817828261716771545203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10601090437682289028726937 7950817828261716771545203)
                ·
                  refine ⟨11926226742392575157317805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7950817828261716771545203 11926226742392575157317805)
                  ·
                    refine ⟨4472335028397215683994177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11926226742392575157317805 4472335028397215683994177)
                    ·
                      refine ⟨3354251271297911762995633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472335028397215683994177 3354251271297911762995633)
                      ·
                        rfl

theorem cell23_6532381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6532381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532381 prefixEnd_6532381 := by exact prefixLift 6532381
  have htrace : WordTrace (prefixWord ++ tailWord_6532381) baseStart_6532381 baseEnd_6532381 := by
    simpa [prefixWord, tailWord_6532381, baseEnd_6532381] using wordTrace_append hprefix tailTrace_6532381
  have hstable : (prefixWord ++ tailWord_6532381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532381).length < 2 ^ (prefixWord ++ tailWord_6532381).sum := by decide
  have hdescent : baseEnd_6532381 < baseStart_6532381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532393 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_6532393 : Nat := 118140960795 + 6532393 * 2 ^ 59
def prefixEnd_6532393 : Nat := 4983230072969 + 3 ^ 40 * 6532393 * 2
def baseEnd_6532393 : Nat := 3354257433065765716045577

theorem tailTrace_6532393 : CollatzResearch.WordTrace tailWord_6532393 prefixEnd_6532393 3354257433065765716045577 := by
  unfold tailWord_6532393
  simp only [CollatzResearch.WordTrace]
  refine ⟨238255946223263279748561833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158837297482175519832374555 238255946223263279748561833)
  ·
    refine ⟨178691959667447459811421375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238255946223263279748561833 178691959667447459811421375)
    ·
      refine ⟨268037939501171189717132063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178691959667447459811421375 268037939501171189717132063)
      ·
        refine ⟨402056909251756784575698095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268037939501171189717132063 402056909251756784575698095)
        ·
          refine ⟨603085363877635176863547143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402056909251756784575698095 603085363877635176863547143)
          ·
            refine ⟨904628045816452765295320715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603085363877635176863547143 904628045816452765295320715)
            ·
              refine ⟨1356942068724679147942981073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904628045816452765295320715 1356942068724679147942981073)
              ·
                refine ⟨1017706551543509360957235805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356942068724679147942981073 1017706551543509360957235805)
                ·
                  refine ⟨381639956828816010358963427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017706551543509360957235805 381639956828816010358963427)
                  ·
                    refine ⟨572459935243224015538445141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381639956828816010358963427 572459935243224015538445141)
                    ·
                      refine ⟨3354257433065765716045577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 572459935243224015538445141 3354257433065765716045577)
                      ·
                        rfl

theorem cell23_6532393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_6532393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532393 prefixEnd_6532393 := by exact prefixLift 6532393
  have htrace : WordTrace (prefixWord ++ tailWord_6532393) baseStart_6532393 baseEnd_6532393 := by
    simpa [prefixWord, tailWord_6532393, baseEnd_6532393] using wordTrace_append hprefix tailTrace_6532393
  have hstable : (prefixWord ++ tailWord_6532393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532393).length < 2 ^ (prefixWord ++ tailWord_6532393).sum := by decide
  have hdescent : baseEnd_6532393 < baseStart_6532393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532394 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6532394 : Nat := 118140960795 + 6532394 * 2 ^ 59
def prefixEnd_6532394 : Nat := 4983230072969 + 3 ^ 40 * 6532394 * 2
def baseEnd_6532394 : Nat := 3354257946546420212133073

theorem tailTrace_6532394 : CollatzResearch.WordTrace tailWord_6532394 prefixEnd_6532394 3354257946546420212133073 := by
  unfold tailWord_6532394
  simp only [CollatzResearch.WordTrace]
  refine ⟨59563995674064914229837059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158837321797506437946232157 59563995674064914229837059)
  ·
    refine ⟨89345993511097371344755589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59563995674064914229837059 89345993511097371344755589)
    ·
      refine ⟨16752373783330757127141673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89345993511097371344755589 16752373783330757127141673)
      ·
        refine ⟨12564280337498067845356255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16752373783330757127141673 12564280337498067845356255)
        ·
          refine ⟨18846420506247101768034383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12564280337498067845356255 18846420506247101768034383)
          ·
            refine ⟨28269630759370652652051575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18846420506247101768034383 28269630759370652652051575)
            ·
              refine ⟨42404446139055978978077363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28269630759370652652051575 42404446139055978978077363)
              ·
                refine ⟨63606669208583968467116045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42404446139055978978077363 63606669208583968467116045)
                ·
                  refine ⟨23852500953218988175168517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63606669208583968467116045 23852500953218988175168517)
                  ·
                    refine ⟨4472343928728560282844097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23852500953218988175168517 4472343928728560282844097)
                    ·
                      refine ⟨3354257946546420212133073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472343928728560282844097 3354257946546420212133073)
                      ·
                        rfl

theorem cell23_6532394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6532394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532394 prefixEnd_6532394 := by exact prefixLift 6532394
  have htrace : WordTrace (prefixWord ++ tailWord_6532394) baseStart_6532394 baseEnd_6532394 := by
    simpa [prefixWord, tailWord_6532394, baseEnd_6532394] using wordTrace_append hprefix tailTrace_6532394
  have hstable : (prefixWord ++ tailWord_6532394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532394).length < 2 ^ (prefixWord ++ tailWord_6532394).sum := by decide
  have hdescent : baseEnd_6532394 < baseStart_6532394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532430 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 7]
def baseStart_6532430 : Nat := 118140960795 + 6532430 * 2 ^ 59
def prefixEnd_6532430 : Nat := 4983230072969 + 3 ^ 40 * 6532430 * 2
def baseEnd_6532430 : Nat := 1118092143949994023760969

theorem tailTrace_6532430 : CollatzResearch.WordTrace tailWord_6532430 prefixEnd_6532430 1118092143949994023760969 := by
  unfold tailWord_6532430
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782161965516154383457343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158838197149419490045105829 29782161965516154383457343)
  ·
    refine ⟨44673242948274231575186015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782161965516154383457343 44673242948274231575186015)
    ·
      refine ⟨67009864422411347362779023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44673242948274231575186015 67009864422411347362779023)
      ·
        refine ⟨100514796633617021044168535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67009864422411347362779023 100514796633617021044168535)
        ·
          refine ⟨150772194950425531566252803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100514796633617021044168535 150772194950425531566252803)
          ·
            refine ⟨226158292425638297349379205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150772194950425531566252803 226158292425638297349379205)
            ·
              refine ⟨42404679829807180753008601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226158292425638297349379205 42404679829807180753008601)
              ·
                refine ⟨31803509872355385564756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42404679829807180753008601 31803509872355385564756451)
                ·
                  refine ⟨47705264808533078347134677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31803509872355385564756451 47705264808533078347134677)
                  ·
                    refine ⟨1118092143949994023760969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47705264808533078347134677 1118092143949994023760969)
                    ·
                      rfl

theorem cell23_6532430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_6532430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532430 prefixEnd_6532430 := by exact prefixLift 6532430
  have htrace : WordTrace (prefixWord ++ tailWord_6532430) baseStart_6532430 baseEnd_6532430 := by
    simpa [prefixWord, tailWord_6532430, baseEnd_6532430] using wordTrace_append hprefix tailTrace_6532430
  have hstable : (prefixWord ++ tailWord_6532430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532430).length < 2 ^ (prefixWord ++ tailWord_6532430).sum := by decide
  have hdescent : baseEnd_6532430 < baseStart_6532430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532462 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6532462 : Nat := 118140960795 + 6532462 * 2 ^ 59
def prefixEnd_6532462 : Nat := 4983230072969 + 3 ^ 40 * 6532462 * 2
def baseEnd_6532462 : Nat := 3354292863230925946082761

theorem tailTrace_6532462 : CollatzResearch.WordTrace tailWord_6532462 prefixEnd_6532462 3354292863230925946082761 := by
  unfold tailWord_6532462
  simp only [CollatzResearch.WordTrace]
  refine ⟨29782307857501663066602955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158838975240008869688549093 29782307857501663066602955)
  ·
    refine ⟨44673461786252494599904433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29782307857501663066602955 44673461786252494599904433)
    ·
      refine ⟨33505096339689370949928325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44673461786252494599904433 33505096339689370949928325)
      ·
        refine ⟨6282205563691757053111561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33505096339689370949928325 6282205563691757053111561)
        ·
          refine ⟨4711654172768817789833671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282205563691757053111561 4711654172768817789833671)
          ·
            refine ⟨7067481259153226684750507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711654172768817789833671 7067481259153226684750507)
            ·
              refine ⟨10601221888729840027125761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067481259153226684750507 10601221888729840027125761)
              ·
                refine ⟨7950916416547380020344321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10601221888729840027125761 7950916416547380020344321)
                ·
                  refine ⟨5963187312410535015258241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7950916416547380020344321 5963187312410535015258241)
                  ·
                    refine ⟨4472390484307901261443681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5963187312410535015258241 4472390484307901261443681)
                    ·
                      refine ⟨3354292863230925946082761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472390484307901261443681 3354292863230925946082761)
                      ·
                        rfl

theorem cell23_6532462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6532462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532462 prefixEnd_6532462 := by exact prefixLift 6532462
  have htrace : WordTrace (prefixWord ++ tailWord_6532462) baseStart_6532462 baseEnd_6532462 := by
    simpa [prefixWord, tailWord_6532462, baseEnd_6532462] using wordTrace_append hprefix tailTrace_6532462
  have hstable : (prefixWord ++ tailWord_6532462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532462).length < 2 ^ (prefixWord ++ tailWord_6532462).sum := by decide
  have hdescent : baseEnd_6532462 < baseStart_6532462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532484 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6532484 : Nat := 118140960795 + 6532484 * 2 ^ 59
def prefixEnd_6532484 : Nat := 4983230072969 + 3 ^ 40 * 6532484 * 2
def baseEnd_6532484 : Nat := 3354304159805324860007659

theorem tailTrace_6532484 : CollatzResearch.WordTrace tailWord_6532484 prefixEnd_6532484 3354304159805324860007659 := by
  unfold tailWord_6532484
  simp only [CollatzResearch.WordTrace]
  refine ⟨119129632632966801145062253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158839510177289068193416337 119129632632966801145062253)
  ·
    refine ⟨44673612237362550429398345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119129632632966801145062253 44673612237362550429398345)
    ·
      refine ⟨33505209178021912822048759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44673612237362550429398345 33505209178021912822048759)
      ·
        refine ⟨50257813767032869233073139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33505209178021912822048759 50257813767032869233073139)
        ·
          refine ⟨75386720650549303849609709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50257813767032869233073139 75386720650549303849609709)
          ·
            refine ⟨28270020243955988943603641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75386720650549303849609709 28270020243955988943603641)
            ·
              refine ⟨21202515182966991707702731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28270020243955988943603641 21202515182966991707702731)
              ·
                refine ⟨31803772774450487561554097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21202515182966991707702731 31803772774450487561554097)
                ·
                  refine ⟨23852829580837865671165573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31803772774450487561554097 23852829580837865671165573)
                  ·
                    refine ⟨4472405546407099813343545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23852829580837865671165573 4472405546407099813343545)
                    ·
                      refine ⟨3354304159805324860007659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472405546407099813343545 3354304159805324860007659)
                      ·
                        rfl

theorem cell23_6532484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6532484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532484 prefixEnd_6532484 := by exact prefixLift 6532484
  have htrace : WordTrace (prefixWord ++ tailWord_6532484) baseStart_6532484 baseEnd_6532484 := by
    simpa [prefixWord, tailWord_6532484, baseEnd_6532484] using wordTrace_append hprefix tailTrace_6532484
  have hstable : (prefixWord ++ tailWord_6532484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532484).length < 2 ^ (prefixWord ++ tailWord_6532484).sum := by decide
  have hdescent : baseEnd_6532484 < baseStart_6532484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532487 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_6532487 : Nat := 118140960795 + 6532487 * 2 ^ 59
def prefixEnd_6532487 : Nat := 4983230072969 + 3 ^ 40 * 6532487 * 2
def baseEnd_6532487 : Nat := 3354305700247288348270145

theorem tailTrace_6532487 : CollatzResearch.WordTrace tailWord_6532487 prefixEnd_6532487 3354305700247288348270145 := by
  unfold tailWord_6532487
  simp only [CollatzResearch.WordTrace]
  refine ⟨238259374684922733802483715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158839583123281822534989143 238259374684922733802483715)
  ·
    refine ⟨357389062027384100703725573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238259374684922733802483715 357389062027384100703725573)
    ·
      refine ⟨67010449130134518881948545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357389062027384100703725573 67010449130134518881948545)
      ·
        refine ⟨50257836847600889161461409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67010449130134518881948545 50257836847600889161461409)
        ·
          refine ⟨37693377635700666871096057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50257836847600889161461409 37693377635700666871096057)
          ·
            refine ⟨28270033226775500153322043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37693377635700666871096057 28270033226775500153322043)
            ·
              refine ⟨42405049840163250229983065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28270033226775500153322043 42405049840163250229983065)
              ·
                refine ⟨31803787380122437672487299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42405049840163250229983065 31803787380122437672487299)
                ·
                  refine ⟨47705681070183656508730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31803787380122437672487299 47705681070183656508730949)
                  ·
                    refine ⟨8944815200659435595387053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47705681070183656508730949 8944815200659435595387053)
                    ·
                      refine ⟨3354305700247288348270145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8944815200659435595387053 3354305700247288348270145)
                      ·
                        rfl

theorem cell23_6532487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_6532487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532487 prefixEnd_6532487 := by exact prefixLift 6532487
  have htrace : WordTrace (prefixWord ++ tailWord_6532487) baseStart_6532487 baseEnd_6532487 := by
    simpa [prefixWord, tailWord_6532487, baseEnd_6532487] using wordTrace_append hprefix tailTrace_6532487
  have hstable : (prefixWord ++ tailWord_6532487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532487).length < 2 ^ (prefixWord ++ tailWord_6532487).sum := by decide
  have hdescent : baseEnd_6532487 < baseStart_6532487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532511 : List Nat := [1, 1, 2, 5, 1, 2, 3, 3, 1, 4]
def baseStart_6532511 : Nat := 118140960795 + 6532511 * 2 ^ 59
def prefixEnd_6532511 : Nat := 4983230072969 + 3 ^ 40 * 6532511 * 2
def baseEnd_6532511 : Nat := 1118106007927665418123345

theorem tailTrace_6532511 : CollatzResearch.WordTrace tailWord_6532511 prefixEnd_6532511 1118106007927665418123345 := by
  unfold tailWord_6532511
  simp only [CollatzResearch.WordTrace]
  refine ⟨238260250036835785901357387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158840166691223857267571591 238260250036835785901357387)
  ·
    refine ⟨357390375055253678852036081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238260250036835785901357387 357390375055253678852036081)
    ·
      refine ⟨268042781291440259139027061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357390375055253678852036081 268042781291440259139027061)
      ·
        refine ⟨25129010746072524294283787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268042781291440259139027061 25129010746072524294283787)
        ·
          refine ⟨37693516119108786441425681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25129010746072524294283787 37693516119108786441425681)
          ·
            refine ⟨28270137089331589831069261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37693516119108786441425681 28270137089331589831069261)
            ·
              refine ⟨10601301408499346186650973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28270137089331589831069261 10601301408499346186650973)
              ·
                refine ⟨3975488028187254819994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10601301408499346186650973 3975488028187254819994115)
                ·
                  refine ⟨5963232042280882229991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975488028187254819994115 5963232042280882229991173)
                  ·
                    refine ⟨1118106007927665418123345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5963232042280882229991173 1118106007927665418123345)
                    ·
                      rfl

theorem cell23_6532511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_6532511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532511 prefixEnd_6532511 := by exact prefixLift 6532511
  have htrace : WordTrace (prefixWord ++ tailWord_6532511) baseStart_6532511 baseEnd_6532511 := by
    simpa [prefixWord, tailWord_6532511, baseEnd_6532511] using wordTrace_append hprefix tailTrace_6532511
  have hstable : (prefixWord ++ tailWord_6532511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532511).length < 2 ^ (prefixWord ++ tailWord_6532511).sum := by decide
  have hdescent : baseEnd_6532511 < baseStart_6532511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532554 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_6532554 : Nat := 118140960795 + 6532554 * 2 ^ 59
def prefixEnd_6532554 : Nat := 4983230072969 + 3 ^ 40 * 6532554 * 2
def baseEnd_6532554 : Nat := 1118113367817046528710779

theorem tailTrace_6532554 : CollatzResearch.WordTrace tailWord_6532554 prefixEnd_6532554 1118113367817046528710779 := by
  unfold tailWord_6532554
  simp only [CollatzResearch.WordTrace]
  refine ⟨59565454593920001061293179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158841212250453336163448477 59565454593920001061293179)
  ·
    refine ⟨89348181890880001591939769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59565454593920001061293179 89348181890880001591939769)
    ·
      refine ⟨67011136418160001193954827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89348181890880001591939769 67011136418160001193954827)
      ·
        refine ⟨100516704627240001790932241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67011136418160001193954827 100516704627240001790932241)
        ·
          refine ⟨75387528470430001343199181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100516704627240001790932241 75387528470430001343199181)
          ·
            refine ⟨28270323176411250503699693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75387528470430001343199181 28270323176411250503699693)
            ·
              refine ⟨10601371191154218938887385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28270323176411250503699693 10601371191154218938887385)
              ·
                refine ⟨7951028393365664204165539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10601371191154218938887385 7951028393365664204165539)
                ·
                  refine ⟨11926542590048496306248309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951028393365664204165539 11926542590048496306248309)
                  ·
                    refine ⟨1118113367817046528710779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11926542590048496306248309 1118113367817046528710779)
                    ·
                      rfl

theorem cell23_6532554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_6532554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532554 prefixEnd_6532554 := by exact prefixLift 6532554
  have htrace : WordTrace (prefixWord ++ tailWord_6532554) baseStart_6532554 baseEnd_6532554 := by
    simpa [prefixWord, tailWord_6532554, baseEnd_6532554] using wordTrace_append hprefix tailTrace_6532554
  have hstable : (prefixWord ++ tailWord_6532554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532554).length < 2 ^ (prefixWord ++ tailWord_6532554).sum := by decide
  have hdescent : baseEnd_6532554 < baseStart_6532554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532567 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 6, 4]
def baseStart_6532567 : Nat := 118140960795 + 6532567 * 2 ^ 59
def prefixEnd_6532567 : Nat := 4983230072969 + 3 ^ 40 * 6532567 * 2
def baseEnd_6532567 : Nat := 1118115592899882678423259

theorem tailTrace_6532567 : CollatzResearch.WordTrace tailWord_6532567 prefixEnd_6532567 1118115592899882678423259 := by
  unfold tailWord_6532567
  simp only [CollatzResearch.WordTrace]
  refine ⟨238262292524632907465395955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158841528349755271643597303 238262292524632907465395955)
  ·
    refine ⟨357393438786949361198093933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238262292524632907465395955 357393438786949361198093933)
    ·
      refine ⟨134022539545106010449285225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357393438786949361198093933 134022539545106010449285225)
      ·
        refine ⟨100516904658829507836963919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134022539545106010449285225 100516904658829507836963919)
        ·
          refine ⟨150775356988244261755445879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100516904658829507836963919 150775356988244261755445879)
          ·
            refine ⟨226163035482366392633168819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150775356988244261755445879 226163035482366392633168819)
            ·
              refine ⟨339244553223549588949753229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226163035482366392633168819 339244553223549588949753229)
              ·
                refine ⟨127216707458831095856157461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339244553223549588949753229 127216707458831095856157461)
                ·
                  refine ⟨5963283162132707618257381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127216707458831095856157461 5963283162132707618257381)
                  ·
                    refine ⟨1118115592899882678423259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5963283162132707618257381 1118115592899882678423259)
                    ·
                      rfl

theorem cell23_6532567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_6532567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532567 prefixEnd_6532567 := by exact prefixLift 6532567
  have htrace : WordTrace (prefixWord ++ tailWord_6532567) baseStart_6532567 baseEnd_6532567 := by
    simpa [prefixWord, tailWord_6532567, baseEnd_6532567] using wordTrace_append hprefix tailTrace_6532567
  have hstable : (prefixWord ++ tailWord_6532567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532567).length < 2 ^ (prefixWord ++ tailWord_6532567).sum := by decide
  have hdescent : baseEnd_6532567 < baseStart_6532567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532641 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6532641 : Nat := 118140960795 + 6532641 * 2 ^ 59
def prefixEnd_6532641 : Nat := 4983230072969 + 3 ^ 40 * 6532641 * 2
def baseEnd_6532641 : Nat := 3354384776268080745744437

theorem tailTrace_6532641 : CollatzResearch.WordTrace tailWord_6532641 prefixEnd_6532641 3354384776268080745744437 := by
  unfold tailWord_6532641
  simp only [CollatzResearch.WordTrace]
  refine ⟨238264991526364818103589777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158843327684243212069059851 238264991526364818103589777)
  ·
    refine ⟨178698743644773613577692333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238264991526364818103589777 178698743644773613577692333)
    ·
      refine ⟨67012028866790105091634625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178698743644773613577692333 67012028866790105091634625)
      ·
        refine ⟨50259021650092578818725969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67012028866790105091634625 50259021650092578818725969)
        ·
          refine ⟨37694266237569434114044477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50259021650092578818725969 37694266237569434114044477)
          ·
            refine ⟨14135349839088537792766679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37694266237569434114044477 14135349839088537792766679)
            ·
              refine ⟨21203024758632806689150019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14135349839088537792766679 21203024758632806689150019)
              ·
                refine ⟨31804537137949210033725029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21203024758632806689150019 31804537137949210033725029)
                ·
                  refine ⟨5963350713365476881323443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31804537137949210033725029 5963350713365476881323443)
                  ·
                    refine ⟨8945026070048215321985165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963350713365476881323443 8945026070048215321985165)
                    ·
                      refine ⟨3354384776268080745744437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945026070048215321985165 3354384776268080745744437)
                      ·
                        rfl

theorem cell23_6532641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6532641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532641 prefixEnd_6532641 := by exact prefixLift 6532641
  have htrace : WordTrace (prefixWord ++ tailWord_6532641) baseStart_6532641 baseEnd_6532641 := by
    simpa [prefixWord, tailWord_6532641, baseEnd_6532641] using wordTrace_append hprefix tailTrace_6532641
  have hstable : (prefixWord ++ tailWord_6532641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532641).length < 2 ^ (prefixWord ++ tailWord_6532641).sum := by decide
  have hdescent : baseEnd_6532641 < baseStart_6532641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532684 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6532684 : Nat := 118140960795 + 6532684 * 2 ^ 59
def prefixEnd_6532684 : Nat := 4983230072969 + 3 ^ 40 * 6532684 * 2
def baseEnd_6532684 : Nat := 3354406855936224077506739

theorem tailTrace_6532684 : CollatzResearch.WordTrace tailWord_6532684 prefixEnd_6532684 3354406855936224077506739 := by
  unfold tailWord_6532684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119133279932604518223702553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158844373243472690964936737 119133279932604518223702553)
  ·
    refine ⟨89349959949453388667776915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119133279932604518223702553 89349959949453388667776915)
    ·
      refine ⟨134024939924180083001665373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89349959949453388667776915 134024939924180083001665373)
      ·
        refine ⟨50259352471567531125624515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134024939924180083001665373 50259352471567531125624515)
        ·
          refine ⟨75389028707351296688436773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50259352471567531125624515 75389028707351296688436773)
          ·
            refine ⟨14135442882628368129081895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75389028707351296688436773 14135442882628368129081895)
            ·
              refine ⟨21203164323942552193622843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14135442882628368129081895 21203164323942552193622843)
              ·
                refine ⟨31804746485913828290434265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21203164323942552193622843 31804746485913828290434265)
                ·
                  refine ⟨23853559864435371217825699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31804746485913828290434265 23853559864435371217825699)
                  ·
                    refine ⟨35780339796653056826738549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23853559864435371217825699 35780339796653056826738549)
                    ·
                      refine ⟨3354406855936224077506739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35780339796653056826738549 3354406855936224077506739)
                      ·
                        rfl

theorem cell23_6532684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6532684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532684 prefixEnd_6532684 := by exact prefixLift 6532684
  have htrace : WordTrace (prefixWord ++ tailWord_6532684) baseStart_6532684 baseEnd_6532684 := by
    simpa [prefixWord, tailWord_6532684, baseEnd_6532684] using wordTrace_append hprefix tailTrace_6532684
  have hstable : (prefixWord ++ tailWord_6532684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532684).length < 2 ^ (prefixWord ++ tailWord_6532684).sum := by decide
  have hdescent : baseEnd_6532684 < baseStart_6532684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532727 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_6532727 : Nat := 118140960795 + 6532727 * 2 ^ 59
def prefixEnd_6532727 : Nat := 4983230072969 + 3 ^ 40 * 6532727 * 2
def baseEnd_6532727 : Nat := 3354428935604367409269041

theorem tailTrace_6532727 : CollatzResearch.WordTrace tailWord_6532727 prefixEnd_6532727 3354428935604367409269041 := by
  unfold tailWord_6532727
  simp only [CollatzResearch.WordTrace]
  refine ⟨238268128204053254791220435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158845418802702169860813623 238268128204053254791220435)
  ·
    refine ⟨357402192306079882186830653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238268128204053254791220435 357402192306079882186830653)
    ·
      refine ⟨134025822114779955820061495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357402192306079882186830653 134025822114779955820061495)
      ·
        refine ⟨201038733172169933730092243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134025822114779955820061495 201038733172169933730092243)
        ·
          refine ⟨301558099758254900595138365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201038733172169933730092243 301558099758254900595138365)
          ·
            refine ⟨113084287409345587723176887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301558099758254900595138365 113084287409345587723176887)
            ·
              refine ⟨169626431114018381584765331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113084287409345587723176887 169626431114018381584765331)
              ·
                refine ⟨254439646671027572377147997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169626431114018381584765331 254439646671027572377147997)
                ·
                  refine ⟨95414867501635339641430499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254439646671027572377147997 95414867501635339641430499)
                  ·
                    refine ⟨143122301252453009462145749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95414867501635339641430499 143122301252453009462145749)
                    ·
                      refine ⟨3354428935604367409269041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143122301252453009462145749 3354428935604367409269041)
                      ·
                        rfl

theorem cell23_6532727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_6532727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532727 prefixEnd_6532727 := by exact prefixLift 6532727
  have htrace : WordTrace (prefixWord ++ tailWord_6532727) baseStart_6532727 baseEnd_6532727 := by
    simpa [prefixWord, tailWord_6532727, baseEnd_6532727] using wordTrace_append hprefix tailTrace_6532727
  have hstable : (prefixWord ++ tailWord_6532727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532727).length < 2 ^ (prefixWord ++ tailWord_6532727).sum := by decide
  have hdescent : baseEnd_6532727 < baseStart_6532727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532771 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 4, 2]
def baseStart_6532771 : Nat := 118140960795 + 6532771 * 2 ^ 59
def prefixEnd_6532771 : Nat := 4983230072969 + 3 ^ 40 * 6532771 * 2
def baseEnd_6532771 : Nat := 3354451528753165237118839

theorem tailTrace_6532771 : CollatzResearch.WordTrace tailWord_6532771 prefixEnd_6532771 3354451528753165237118839 := by
  unfold tailWord_6532771
  simp only [CollatzResearch.WordTrace]
  refine ⟨238269733015893850305822167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158846488677262566870548111 238269733015893850305822167)
  ·
    refine ⟨357404599523840775458733251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238269733015893850305822167 357404599523840775458733251)
    ·
      refine ⟨536106899285761163188099877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357404599523840775458733251 536106899285761163188099877)
      ·
        refine ⟨100520043616080218097768727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536106899285761163188099877 100520043616080218097768727)
        ·
          refine ⟨150780065424120327146653091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100520043616080218097768727 150780065424120327146653091)
          ·
            refine ⟨226170098136180490719979637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150780065424120327146653091 226170098136180490719979637)
            ·
              refine ⟨21203446700266921004998091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 226170098136180490719979637 21203446700266921004998091)
              ·
                refine ⟨31805170050400381507497137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21203446700266921004998091 31805170050400381507497137)
                ·
                  refine ⟨23853877537800286130622853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31805170050400381507497137 23853877537800286130622853)
                  ·
                    refine ⟨4472602038337553649491785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23853877537800286130622853 4472602038337553649491785)
                    ·
                      refine ⟨3354451528753165237118839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472602038337553649491785 3354451528753165237118839)
                      ·
                        rfl

theorem cell23_6532771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_6532771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532771 prefixEnd_6532771 := by exact prefixLift 6532771
  have htrace : WordTrace (prefixWord ++ tailWord_6532771) baseStart_6532771 baseEnd_6532771 := by
    simpa [prefixWord, tailWord_6532771, baseEnd_6532771] using wordTrace_append hprefix tailTrace_6532771
  have hstable : (prefixWord ++ tailWord_6532771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532771).length < 2 ^ (prefixWord ++ tailWord_6532771).sum := by decide
  have hdescent : baseEnd_6532771 < baseStart_6532771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532791 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_6532791 : Nat := 118140960795 + 6532791 * 2 ^ 59
def prefixEnd_6532791 : Nat := 4983230072969 + 3 ^ 40 * 6532791 * 2
def baseEnd_6532791 : Nat := 3354461798366255158868747

theorem tailTrace_6532791 : CollatzResearch.WordTrace tailWord_6532791 prefixEnd_6532791 3354461798366255158868747 := by
  unfold tailWord_6532791
  simp only [CollatzResearch.WordTrace]
  refine ⟨238270462475821393721550227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158846974983880929147700151 238270462475821393721550227)
  ·
    refine ⟨357405693713732090582325341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238270462475821393721550227 357405693713732090582325341)
    ·
      refine ⟨134027135142649533968372003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357405693713732090582325341 134027135142649533968372003)
      ·
        refine ⟨201040702713974300952558005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134027135142649533968372003 201040702713974300952558005)
        ·
          refine ⟨18847565879435090714302313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201040702713974300952558005 18847565879435090714302313)
          ·
            refine ⟨14135674409576318035726735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18847565879435090714302313 14135674409576318035726735)
            ·
              refine ⟨21203511614364477053590103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14135674409576318035726735 21203511614364477053590103)
              ·
                refine ⟨31805267421546715580385155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21203511614364477053590103 31805267421546715580385155)
                ·
                  refine ⟨47707901132320073370577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31805267421546715580385155 47707901132320073370577733)
                  ·
                    refine ⟨8945231462310013756983325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47707901132320073370577733 8945231462310013756983325)
                    ·
                      refine ⟨3354461798366255158868747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945231462310013756983325 3354461798366255158868747)
                      ·
                        rfl

theorem cell23_6532791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_6532791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532791 prefixEnd_6532791 := by exact prefixLift 6532791
  have htrace : WordTrace (prefixWord ++ tailWord_6532791) baseStart_6532791 baseEnd_6532791 := by
    simpa [prefixWord, tailWord_6532791, baseEnd_6532791] using wordTrace_append hprefix tailTrace_6532791
  have hstable : (prefixWord ++ tailWord_6532791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532791).length < 2 ^ (prefixWord ++ tailWord_6532791).sum := by decide
  have hdescent : baseEnd_6532791 < baseStart_6532791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532814 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6532814 : Nat := 118140960795 + 6532814 * 2 ^ 59
def prefixEnd_6532814 : Nat := 4983230072969 + 3 ^ 40 * 6532814 * 2
def baseEnd_6532814 : Nat := 3354473608421308568881141

theorem tailTrace_6532814 : CollatzResearch.WordTrace tailWord_6532814 prefixEnd_6532814 3354473608421308568881141 := by
  unfold tailWord_6532814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29783912669342258581204687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158847534236492045766424997 29783912669342258581204687)
  ·
    refine ⟨44675869004013387871807031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29783912669342258581204687 44675869004013387871807031)
    ·
      refine ⟨67013803506020081807710547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44675869004013387871807031 67013803506020081807710547)
      ·
        refine ⟨100520705259030122711565821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67013803506020081807710547 100520705259030122711565821)
        ·
          refine ⟨37695264472136296016837183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100520705259030122711565821 37695264472136296016837183)
          ·
            refine ⟨56542896708204444025255775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37695264472136296016837183 56542896708204444025255775)
            ·
              refine ⟨84814345062306666037883663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56542896708204444025255775 84814345062306666037883663)
              ·
                refine ⟨127221517593459999056825495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84814345062306666037883663 127221517593459999056825495)
                ·
                  refine ⟨190832276390189998585238243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127221517593459999056825495 190832276390189998585238243)
                  ·
                    refine ⟨286248414585284997877857365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190832276390189998585238243 286248414585284997877857365)
                    ·
                      refine ⟨3354473608421308568881141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286248414585284997877857365 3354473608421308568881141)
                      ·
                        rfl

theorem cell23_6532814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6532814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532814 prefixEnd_6532814 := by exact prefixLift 6532814
  have htrace : WordTrace (prefixWord ++ tailWord_6532814) baseStart_6532814 baseEnd_6532814 := by
    simpa [prefixWord, tailWord_6532814, baseEnd_6532814] using wordTrace_append hprefix tailTrace_6532814
  have hstable : (prefixWord ++ tailWord_6532814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532814).length < 2 ^ (prefixWord ++ tailWord_6532814).sum := by decide
  have hdescent : baseEnd_6532814 < baseStart_6532814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532831 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 5, 2]
def baseStart_6532831 : Nat := 118140960795 + 6532831 * 2 ^ 59
def prefixEnd_6532831 : Nat := 4983230072969 + 3 ^ 40 * 6532831 * 2
def baseEnd_6532831 : Nat := 3354482337592435002368563

theorem tailTrace_6532831 : CollatzResearch.WordTrace tailWord_6532831 prefixEnd_6532831 3354482337592435002368563 := by
  unfold tailWord_6532831
  simp only [CollatzResearch.WordTrace]
  refine ⟨238271921395676480553006347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158847947597117653702004231 238271921395676480553006347)
  ·
    refine ⟨357407882093514720829509521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238271921395676480553006347 357407882093514720829509521)
    ·
      refine ⟨268055911570136040622132141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357407882093514720829509521 268055911570136040622132141)
      ·
        refine ⟨100520966838801015233299553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268055911570136040622132141 100520966838801015233299553)
        ·
          refine ⟨75390725129100761424974665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100520966838801015233299553 75390725129100761424974665)
          ·
            refine ⟨56543043846825571068730999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75390725129100761424974665 56543043846825571068730999)
            ·
              refine ⟨84814565770238356603096499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56543043846825571068730999 84814565770238356603096499)
              ·
                refine ⟨127221848655357534904644749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84814565770238356603096499 127221848655357534904644749)
                ·
                  refine ⟨47708193245759075589241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127221848655357534904644749 47708193245759075589241781)
                  ·
                    refine ⟨4472643116789913336491417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47708193245759075589241781 4472643116789913336491417)
                    ·
                      refine ⟨3354482337592435002368563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472643116789913336491417 3354482337592435002368563)
                      ·
                        rfl

theorem cell23_6532831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_6532831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532831 prefixEnd_6532831 := by exact prefixLift 6532831
  have htrace : WordTrace (prefixWord ++ tailWord_6532831) baseStart_6532831 baseEnd_6532831 := by
    simpa [prefixWord, tailWord_6532831, baseEnd_6532831] using wordTrace_append hprefix tailTrace_6532831
  have hstable : (prefixWord ++ tailWord_6532831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532831).length < 2 ^ (prefixWord ++ tailWord_6532831).sum := by decide
  have hdescent : baseEnd_6532831 < baseStart_6532831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532855 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_6532855 : Nat := 118140960795 + 6532855 * 2 ^ 59
def prefixEnd_6532855 : Nat := 4983230072969 + 3 ^ 40 * 6532855 * 2
def baseEnd_6532855 : Nat := 3354494661128142908468453

theorem tailTrace_6532855 : CollatzResearch.WordTrace tailWord_6532855 prefixEnd_6532855 3354494661128142908468453 := by
  unfold tailWord_6532855
  simp only [CollatzResearch.WordTrace]
  refine ⟨238272796747589532651880019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158848531165059688434586679 238272796747589532651880019)
  ·
    refine ⟨357409195121384298977820029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238272796747589532651880019 357409195121384298977820029)
    ·
      refine ⟨134028448170519112116682511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357409195121384298977820029 134028448170519112116682511)
      ·
        refine ⟨201042672255778668175023767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134028448170519112116682511 201042672255778668175023767)
        ·
          refine ⟨301564008383668002262535651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201042672255778668175023767 301564008383668002262535651)
          ·
            refine ⟨452346012575502003393803477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301564008383668002262535651 452346012575502003393803477)
            ·
              refine ⟨10601859669738328204542269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 452346012575502003393803477 10601859669738328204542269)
              ·
                refine ⟨3975697376151873076703351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10601859669738328204542269 3975697376151873076703351)
                ·
                  refine ⟨5963546064227809615055027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975697376151873076703351 5963546064227809615055027)
                  ·
                    refine ⟨8945319096341714422582541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963546064227809615055027 8945319096341714422582541)
                    ·
                      refine ⟨3354494661128142908468453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945319096341714422582541 3354494661128142908468453)
                      ·
                        rfl

theorem cell23_6532855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_6532855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532855 prefixEnd_6532855 := by exact prefixLift 6532855
  have htrace : WordTrace (prefixWord ++ tailWord_6532855) baseStart_6532855 baseEnd_6532855 := by
    simpa [prefixWord, tailWord_6532855, baseEnd_6532855] using wordTrace_append hprefix tailTrace_6532855
  have hstable : (prefixWord ++ tailWord_6532855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532855).length < 2 ^ (prefixWord ++ tailWord_6532855).sum := by decide
  have hdescent : baseEnd_6532855 < baseStart_6532855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532864 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_6532864 : Nat := 118140960795 + 6532864 * 2 ^ 59
def prefixEnd_6532864 : Nat := 4983230072969 + 3 ^ 40 * 6532864 * 2
def baseEnd_6532864 : Nat := 3354499282454033373255911

theorem tailTrace_6532864 : CollatzResearch.WordTrace tailWord_6532864 prefixEnd_6532864 3354499282454033373255911 := by
  unfold tailWord_6532864
  simp only [CollatzResearch.WordTrace]
  refine ⟨119136562502278463594478823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158848750003037951459305097 119136562502278463594478823)
  ·
    refine ⟨178704843753417695391718235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119136562502278463594478823 178704843753417695391718235)
    ·
      refine ⟨268057265630126543087577353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178704843753417695391718235 268057265630126543087577353)
      ·
        refine ⟨201042949222594907315683015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268057265630126543087577353 201042949222594907315683015)
        ·
          refine ⟨301564423833892360973524523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201042949222594907315683015 301564423833892360973524523)
          ·
            refine ⟨452346635750838541460286785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301564423833892360973524523 452346635750838541460286785)
            ·
              refine ⟨339259976813128906095215089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452346635750838541460286785 339259976813128906095215089)
              ·
                refine ⟨254444982609846679571411317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339259976813128906095215089 254444982609846679571411317)
                ·
                  refine ⟨23854217119673126209819811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254444982609846679571411317 23854217119673126209819811)
                  ·
                    refine ⟨35781325679509689314729717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23854217119673126209819811 35781325679509689314729717)
                    ·
                      refine ⟨3354499282454033373255911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35781325679509689314729717 3354499282454033373255911)
                      ·
                        rfl

theorem cell23_6532864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_6532864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532864 prefixEnd_6532864 := by exact prefixLift 6532864
  have htrace : WordTrace (prefixWord ++ tailWord_6532864) baseStart_6532864 baseEnd_6532864 := by
    simpa [prefixWord, tailWord_6532864, baseEnd_6532864] using wordTrace_append hprefix tailTrace_6532864
  have hstable : (prefixWord ++ tailWord_6532864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532864).length < 2 ^ (prefixWord ++ tailWord_6532864).sum := by decide
  have hdescent : baseEnd_6532864 < baseStart_6532864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532872 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_6532872 : Nat := 118140960795 + 6532872 * 2 ^ 59
def prefixEnd_6532872 : Nat := 4983230072969 + 3 ^ 40 * 6532872 * 2
def baseEnd_6532872 : Nat := 3354503390299269341955875

theorem tailTrace_6532872 : CollatzResearch.WordTrace tailWord_6532872 prefixEnd_6532872 3354503390299269341955875 := by
  unfold tailWord_6532872
  simp only [CollatzResearch.WordTrace]
  refine ⟨119136708394263972277624435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158848944525685296370165913 119136708394263972277624435)
  ·
    refine ⟨178705062591395958416436653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119136708394263972277624435 178705062591395958416436653)
    ·
      refine ⟨67014398471773484406163745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178705062591395958416436653 67014398471773484406163745)
      ·
        refine ⟨50260798853830113304622809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67014398471773484406163745 50260798853830113304622809)
        ·
          refine ⟨37695599140372584978467107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50260798853830113304622809 37695599140372584978467107)
          ·
            refine ⟨56543398710558877467700661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37695599140372584978467107 56543398710558877467700661)
            ·
              refine ⟨5300943629114894762596937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56543398710558877467700661 5300943629114894762596937)
              ·
                refine ⟨3975707721836171071947703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300943629114894762596937 3975707721836171071947703)
                ·
                  refine ⟨5963561582754256607921555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3975707721836171071947703 5963561582754256607921555)
                  ·
                    refine ⟨8945342374131384911882333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963561582754256607921555 8945342374131384911882333)
                    ·
                      refine ⟨3354503390299269341955875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945342374131384911882333 3354503390299269341955875)
                      ·
                        rfl

theorem cell23_6532872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_6532872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532872 prefixEnd_6532872 := by exact prefixLift 6532872
  have htrace : WordTrace (prefixWord ++ tailWord_6532872) baseStart_6532872 baseEnd_6532872 := by
    simpa [prefixWord, tailWord_6532872, baseEnd_6532872] using wordTrace_append hprefix tailTrace_6532872
  have hstable : (prefixWord ++ tailWord_6532872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532872).length < 2 ^ (prefixWord ++ tailWord_6532872).sum := by decide
  have hdescent : baseEnd_6532872 < baseStart_6532872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532881 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_6532881 : Nat := 118140960795 + 6532881 * 2 ^ 59
def prefixEnd_6532881 : Nat := 4983230072969 + 3 ^ 40 * 6532881 * 2
def baseEnd_6532881 : Nat := 3354508011625159806743333

theorem tailTrace_6532881 : CollatzResearch.WordTrace tailWord_6532881 prefixEnd_6532881 3354508011625159806743333 := by
  unfold tailWord_6532881
  simp only [CollatzResearch.WordTrace]
  refine ⟨238273745045495339092326497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158849163363663559394884331 238273745045495339092326497)
  ·
    refine ⟨178705308784121504319244873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238273745045495339092326497 178705308784121504319244873)
    ·
      refine ⟨134028981588091128239433655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178705308784121504319244873 134028981588091128239433655)
      ·
        refine ⟨201043472382136692359150483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134028981588091128239433655 201043472382136692359150483)
        ·
          refine ⟨301565208573205038538725725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201043472382136692359150483 301565208573205038538725725)
          ·
            refine ⟨113086953214951889452022147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301565208573205038538725725 113086953214951889452022147)
            ·
              refine ⟨169630429822427834178033221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113086953214951889452022147 169630429822427834178033221)
              ·
                refine ⟨31805705591705218908381229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169630429822427834178033221 31805705591705218908381229)
                ·
                  refine ⟨11927139596889457090642961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31805705591705218908381229 11927139596889457090642961)
                  ·
                    refine ⟨8945354697667092817982221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11927139596889457090642961 8945354697667092817982221)
                    ·
                      refine ⟨3354508011625159806743333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945354697667092817982221 3354508011625159806743333)
                      ·
                        rfl

theorem cell23_6532881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_6532881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532881 prefixEnd_6532881 := by exact prefixLift 6532881
  have htrace : WordTrace (prefixWord ++ tailWord_6532881) baseStart_6532881 baseEnd_6532881 := by
    simpa [prefixWord, tailWord_6532881, baseEnd_6532881] using wordTrace_append hprefix tailTrace_6532881
  have hstable : (prefixWord ++ tailWord_6532881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532881).length < 2 ^ (prefixWord ++ tailWord_6532881).sum := by decide
  have hdescent : baseEnd_6532881 < baseStart_6532881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532898 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_6532898 : Nat := 118140960795 + 6532898 * 2 ^ 59
def prefixEnd_6532898 : Nat := 4983230072969 + 3 ^ 40 * 6532898 * 2
def baseEnd_6532898 : Nat := 3354516740796286240230755

theorem tailTrace_6532898 : CollatzResearch.WordTrace tailWord_6532898 prefixEnd_6532898 3354516740796286240230755 := by
  unfold tailWord_6532898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568591271608437748923837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158849576724289167330463565 59568591271608437748923837)
  ·
    refine ⟨22338221726853164155846439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59568591271608437748923837 22338221726853164155846439)
    ·
      refine ⟨33507332590279746233769659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22338221726853164155846439 33507332590279746233769659)
      ·
        refine ⟨50260998885419619350654489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33507332590279746233769659 50260998885419619350654489)
        ·
          refine ⟨37695749164064714512990867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50260998885419619350654489 37695749164064714512990867)
          ·
            refine ⟨56543623746097071769486301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37695749164064714512990867 56543623746097071769486301)
            ·
              refine ⟨21203858904786401913557363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56543623746097071769486301 21203858904786401913557363)
              ·
                refine ⟨31805788357179602870336045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21203858904786401913557363 31805788357179602870336045)
                ·
                  refine ⟨11927170633942351076376017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31805788357179602870336045 11927170633942351076376017)
                  ·
                    refine ⟨8945377975456763307282013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11927170633942351076376017 8945377975456763307282013)
                    ·
                      refine ⟨3354516740796286240230755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945377975456763307282013 3354516740796286240230755)
                      ·
                        rfl

theorem cell23_6532898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_6532898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532898 prefixEnd_6532898 := by exact prefixLift 6532898
  have htrace : WordTrace (prefixWord ++ tailWord_6532898) baseStart_6532898 baseEnd_6532898 := by
    simpa [prefixWord, tailWord_6532898, baseEnd_6532898] using wordTrace_append hprefix tailTrace_6532898
  have hstable : (prefixWord ++ tailWord_6532898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532898).length < 2 ^ (prefixWord ++ tailWord_6532898).sum := by decide
  have hdescent : baseEnd_6532898 < baseStart_6532898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532911 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_6532911 : Nat := 118140960795 + 6532911 * 2 ^ 59
def prefixEnd_6532911 : Nat := 4983230072969 + 3 ^ 40 * 6532911 * 2
def baseEnd_6532911 : Nat := 3354523416044794689368195

theorem tailTrace_6532911 : CollatzResearch.WordTrace tailWord_6532911 prefixEnd_6532911 3354523416044794689368195 := by
  unfold tailWord_6532911
  simp only [CollatzResearch.WordTrace]
  refine ⟨238274839235386654215918587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158849892823591102810612391 238274839235386654215918587)
  ·
    refine ⟨357412258853079981323877881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238274839235386654215918587 357412258853079981323877881)
    ·
      refine ⟨268059194139809985992908411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357412258853079981323877881 268059194139809985992908411)
      ·
        refine ⟨402088791209714978989362617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268059194139809985992908411 402088791209714978989362617)
        ·
          refine ⟨301566593407286234242021963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402088791209714978989362617 301566593407286234242021963)
          ·
            refine ⟨452349890110929351363032945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301566593407286234242021963 452349890110929351363032945)
            ·
              refine ⟨339262417583197013522274709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452349890110929351363032945 339262417583197013522274709)
              ·
                refine ⟨15902925824212360008856627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 339262417583197013522274709 15902925824212360008856627)
                ·
                  refine ⟨23854388736318540013284941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15902925824212360008856627 23854388736318540013284941)
                  ·
                    refine ⟨8945395776119452504981853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23854388736318540013284941 8945395776119452504981853)
                    ·
                      refine ⟨3354523416044794689368195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945395776119452504981853 3354523416044794689368195)
                      ·
                        rfl

theorem cell23_6532911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_6532911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532911 prefixEnd_6532911 := by exact prefixLift 6532911
  have htrace : WordTrace (prefixWord ++ tailWord_6532911) baseStart_6532911 baseEnd_6532911 := by
    simpa [prefixWord, tailWord_6532911, baseEnd_6532911] using wordTrace_append hprefix tailTrace_6532911
  have hstable : (prefixWord ++ tailWord_6532911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532911).length < 2 ^ (prefixWord ++ tailWord_6532911).sum := by decide
  have hdescent : baseEnd_6532911 < baseStart_6532911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532915 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 1, 5]
def baseStart_6532915 : Nat := 118140960795 + 6532915 * 2 ^ 59
def prefixEnd_6532915 : Nat := 4983230072969 + 3 ^ 40 * 6532915 * 2
def baseEnd_6532915 : Nat := 3354525469967412673718177

theorem tailTrace_6532915 : CollatzResearch.WordTrace tailWord_6532915 prefixEnd_6532915 3354525469967412673718177 := by
  unfold tailWord_6532915
  simp only [CollatzResearch.WordTrace]
  refine ⟨238274985127372162899064199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158849990084914775266042799 238274985127372162899064199)
  ·
    refine ⟨357412477691058244348596299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238274985127372162899064199 357412477691058244348596299)
    ·
      refine ⟨536118716536587366522894449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357412477691058244348596299 536118716536587366522894449)
      ·
        refine ⟨402089037402440524892170837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536118716536587366522894449 402089037402440524892170837)
        ·
          refine ⟨4711980907059849901080127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 402089037402440524892170837 4711980907059849901080127)
          ·
            refine ⟨7067971360589774851620191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4711980907059849901080127 7067971360589774851620191)
            ·
              refine ⟨10601957040884662277430287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067971360589774851620191 10601957040884662277430287)
              ·
                refine ⟨15902935561326993416145431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10601957040884662277430287 15902935561326993416145431)
                ·
                  refine ⟨23854403341990490124218147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15902935561326993416145431 23854403341990490124218147)
                  ·
                    refine ⟨35781605012985735186327221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23854403341990490124218147 35781605012985735186327221)
                    ·
                      refine ⟨3354525469967412673718177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35781605012985735186327221 3354525469967412673718177)
                      ·
                        rfl

theorem cell23_6532915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 1, 5].length) (baseStart_6532915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532915 prefixEnd_6532915 := by exact prefixLift 6532915
  have htrace : WordTrace (prefixWord ++ tailWord_6532915) baseStart_6532915 baseEnd_6532915 := by
    simpa [prefixWord, tailWord_6532915, baseEnd_6532915] using wordTrace_append hprefix tailTrace_6532915
  have hstable : (prefixWord ++ tailWord_6532915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532915).length < 2 ^ (prefixWord ++ tailWord_6532915).sum := by decide
  have hdescent : baseEnd_6532915 < baseStart_6532915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532938 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_6532938 : Nat := 118140960795 + 6532938 * 2 ^ 59
def prefixEnd_6532938 : Nat := 4983230072969 + 3 ^ 40 * 6532938 * 2
def baseEnd_6532938 : Nat := 3354537280022466083730571

theorem tailTrace_6532938 : CollatzResearch.WordTrace tailWord_6532938 prefixEnd_6532938 3354537280022466083730571 := by
  unfold tailWord_6532938
  simp only [CollatzResearch.WordTrace]
  refine ⟨59568956001572209456787867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158850549337525891884767645 59568956001572209456787867)
  ·
    refine ⟨89353434002358314185181801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59568956001572209456787867 89353434002358314185181801)
    ·
      refine ⟨67015075501768735638886351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89353434002358314185181801 67015075501768735638886351)
      ·
        refine ⟨100522613252653103458329527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67015075501768735638886351 100522613252653103458329527)
        ·
          refine ⟨150783919878979655187494291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100522613252653103458329527 150783919878979655187494291)
          ·
            refine ⟨226175879818469482781241437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150783919878979655187494291 226175879818469482781241437)
            ·
              refine ⟨84815954931926056042965539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226175879818469482781241437 84815954931926056042965539)
              ·
                refine ⟨127223932397889084064448309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84815954931926056042965539 127223932397889084064448309)
                ·
                  refine ⟨11927243662302101631042029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127223932397889084064448309 11927243662302101631042029)
                  ·
                    refine ⟨4472716373363288111640761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11927243662302101631042029 4472716373363288111640761)
                    ·
                      refine ⟨3354537280022466083730571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472716373363288111640761 3354537280022466083730571)
                      ·
                        rfl

theorem cell23_6532938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_6532938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532938 prefixEnd_6532938 := by exact prefixLift 6532938
  have htrace : WordTrace (prefixWord ++ tailWord_6532938) baseStart_6532938 baseEnd_6532938 := by
    simpa [prefixWord, tailWord_6532938, baseEnd_6532938] using wordTrace_append hprefix tailTrace_6532938
  have hstable : (prefixWord ++ tailWord_6532938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532938).length < 2 ^ (prefixWord ++ tailWord_6532938).sum := by decide
  have hdescent : baseEnd_6532938 < baseStart_6532938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532945 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_6532945 : Nat := 118140960795 + 6532945 * 2 ^ 59
def prefixEnd_6532945 : Nat := 4983230072969 + 3 ^ 40 * 6532945 * 2
def baseEnd_6532945 : Nat := 3354540874387047556343039

theorem tailTrace_6532945 : CollatzResearch.WordTrace tailWord_6532945 prefixEnd_6532945 3354540874387047556343039 := by
  unfold tailWord_6532945
  simp only [CollatzResearch.WordTrace]
  refine ⟨238276079317263478022656289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158850719544842318681770859 238276079317263478022656289)
  ·
    refine ⟨178707059487947608516992217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238276079317263478022656289 178707059487947608516992217)
    ·
      refine ⟨134030294615960706387744163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178707059487947608516992217 134030294615960706387744163)
      ·
        refine ⟨201045441923941059581616245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134030294615960706387744163 201045441923941059581616245)
        ·
          refine ⟨18848010180369474335776523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201045441923941059581616245 18848010180369474335776523)
          ·
            refine ⟨28272015270554211503664785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18848010180369474335776523 28272015270554211503664785)
            ·
              refine ⟨21204011452915658627748589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28272015270554211503664785 21204011452915658627748589)
              ·
                refine ⟨7951504294843371985405721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21204011452915658627748589 7951504294843371985405721)
                ·
                  refine ⟨5963628221132528989054291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7951504294843371985405721 5963628221132528989054291)
                  ·
                    refine ⟨8945442331698793483581437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963628221132528989054291 8945442331698793483581437)
                    ·
                      refine ⟨3354540874387047556343039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945442331698793483581437 3354540874387047556343039)
                      ·
                        rfl

theorem cell23_6532945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_6532945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532945 prefixEnd_6532945 := by exact prefixLift 6532945
  have htrace : WordTrace (prefixWord ++ tailWord_6532945) baseStart_6532945 baseEnd_6532945 := by
    simpa [prefixWord, tailWord_6532945, baseEnd_6532945] using wordTrace_append hprefix tailTrace_6532945
  have hstable : (prefixWord ++ tailWord_6532945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532945).length < 2 ^ (prefixWord ++ tailWord_6532945).sum := by decide
  have hdescent : baseEnd_6532945 < baseStart_6532945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532972 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 1, 3, 2]
def baseStart_6532972 : Nat := 118140960795 + 6532972 * 2 ^ 59
def prefixEnd_6532972 : Nat := 4983230072969 + 3 ^ 40 * 6532972 * 2
def baseEnd_6532972 : Nat := 3354554738364718950705415

theorem tailTrace_6532972 : CollatzResearch.WordTrace tailWord_6532972 prefixEnd_6532972 3354554738364718950705415 := by
  unfold tailWord_6532972
  simp only [CollatzResearch.WordTrace]
  refine ⟨119138532044082830816944585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158851376058777107755926113 119138532044082830816944585)
  ·
    refine ⟨89353899033062123112708439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119138532044082830816944585 89353899033062123112708439)
    ·
      refine ⟨134030848549593184669062659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89353899033062123112708439 134030848549593184669062659)
      ·
        refine ⟨201046272824389777003593989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134030848549593184669062659 201046272824389777003593989)
        ·
          refine ⟨37696176154573083188173873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201046272824389777003593989 37696176154573083188173873)
          ·
            refine ⟨28272132115929812391130405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37696176154573083188173873 28272132115929812391130405)
            ·
              refine ⟨5301024771736839823336951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28272132115929812391130405 5301024771736839823336951)
              ·
                refine ⟨7951537157605259735005427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301024771736839823336951 7951537157605259735005427)
                ·
                  refine ⟨11927305736407889602508141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951537157605259735005427 11927305736407889602508141)
                  ·
                    refine ⟨4472739651152958600940553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11927305736407889602508141 4472739651152958600940553)
                    ·
                      refine ⟨3354554738364718950705415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472739651152958600940553 3354554738364718950705415)
                      ·
                        rfl

theorem cell23_6532972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_6532972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532972 prefixEnd_6532972 := by exact prefixLift 6532972
  have htrace : WordTrace (prefixWord ++ tailWord_6532972) baseStart_6532972 baseEnd_6532972 := by
    simpa [prefixWord, tailWord_6532972, baseEnd_6532972] using wordTrace_append hprefix tailTrace_6532972
  have hstable : (prefixWord ++ tailWord_6532972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532972).length < 2 ^ (prefixWord ++ tailWord_6532972).sum := by decide
  have hdescent : baseEnd_6532972 < baseStart_6532972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6532985 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6532985 : Nat := 118140960795 + 6532985 * 2 ^ 59
def prefixEnd_6532985 : Nat := 4983230072969 + 3 ^ 40 * 6532985 * 2
def baseEnd_6532985 : Nat := 3354561413613227399842855

theorem tailTrace_6532985 : CollatzResearch.WordTrace tailWord_6532985 prefixEnd_6532985 3354561413613227399842855 := by
  unfold tailWord_6532985
  simp only [CollatzResearch.WordTrace]
  refine ⟨238277538237118564854112409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158851692158079043236074939 238277538237118564854112409)
  ·
    refine ⟨178708153677838923640584307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238277538237118564854112409 178708153677838923640584307)
    ·
      refine ⟨268062230516758385460876461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178708153677838923640584307 268062230516758385460876461)
      ·
        refine ⟨100523336443784394547828673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268062230516758385460876461 100523336443784394547828673)
        ·
          refine ⟨75392502332838295910871505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100523336443784394547828673 75392502332838295910871505)
          ·
            refine ⟨56544376749628721933153629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75392502332838295910871505 56544376749628721933153629)
            ·
              refine ⟨21204141281110770724932611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56544376749628721933153629 21204141281110770724932611)
              ·
                refine ⟨31806211921666156087398917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21204141281110770724932611 31806211921666156087398917)
                ·
                  refine ⟨5963664735312404266387297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31806211921666156087398917 5963664735312404266387297)
                  ·
                    refine ⟨4472748551484303199790473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5963664735312404266387297 4472748551484303199790473)
                    ·
                      refine ⟨3354561413613227399842855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472748551484303199790473 3354561413613227399842855)
                      ·
                        rfl

theorem cell23_6532985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6532985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6532985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6532985 prefixEnd_6532985 := by exact prefixLift 6532985
  have htrace : WordTrace (prefixWord ++ tailWord_6532985) baseStart_6532985 baseEnd_6532985 := by
    simpa [prefixWord, tailWord_6532985, baseEnd_6532985] using wordTrace_append hprefix tailTrace_6532985
  have hstable : (prefixWord ++ tailWord_6532985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6532985).length < 2 ^ (prefixWord ++ tailWord_6532985).sum := by decide
  have hdescent : baseEnd_6532985 < baseStart_6532985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6532985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533022 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6533022 : Nat := 118140960795 + 6533022 * 2 ^ 59
def prefixEnd_6533022 : Nat := 4983230072969 + 3 ^ 40 * 6533022 * 2
def baseEnd_6533022 : Nat := 3354580412397443755080185

theorem tailTrace_6533022 : CollatzResearch.WordTrace tailWord_6533022 prefixEnd_6533022 3354580412397443755080185 := by
  unfold tailWord_6533022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29784860967248065021651165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158852591825323013448806213 29784860967248065021651165)
  ·
    refine ⟨11169322862718024383119187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29784860967248065021651165 11169322862718024383119187)
    ·
      refine ⟨16753984294077036574678781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11169322862718024383119187 16753984294077036574678781)
      ·
        refine ⟨6282744110278888715504543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16753984294077036574678781 6282744110278888715504543)
        ·
          refine ⟨9424116165418333073256815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282744110278888715504543 9424116165418333073256815)
          ·
            refine ⟨14136174248127499609885223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424116165418333073256815 14136174248127499609885223)
            ·
              refine ⟨21204261372191249414827835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14136174248127499609885223 21204261372191249414827835)
              ·
                refine ⟨31806392058286874122241753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21204261372191249414827835 31806392058286874122241753)
                ·
                  refine ⟨23854794043715155591681315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31806392058286874122241753 23854794043715155591681315)
                  ·
                    refine ⟨35782191065572733387521973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23854794043715155591681315 35782191065572733387521973)
                    ·
                      refine ⟨3354580412397443755080185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35782191065572733387521973 3354580412397443755080185)
                      ·
                        rfl

theorem cell23_6533022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6533022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533022 prefixEnd_6533022 := by exact prefixLift 6533022
  have htrace : WordTrace (prefixWord ++ tailWord_6533022) baseStart_6533022 baseEnd_6533022 := by
    simpa [prefixWord, tailWord_6533022, baseEnd_6533022] using wordTrace_append hprefix tailTrace_6533022
  have hstable : (prefixWord ++ tailWord_6533022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533022).length < 2 ^ (prefixWord ++ tailWord_6533022).sum := by decide
  have hdescent : baseEnd_6533022 < baseStart_6533022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533125 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_6533125 : Nat := 118140960795 + 6533125 * 2 ^ 59
def prefixEnd_6533125 : Nat := 4983230072969 + 3 ^ 40 * 6533125 * 2
def baseEnd_6533125 : Nat := 3354633300904856852092211

theorem tailTrace_6533125 : CollatzResearch.WordTrace tailWord_6533125 prefixEnd_6533125 3354633300904856852092211 := by
  unfold tailWord_6533125
  simp only [CollatzResearch.WordTrace]
  refine ⟨238282644456611368764208829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158855096304407579176139219 238282644456611368764208829)
  ·
    refine ⟨89355991671229263286578311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238282644456611368764208829 89355991671229263286578311)
    ·
      refine ⟨134033987506843894929867467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89355991671229263286578311 134033987506843894929867467)
      ·
        refine ⟨201050981260265842394801201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134033987506843894929867467 201050981260265842394801201)
        ·
          refine ⟨150788235945199381796100901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201050981260265842394801201 150788235945199381796100901)
          ·
            refine ⟨28272794239724884086768919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150788235945199381796100901 28272794239724884086768919)
            ·
              refine ⟨42409191359587326130153379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28272794239724884086768919 42409191359587326130153379)
              ·
                refine ⟨63613787039380989195230069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42409191359587326130153379 63613787039380989195230069)
                ·
                  refine ⟨5963792534941967737052819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63613787039380989195230069 5963792534941967737052819)
                  ·
                    refine ⟨8945688802412951605579229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5963792534941967737052819 8945688802412951605579229)
                    ·
                      refine ⟨3354633300904856852092211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945688802412951605579229 3354633300904856852092211)
                      ·
                        rfl

theorem cell23_6533125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_6533125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533125 prefixEnd_6533125 := by exact prefixLift 6533125
  have htrace : WordTrace (prefixWord ++ tailWord_6533125) baseStart_6533125 baseEnd_6533125 := by
    simpa [prefixWord, tailWord_6533125, baseEnd_6533125] using wordTrace_append hprefix tailTrace_6533125
  have hstable : (prefixWord ++ tailWord_6533125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533125).length < 2 ^ (prefixWord ++ tailWord_6533125).sum := by decide
  have hdescent : baseEnd_6533125 < baseStart_6533125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533126 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6533126 : Nat := 118140960795 + 6533126 * 2 ^ 59
def prefixEnd_6533126 : Nat := 4983230072969 + 3 ^ 40 * 6533126 * 2
def baseEnd_6533126 : Nat := 3354633814385511348179707

theorem tailTrace_6533126 : CollatzResearch.WordTrace tailWord_6533126 prefixEnd_6533126 3354633814385511348179707 := by
  unfold tailWord_6533126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446333779050242060468601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158855120619738497289996821 7446333779050242060468601)
  ·
    refine ⟨5584750334287681545351451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7446333779050242060468601 5584750334287681545351451)
    ·
      refine ⟨8377125501431522318027177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584750334287681545351451 8377125501431522318027177)
      ·
        refine ⟨6282844126073641738520383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377125501431522318027177 6282844126073641738520383)
        ·
          refine ⟨9424266189110462607780575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282844126073641738520383 9424266189110462607780575)
          ·
            refine ⟨14136399283665693911670863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424266189110462607780575 14136399283665693911670863)
            ·
              refine ⟨21204598925498540867506295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14136399283665693911670863 21204598925498540867506295)
              ·
                refine ⟨31806898388247811301259443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21204598925498540867506295 31806898388247811301259443)
                ·
                  refine ⟨47710347582371716951889165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31806898388247811301259443 47710347582371716951889165)
                  ·
                    refine ⟨17891380343389393856958437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47710347582371716951889165 17891380343389393856958437)
                    ·
                      refine ⟨3354633814385511348179707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17891380343389393856958437 3354633814385511348179707)
                      ·
                        rfl

theorem cell23_6533126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6533126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533126 prefixEnd_6533126 := by exact prefixLift 6533126
  have htrace : WordTrace (prefixWord ++ tailWord_6533126) baseStart_6533126 baseEnd_6533126 := by
    simpa [prefixWord, tailWord_6533126, baseEnd_6533126] using wordTrace_append hprefix tailTrace_6533126
  have hstable : (prefixWord ++ tailWord_6533126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533126).length < 2 ^ (prefixWord ++ tailWord_6533126).sum := by decide
  have hdescent : baseEnd_6533126 < baseStart_6533126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533128 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_6533128 : Nat := 118140960795 + 6533128 * 2 ^ 59
def prefixEnd_6533128 : Nat := 4983230072969 + 3 ^ 40 * 6533128 * 2
def baseEnd_6533128 : Nat := 1118211613782273446784899

theorem tailTrace_6533128 : CollatzResearch.WordTrace tailWord_6533128 prefixEnd_6533128 1118211613782273446784899 := by
  unfold tailWord_6533128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119141376937800250138284019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158855169250400333517712025 119141376937800250138284019)
  ·
    refine ⟨178712065406700375207426029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119141376937800250138284019 178712065406700375207426029)
    ·
      refine ⟨67017024527512640702784761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178712065406700375207426029 67017024527512640702784761)
      ·
        refine ⟨50262768395634480527088571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67017024527512640702784761 50262768395634480527088571)
        ·
          refine ⟨75394152593451720790632857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50262768395634480527088571 75394152593451720790632857)
          ·
            refine ⟨56545614445088790592974643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75394152593451720790632857 56545614445088790592974643)
            ·
              refine ⟨84818421667633185889461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56545614445088790592974643 84818421667633185889461965)
              ·
                refine ⟨31806908125362444708548237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84818421667633185889461965 31806908125362444708548237)
                ·
                  refine ⟨11927590547010916765705589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31806908125362444708548237 11927590547010916765705589)
                  ·
                    refine ⟨1118211613782273446784899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11927590547010916765705589 1118211613782273446784899)
                    ·
                      rfl

theorem cell23_6533128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_6533128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533128 prefixEnd_6533128 := by exact prefixLift 6533128
  have htrace : WordTrace (prefixWord ++ tailWord_6533128) baseStart_6533128 baseEnd_6533128 := by
    simpa [prefixWord, tailWord_6533128, baseEnd_6533128] using wordTrace_append hprefix tailTrace_6533128
  have hstable : (prefixWord ++ tailWord_6533128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533128).length < 2 ^ (prefixWord ++ tailWord_6533128).sum := by decide
  have hdescent : baseEnd_6533128 < baseStart_6533128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533168 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_6533168 : Nat := 118140960795 + 6533168 * 2 ^ 59
def prefixEnd_6533168 : Nat := 4983230072969 + 3 ^ 40 * 6533168 * 2
def baseEnd_6533168 : Nat := 3354655380573000183854513

theorem tailTrace_6533168 : CollatzResearch.WordTrace tailWord_6533168 prefixEnd_6533168 3354655380573000183854513 := by
  unfold tailWord_6533168
  simp only [CollatzResearch.WordTrace]
  refine ⟨119142106397727793554012079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158856141863637058072016105 119142106397727793554012079)
  ·
    refine ⟨178713159596591690331018119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119142106397727793554012079 178713159596591690331018119)
    ·
      refine ⟨268069739394887535496527179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178713159596591690331018119 268069739394887535496527179)
      ·
        refine ⟨402104609092331303244790769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268069739394887535496527179 402104609092331303244790769)
        ·
          refine ⟨301578456819248477433593077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402104609092331303244790769 301578456819248477433593077)
          ·
            refine ⟨28272980326804544759399351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301578456819248477433593077 28272980326804544759399351)
            ·
              refine ⟨42409470490206817139099027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28272980326804544759399351 42409470490206817139099027)
              ·
                refine ⟨63614205735310225708648541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42409470490206817139099027 63614205735310225708648541)
                ·
                  refine ⟨23855327150741334640743203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63614205735310225708648541 23855327150741334640743203)
                  ·
                    refine ⟨35782990726112001961114805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23855327150741334640743203 35782990726112001961114805)
                    ·
                      refine ⟨3354655380573000183854513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35782990726112001961114805 3354655380573000183854513)
                      ·
                        rfl

theorem cell23_6533168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_6533168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533168 prefixEnd_6533168 := by exact prefixLift 6533168
  have htrace : WordTrace (prefixWord ++ tailWord_6533168) baseStart_6533168 baseEnd_6533168 := by
    simpa [prefixWord, tailWord_6533168, baseEnd_6533168] using wordTrace_append hprefix tailTrace_6533168
  have hstable : (prefixWord ++ tailWord_6533168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533168).length < 2 ^ (prefixWord ++ tailWord_6533168).sum := by decide
  have hdescent : baseEnd_6533168 < baseStart_6533168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533175 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 2, 4]
def baseStart_6533175 : Nat := 118140960795 + 6533175 * 2 ^ 59
def prefixEnd_6533175 : Nat := 4983230072969 + 3 ^ 40 * 6533175 * 2
def baseEnd_6533175 : Nat := 1118219658312527218822327

theorem tailTrace_6533175 : CollatzResearch.WordTrace tailWord_6533175 prefixEnd_6533175 1118219658312527218822327 := by
  unfold tailWord_6533175
  simp only [CollatzResearch.WordTrace]
  refine ⟨238284468106430227303528979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158856312070953484869019319 238284468106430227303528979)
  ·
    refine ⟨357426702159645340955293469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238284468106430227303528979 357426702159645340955293469)
    ·
      refine ⟨134035013309867002858235051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357426702159645340955293469 134035013309867002858235051)
      ·
        refine ⟨201052519964800504287352577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134035013309867002858235051 201052519964800504287352577)
        ·
          refine ⟨150789389973600378215514433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201052519964800504287352577 150789389973600378215514433)
          ·
            refine ⟨113092042480200283661635825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150789389973600378215514433 113092042480200283661635825)
            ·
              refine ⟨84819031860150212746226869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113092042480200283661635825 84819031860150212746226869)
              ·
                refine ⟨7951784236889082444958769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84819031860150212746226869 7951784236889082444958769)
                ·
                  refine ⟨5963838177666811833719077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7951784236889082444958769 5963838177666811833719077)
                  ·
                    refine ⟨1118219658312527218822327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5963838177666811833719077 1118219658312527218822327)
                    ·
                      rfl

theorem cell23_6533175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_6533175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533175 prefixEnd_6533175 := by exact prefixLift 6533175
  have htrace : WordTrace (prefixWord ++ tailWord_6533175) baseStart_6533175 baseEnd_6533175 := by
    simpa [prefixWord, tailWord_6533175, baseEnd_6533175] using wordTrace_append hprefix tailTrace_6533175
  have hstable : (prefixWord ++ tailWord_6533175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533175).length < 2 ^ (prefixWord ++ tailWord_6533175).sum := by decide
  have hdescent : baseEnd_6533175 < baseStart_6533175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533202 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_6533202 : Nat := 118140960795 + 6533202 * 2 ^ 59
def prefixEnd_6533202 : Nat := 4983230072969 + 3 ^ 40 * 6533202 * 2
def baseEnd_6533202 : Nat := 3354672838915253050829357

theorem tailTrace_6533202 : CollatzResearch.WordTrace tailWord_6533202 prefixEnd_6533202 3354672838915253050829357 := by
  unfold tailWord_6533202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571363219333102728690465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158856968584888273943174573 59571363219333102728690465)
  ·
    refine ⟨44678522414499827046517849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59571363219333102728690465 44678522414499827046517849)
    ·
      refine ⟨33508891810874870284888387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44678522414499827046517849 33508891810874870284888387)
      ·
        refine ⟨50263337716312305427332581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33508891810874870284888387 50263337716312305427332581)
        ·
          refine ⟨9424375821808557267624859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50263337716312305427332581 9424375821808557267624859)
          ·
            refine ⟨14136563732712835901437289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424375821808557267624859 14136563732712835901437289)
            ·
              refine ⟨10602422799534626926077967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14136563732712835901437289 10602422799534626926077967)
              ·
                refine ⟨15903634199301940389116951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10602422799534626926077967 15903634199301940389116951)
                ·
                  refine ⟨23855451298952910583675427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15903634199301940389116951 23855451298952910583675427)
                  ·
                    refine ⟨35783176948429365875513141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23855451298952910583675427 35783176948429365875513141)
                    ·
                      refine ⟨3354672838915253050829357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35783176948429365875513141 3354672838915253050829357)
                      ·
                        rfl

theorem cell23_6533202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_6533202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533202 prefixEnd_6533202 := by exact prefixLift 6533202
  have htrace : WordTrace (prefixWord ++ tailWord_6533202) baseStart_6533202 baseEnd_6533202 := by
    simpa [prefixWord, tailWord_6533202, baseEnd_6533202] using wordTrace_append hprefix tailTrace_6533202
  have hstable : (prefixWord ++ tailWord_6533202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533202).length < 2 ^ (prefixWord ++ tailWord_6533202).sum := by decide
  have hdescent : baseEnd_6533202 < baseStart_6533202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533226 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_6533226 : Nat := 118140960795 + 6533226 * 2 ^ 59
def prefixEnd_6533226 : Nat := 4983230072969 + 3 ^ 40 * 6533226 * 2
def baseEnd_6533226 : Nat := 1118228387483653652309749

theorem tailTrace_6533226 : CollatzResearch.WordTrace tailWord_6533226 prefixEnd_6533226 1118228387483653652309749 := by
  unfold tailWord_6533226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571582057311365753408883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158857552152830308675757021 59571582057311365753408883)
  ·
    refine ⟨89357373085967048630113325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59571582057311365753408883 89357373085967048630113325)
    ·
      refine ⟨33509014907237643236292497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89357373085967048630113325 33509014907237643236292497)
      ·
        refine ⟨25131761180428232427219373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33509014907237643236292497 25131761180428232427219373)
        ·
          refine ⟨9424410442660587160207265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25131761180428232427219373 9424410442660587160207265)
          ·
            refine ⟨7068307831995440370155449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424410442660587160207265 7068307831995440370155449)
            ·
              refine ⟨5301230873996580277616587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068307831995440370155449 5301230873996580277616587)
              ·
                refine ⟨7951846310994870416424881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301230873996580277616587 7951846310994870416424881)
                ·
                  refine ⟨5963884733246152812318661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7951846310994870416424881 5963884733246152812318661)
                  ·
                    refine ⟨1118228387483653652309749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5963884733246152812318661 1118228387483653652309749)
                    ·
                      rfl

theorem cell23_6533226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_6533226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533226 prefixEnd_6533226 := by exact prefixLift 6533226
  have htrace : WordTrace (prefixWord ++ tailWord_6533226) baseStart_6533226 baseEnd_6533226 := by
    simpa [prefixWord, tailWord_6533226, baseEnd_6533226] using wordTrace_append hprefix tailTrace_6533226
  have hstable : (prefixWord ++ tailWord_6533226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533226).length < 2 ^ (prefixWord ++ tailWord_6533226).sum := by decide
  have hdescent : baseEnd_6533226 < baseStart_6533226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533248 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_6533248 : Nat := 118140960795 + 6533248 * 2 ^ 59
def prefixEnd_6533248 : Nat := 4983230072969 + 3 ^ 40 * 6533248 * 2
def baseEnd_6533248 : Nat := 1118232153008453290284715

theorem tailTrace_6533248 : CollatzResearch.WordTrace tailWord_6533248 prefixEnd_6533248 1118232153008453290284715 := by
  unfold tailWord_6533248
  simp only [CollatzResearch.WordTrace]
  refine ⟨119143565317582880385468199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158858087090110507180624265 119143565317582880385468199)
  ·
    refine ⟨178715347976374320578202299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119143565317582880385468199 178715347976374320578202299)
    ·
      refine ⟨268073021964561480867303449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178715347976374320578202299 268073021964561480867303449)
      ·
        refine ⟨201054766473421110650477587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268073021964561480867303449 201054766473421110650477587)
        ·
          refine ⟨301582149710131665975716381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201054766473421110650477587 301582149710131665975716381)
          ·
            refine ⟨113093306141299374740893643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301582149710131665975716381 113093306141299374740893643)
            ·
              refine ⟨169639959211949062111340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113093306141299374740893643 169639959211949062111340465)
              ·
                refine ⟨127229969408961796583505349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169639959211949062111340465 127229969408961796583505349)
                ·
                  refine ⟨23855619264180336859407253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127229969408961796583505349 23855619264180336859407253)
                  ·
                    refine ⟨1118232153008453290284715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23855619264180336859407253 1118232153008453290284715)
                    ·
                      rfl

theorem cell23_6533248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_6533248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533248 prefixEnd_6533248 := by exact prefixLift 6533248
  have htrace : WordTrace (prefixWord ++ tailWord_6533248) baseStart_6533248 baseEnd_6533248 := by
    simpa [prefixWord, tailWord_6533248, baseEnd_6533248] using wordTrace_append hprefix tailTrace_6533248
  have hstable : (prefixWord ++ tailWord_6533248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533248).length < 2 ^ (prefixWord ++ tailWord_6533248).sum := by decide
  have hdescent : baseEnd_6533248 < baseStart_6533248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533282 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6533282 : Nat := 118140960795 + 6533282 * 2 ^ 59
def prefixEnd_6533282 : Nat := 4983230072969 + 3 ^ 40 * 6533282 * 2
def baseEnd_6533282 : Nat := 1118237972455870912609663

theorem tailTrace_6533282 : CollatzResearch.WordTrace tailWord_6533282 prefixEnd_6533282 1118237972455870912609663 := by
  unfold tailWord_6533282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59572092679260646144418525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158858913811361723051782733 59572092679260646144418525)
  ·
    refine ⟨22339534754722742304156947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59572092679260646144418525 22339534754722742304156947)
    ·
      refine ⟨33509302132084113456235421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22339534754722742304156947 33509302132084113456235421)
      ·
        refine ⟨12565988299531542546088283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33509302132084113456235421 12565988299531542546088283)
        ·
          refine ⟨18848982449297313819132425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12565988299531542546088283 18848982449297313819132425)
          ·
            refine ⟨14136736836972985364349319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18848982449297313819132425 14136736836972985364349319)
            ·
              refine ⟨21205105255459478046523979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14136736836972985364349319 21205105255459478046523979)
              ·
                refine ⟨31807657883189217069785969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21205105255459478046523979 31807657883189217069785969)
                ·
                  refine ⟨23855743412391912802339477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31807657883189217069785969 23855743412391912802339477)
                  ·
                    refine ⟨1118237972455870912609663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23855743412391912802339477 1118237972455870912609663)
                    ·
                      rfl

theorem cell23_6533282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6533282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533282 prefixEnd_6533282 := by exact prefixLift 6533282
  have htrace : WordTrace (prefixWord ++ tailWord_6533282) baseStart_6533282 baseEnd_6533282 := by
    simpa [prefixWord, tailWord_6533282, baseEnd_6533282] using wordTrace_append hprefix tailTrace_6533282
  have hstable : (prefixWord ++ tailWord_6533282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533282).length < 2 ^ (prefixWord ++ tailWord_6533282).sum := by decide
  have hdescent : baseEnd_6533282 < baseStart_6533282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533285 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_6533285 : Nat := 118140960795 + 6533285 * 2 ^ 59
def prefixEnd_6533285 : Nat := 4983230072969 + 3 ^ 40 * 6533285 * 2
def baseEnd_6533285 : Nat := 3354715457809576226091475

theorem tailTrace_6533285 : CollatzResearch.WordTrace tailWord_6533285 prefixEnd_6533285 3354715457809576226091475 := by
  unfold tailWord_6533285
  simp only [CollatzResearch.WordTrace]
  refine ⟨238288480136031716090033309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158858986757354477393355539 238288480136031716090033309)
  ·
    refine ⟨89358180051011893533762491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238288480136031716090033309 89358180051011893533762491)
    ·
      refine ⟨134037270076517840300643737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89358180051011893533762491 134037270076517840300643737)
      ·
        refine ⟨100527952557388380225482803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134037270076517840300643737 100527952557388380225482803)
        ·
          refine ⟨150791928836082570338224205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100527952557388380225482803 150791928836082570338224205)
          ·
            refine ⟨56546973313530963876834077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150791928836082570338224205 56546973313530963876834077)
            ·
              refine ⟨21205114992574111453812779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56546973313530963876834077 21205114992574111453812779)
              ·
                refine ⟨31807672488861167180719169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21205114992574111453812779 31807672488861167180719169)
                ·
                  refine ⟨23855754366645875385539377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31807672488861167180719169 23855754366645875385539377)
                  ·
                    refine ⟨17891815774984406539154533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23855754366645875385539377 17891815774984406539154533)
                    ·
                      refine ⟨3354715457809576226091475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17891815774984406539154533 3354715457809576226091475)
                      ·
                        rfl

theorem cell23_6533285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_6533285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533285 prefixEnd_6533285 := by exact prefixLift 6533285
  have htrace : WordTrace (prefixWord ++ tailWord_6533285) baseStart_6533285 baseEnd_6533285 := by
    simpa [prefixWord, tailWord_6533285, baseEnd_6533285] using wordTrace_append hprefix tailTrace_6533285
  have hstable : (prefixWord ++ tailWord_6533285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533285).length < 2 ^ (prefixWord ++ tailWord_6533285).sum := by decide
  have hdescent : baseEnd_6533285 < baseStart_6533285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533305 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6533305 : Nat := 118140960795 + 6533305 * 2 ^ 59
def prefixEnd_6533305 : Nat := 4983230072969 + 3 ^ 40 * 6533305 * 2
def baseEnd_6533305 : Nat := 3354725727422666147841383

theorem tailTrace_6533305 : CollatzResearch.WordTrace tailWord_6533305 prefixEnd_6533305 3354725727422666147841383 := by
  unfold tailWord_6533305
  simp only [CollatzResearch.WordTrace]
  refine ⟨238289209595959259505761369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158859473063972839670507579 238289209595959259505761369)
  ·
    refine ⟨178716907196969444629321027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238289209595959259505761369 178716907196969444629321027)
    ·
      refine ⟨268075360795454166943981541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178716907196969444629321027 268075360795454166943981541)
      ·
        refine ⟨50264130149147656301996539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268075360795454166943981541 50264130149147656301996539)
        ·
          refine ⟨75396195223721484452994809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50264130149147656301996539 75396195223721484452994809)
          ·
            refine ⟨56547146417791113339746107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75396195223721484452994809 56547146417791113339746107)
            ·
              refine ⟨84820719626686670009619161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56547146417791113339746107 84820719626686670009619161)
              ·
                refine ⟨63615539720015002507214371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84820719626686670009619161 63615539720015002507214371)
                ·
                  refine ⟨95423309580022503760821557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63615539720015002507214371 95423309580022503760821557)
                  ·
                    refine ⟨8945935273127109727577021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95423309580022503760821557 8945935273127109727577021)
                    ·
                      refine ⟨3354725727422666147841383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8945935273127109727577021 3354725727422666147841383)
                      ·
                        rfl

theorem cell23_6533305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6533305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533305 prefixEnd_6533305 := by exact prefixLift 6533305
  have htrace : WordTrace (prefixWord ++ tailWord_6533305) baseStart_6533305 baseEnd_6533305 := by
    simpa [prefixWord, tailWord_6533305, baseEnd_6533305] using wordTrace_append hprefix tailTrace_6533305
  have hstable : (prefixWord ++ tailWord_6533305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533305).length < 2 ^ (prefixWord ++ tailWord_6533305).sum := by decide
  have hdescent : baseEnd_6533305 < baseStart_6533305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533310 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_6533310 : Nat := 118140960795 + 6533310 * 2 ^ 59
def prefixEnd_6533310 : Nat := 4983230072969 + 3 ^ 40 * 6533310 * 2
def baseEnd_6533310 : Nat := 3354728294825938628278861

theorem tailTrace_6533310 : CollatzResearch.WordTrace tailWord_6533310 prefixEnd_6533310 3354728294825938628278861 := by
  unfold tailWord_6533310
  simp only [CollatzResearch.WordTrace]
  refine ⟨29786173995117643169961673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158859594640627430239795589 29786173995117643169961673)
  ·
    refine ⟨22339630496338232377471255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29786173995117643169961673 22339630496338232377471255)
    ·
      refine ⟨33509445744507348566206883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22339630496338232377471255 33509445744507348566206883)
      ·
        refine ⟨50264168616761022849310325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33509445744507348566206883 50264168616761022849310325)
        ·
          refine ⟨4712265807821345892122843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50264168616761022849310325 4712265807821345892122843)
          ·
            refine ⟨7068398711732018838184265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712265807821345892122843 7068398711732018838184265)
            ·
              refine ⟨5301299033799014128638199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068398711732018838184265 5301299033799014128638199)
              ·
                refine ⟨7951948550698521192957299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301299033799014128638199 7951948550698521192957299)
                ·
                  refine ⟨11927922826047781789435949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7951948550698521192957299 11927922826047781789435949)
                  ·
                    refine ⟨4472971059767918171038481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11927922826047781789435949 4472971059767918171038481)
                    ·
                      refine ⟨3354728294825938628278861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472971059767918171038481 3354728294825938628278861)
                      ·
                        rfl

theorem cell23_6533310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_6533310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533310 prefixEnd_6533310 := by exact prefixLift 6533310
  have htrace : WordTrace (prefixWord ++ tailWord_6533310) baseStart_6533310 baseEnd_6533310 := by
    simpa [prefixWord, tailWord_6533310, baseEnd_6533310] using wordTrace_append hprefix tailTrace_6533310
  have hstable : (prefixWord ++ tailWord_6533310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533310).length < 2 ^ (prefixWord ++ tailWord_6533310).sum := by decide
  have hdescent : baseEnd_6533310 < baseStart_6533310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533312 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 5]
def baseStart_6533312 : Nat := 118140960795 + 6533312 * 2 ^ 59
def prefixEnd_6533312 : Nat := 4983230072969 + 3 ^ 40 * 6533312 * 2
def baseEnd_6533312 : Nat := 372747702420805291161539

theorem tailTrace_6533312 : CollatzResearch.WordTrace tailWord_6533312 prefixEnd_6533312 372747702420805291161539 := by
  unfold tailWord_6533312
  simp only [CollatzResearch.WordTrace]
  refine ⟨119144732453466949850633095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158859643271289266467510793 119144732453466949850633095)
  ·
    refine ⟨178717098680200424775949643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119144732453466949850633095 178717098680200424775949643)
    ·
      refine ⟨268075648020300637163924465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178717098680200424775949643 268075648020300637163924465)
      ·
        refine ⟨201056736015225477872943349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268075648020300637163924465 201056736015225477872943349)
        ·
          refine ⟨18849069001427388550588439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201056736015225477872943349 18849069001427388550588439)
          ·
            refine ⟨28273603502141082825882659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18849069001427388550588439 28273603502141082825882659)
            ·
              refine ⟨42410405253211624238823989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28273603502141082825882659 42410405253211624238823989)
              ·
                refine ⟨3975975492488589772389749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42410405253211624238823989 3975975492488589772389749)
                ·
                  refine ⟨372747702420805291161539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975975492488589772389749 372747702420805291161539)
                  ·
                    rfl

theorem cell23_6533312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 5].length) (baseStart_6533312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533312 prefixEnd_6533312 := by exact prefixLift 6533312
  have htrace : WordTrace (prefixWord ++ tailWord_6533312) baseStart_6533312 baseEnd_6533312 := by
    simpa [prefixWord, tailWord_6533312, baseEnd_6533312] using wordTrace_append hprefix tailTrace_6533312
  have hstable : (prefixWord ++ tailWord_6533312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533312).length < 2 ^ (prefixWord ++ tailWord_6533312).sum := by decide
  have hdescent : baseEnd_6533312 < baseStart_6533312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533340 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6533340 : Nat := 118140960795 + 6533340 * 2 ^ 59
def prefixEnd_6533340 : Nat := 4983230072969 + 3 ^ 40 * 6533340 * 2
def baseEnd_6533340 : Nat := 3354743699245573510903723

theorem tailTrace_6533340 : CollatzResearch.WordTrace tailWord_6533340 prefixEnd_6533340 3354743699245573510903723 := by
  unfold tailWord_6533340
  simp only [CollatzResearch.WordTrace]
  refine ⟨119145243075416230241642737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158860324100554973655523649 119145243075416230241642737)
  ·
    refine ⟨89358932306562172681232053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119145243075416230241642737 89358932306562172681232053)
    ·
      refine ⟨8377399903740203688865505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89358932306562172681232053 8377399903740203688865505)
      ·
        refine ⟨6283049927805152766649129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377399903740203688865505 6283049927805152766649129)
        ·
          refine ⟨4712287445853864574986847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6283049927805152766649129 4712287445853864574986847)
          ·
            refine ⟨7068431168780796862480271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712287445853864574986847 7068431168780796862480271)
            ·
              refine ⟨10602646753171195293720407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068431168780796862480271 10602646753171195293720407)
              ·
                refine ⟨15903970129756792940580611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10602646753171195293720407 15903970129756792940580611)
                ·
                  refine ⟨23855955194635189410870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15903970129756792940580611 23855955194635189410870917)
                  ·
                    refine ⟨4472991598994098014538297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23855955194635189410870917 4472991598994098014538297)
                    ·
                      refine ⟨3354743699245573510903723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4472991598994098014538297 3354743699245573510903723)
                      ·
                        rfl

theorem cell23_6533340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6533340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533340 prefixEnd_6533340 := by exact prefixLift 6533340
  have htrace : WordTrace (prefixWord ++ tailWord_6533340) baseStart_6533340 baseEnd_6533340 := by
    simpa [prefixWord, tailWord_6533340, baseEnd_6533340] using wordTrace_append hprefix tailTrace_6533340
  have hstable : (prefixWord ++ tailWord_6533340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533340).length < 2 ^ (prefixWord ++ tailWord_6533340).sum := by decide
  have hdescent : baseEnd_6533340 < baseStart_6533340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533345 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6533345 : Nat := 118140960795 + 6533345 * 2 ^ 59
def prefixEnd_6533345 : Nat := 4983230072969 + 3 ^ 40 * 6533345 * 2
def baseEnd_6533345 : Nat := 3354746266648845991341199

theorem tailTrace_6533345 : CollatzResearch.WordTrace tailWord_6533345 prefixEnd_6533345 3354746266648845991341199 := by
  unfold tailWord_6533345
  simp only [CollatzResearch.WordTrace]
  refine ⟨238290668515814346337217489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158860445677209564224811659 238290668515814346337217489)
  ·
    refine ⟨178718001386860759752913117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238290668515814346337217489 178718001386860759752913117)
    ·
      refine ⟨67019250520072784907342419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178718001386860759752913117 67019250520072784907342419)
      ·
        refine ⟨100528875780109177361013629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67019250520072784907342419 100528875780109177361013629)
        ·
          refine ⟨37698328417540941510380111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100528875780109177361013629 37698328417540941510380111)
          ·
            refine ⟨56547492626311412265570167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37698328417540941510380111 56547492626311412265570167)
            ·
              refine ⟨84821238939467118398355251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56547492626311412265570167 84821238939467118398355251)
              ·
                refine ⟨127231858409200677597532877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84821238939467118398355251 127231858409200677597532877)
                ·
                  refine ⟨47711946903450254099074829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127231858409200677597532877 47711946903450254099074829)
                  ·
                    refine ⟨17891980088793845287153061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47711946903450254099074829 17891980088793845287153061)
                    ·
                      refine ⟨3354746266648845991341199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17891980088793845287153061 3354746266648845991341199)
                      ·
                        rfl

theorem cell23_6533345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6533345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533345 prefixEnd_6533345 := by exact prefixLift 6533345
  have htrace : WordTrace (prefixWord ++ tailWord_6533345) baseStart_6533345 baseEnd_6533345 := by
    simpa [prefixWord, tailWord_6533345, baseEnd_6533345] using wordTrace_append hprefix tailTrace_6533345
  have hstable : (prefixWord ++ tailWord_6533345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533345).length < 2 ^ (prefixWord ++ tailWord_6533345).sum := by decide
  have hdescent : baseEnd_6533345 < baseStart_6533345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533362 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6533362 : Nat := 118140960795 + 6533362 * 2 ^ 59
def prefixEnd_6533362 : Nat := 4983230072969 + 3 ^ 40 * 6533362 * 2
def baseEnd_6533362 : Nat := 3354754995819972424828621

theorem tailTrace_6533362 : CollatzResearch.WordTrace tailWord_6533362 prefixEnd_6533362 3354754995819972424828621 := by
  unfold tailWord_6533362
  simp only [CollatzResearch.WordTrace]
  refine ⟨59572822139188189560146585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158860859037835172160390893 59572822139188189560146585)
  ·
    refine ⟨44679616604391142170109939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59572822139188189560146585 44679616604391142170109939)
    ·
      refine ⟨67019424906586713255164909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44679616604391142170109939 67019424906586713255164909)
      ·
        refine ⟨25132284339970017470686841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67019424906586713255164909 25132284339970017470686841)
        ·
          refine ⟨18849213254977513103015131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25132284339970017470686841 18849213254977513103015131)
          ·
            refine ⟨28273819882466269654522697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18849213254977513103015131 28273819882466269654522697)
            ·
              refine ⟨21205364911849702240892023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28273819882466269654522697 21205364911849702240892023)
              ·
                refine ⟨31808047367774553361338035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21205364911849702240892023 31808047367774553361338035)
                ·
                  refine ⟨47712071051661830042007053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31808047367774553361338035 47712071051661830042007053)
                  ·
                    refine ⟨17892026644373186265752645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47712071051661830042007053 17892026644373186265752645)
                    ·
                      refine ⟨3354754995819972424828621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17892026644373186265752645 3354754995819972424828621)
                      ·
                        rfl

theorem cell23_6533362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6533362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533362 prefixEnd_6533362 := by exact prefixLift 6533362
  have htrace : WordTrace (prefixWord ++ tailWord_6533362) baseStart_6533362 baseEnd_6533362 := by
    simpa [prefixWord, tailWord_6533362, baseEnd_6533362] using wordTrace_append hprefix tailTrace_6533362
  have hstable : (prefixWord ++ tailWord_6533362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533362).length < 2 ^ (prefixWord ++ tailWord_6533362).sum := by decide
  have hdescent : baseEnd_6533362 < baseStart_6533362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533385 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 8]
def baseStart_6533385 : Nat := 118140960795 + 6533385 * 2 ^ 59
def prefixEnd_6533385 : Nat := 4983230072969 + 3 ^ 40 * 6533385 * 2
def baseEnd_6533385 : Nat := 372751867319447314982335

theorem tailTrace_6533385 : CollatzResearch.WordTrace tailWord_6533385 prefixEnd_6533385 372751867319447314982335 := by
  unfold tailWord_6533385
  simp only [CollatzResearch.WordTrace]
  refine ⟨238292127435669433168673609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158861418290446288779115739 238292127435669433168673609)
  ·
    refine ⟨178719095576752074876505207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238292127435669433168673609 178719095576752074876505207)
    ·
      refine ⟨268078643365128112314757811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178719095576752074876505207 268078643365128112314757811)
      ·
        refine ⟨402117965047692168472136717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268078643365128112314757811 402117965047692168472136717)
        ·
          refine ⟨150794236892884563177051269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402117965047692168472136717 150794236892884563177051269)
          ·
            refine ⟨28273919417415855595697113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150794236892884563177051269 28273919417415855595697113)
            ·
              refine ⟨21205439563061891696772835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28273919417415855595697113 21205439563061891696772835)
              ·
                refine ⟨31808159344592837545159253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21205439563061891696772835 31808159344592837545159253)
                ·
                  refine ⟨372751867319447314982335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31808159344592837545159253 372751867319447314982335)
                  ·
                    rfl

theorem cell23_6533385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_6533385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533385 prefixEnd_6533385 := by exact prefixLift 6533385
  have htrace : WordTrace (prefixWord ++ tailWord_6533385) baseStart_6533385 baseEnd_6533385 := by
    simpa [prefixWord, tailWord_6533385, baseEnd_6533385] using wordTrace_append hprefix tailTrace_6533385
  have hstable : (prefixWord ++ tailWord_6533385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533385).length < 2 ^ (prefixWord ++ tailWord_6533385).sum := by decide
  have hdescent : baseEnd_6533385 < baseStart_6533385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533416 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6533416 : Nat := 118140960795 + 6533416 * 2 ^ 59
def prefixEnd_6533416 : Nat := 4983230072969 + 3 ^ 40 * 6533416 * 2
def baseEnd_6533416 : Nat := 3354782723775315213553373

theorem tailTrace_6533416 : CollatzResearch.WordTrace tailWord_6533416 prefixEnd_6533416 3354782723775315213553373 := by
  unfold tailWord_6533416
  simp only [CollatzResearch.WordTrace]
  refine ⟨119146629049278562731526051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158862172065704750308701401 119146629049278562731526051)
  ·
    refine ⟨178719943573917844097289077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119146629049278562731526051 178719943573917844097289077)
    ·
      refine ⟨16754994710054797884120851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178719943573917844097289077 16754994710054797884120851)
      ·
        refine ⟨25132492065082196826181277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16754994710054797884120851 25132492065082196826181277)
        ·
          refine ⟨9424684524405823809817979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25132492065082196826181277 9424684524405823809817979)
          ·
            refine ⟨14137026786608735714726969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424684524405823809817979 14137026786608735714726969)
            ·
              refine ⟨10602770089956551786045227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14137026786608735714726969 10602770089956551786045227)
              ·
                refine ⟨15904155134934827679067841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10602770089956551786045227 15904155134934827679067841)
                ·
                  refine ⟨11928116351201120759300881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904155134934827679067841 11928116351201120759300881)
                  ·
                    refine ⟨8946087263400840569475661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11928116351201120759300881 8946087263400840569475661)
                    ·
                      refine ⟨3354782723775315213553373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8946087263400840569475661 3354782723775315213553373)
                      ·
                        rfl

theorem cell23_6533416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6533416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533416 prefixEnd_6533416 := by exact prefixLift 6533416
  have htrace : WordTrace (prefixWord ++ tailWord_6533416) baseStart_6533416 baseEnd_6533416 := by
    simpa [prefixWord, tailWord_6533416, baseEnd_6533416] using wordTrace_append hprefix tailTrace_6533416
  have hstable : (prefixWord ++ tailWord_6533416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533416).length < 2 ^ (prefixWord ++ tailWord_6533416).sum := by decide
  have hdescent : baseEnd_6533416 < baseStart_6533416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533432 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_6533432 : Nat := 118140960795 + 6533432 * 2 ^ 59
def prefixEnd_6533432 : Nat := 4983230072969 + 3 ^ 40 * 6533432 * 2
def baseEnd_6533432 : Nat := 1118263646488595716984433

theorem tailTrace_6533432 : CollatzResearch.WordTrace tailWord_6533432 prefixEnd_6533432 1118263646488595716984433 := by
  unfold tailWord_6533432
  simp only [CollatzResearch.WordTrace]
  refine ⟨119146920833249580097817275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158862561110999440130423033 119146920833249580097817275)
  ·
    refine ⟨178720381249874370146725913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119146920833249580097817275 178720381249874370146725913)
    ·
      refine ⟨134040285937405777610044435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178720381249874370146725913 134040285937405777610044435)
      ·
        refine ⟨201060428906108666415066653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134040285937405777610044435 201060428906108666415066653)
        ·
          refine ⟨75397660839790749905649995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201060428906108666415066653 75397660839790749905649995)
          ·
            refine ⟨113096491259686124858474993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75397660839790749905649995 113096491259686124858474993)
            ·
              refine ⟨84822368444764593643856245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113096491259686124858474993 84822368444764593643856245)
              ·
                refine ⟨7952097041696680654111523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84822368444764593643856245 7952097041696680654111523)
                ·
                  refine ⟨11928145562545020981167285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952097041696680654111523 11928145562545020981167285)
                  ·
                    refine ⟨1118263646488595716984433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928145562545020981167285 1118263646488595716984433)
                    ·
                      rfl

theorem cell23_6533432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_6533432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533432 prefixEnd_6533432 := by exact prefixLift 6533432
  have htrace : WordTrace (prefixWord ++ tailWord_6533432) baseStart_6533432 baseEnd_6533432 := by
    simpa [prefixWord, tailWord_6533432, baseEnd_6533432] using wordTrace_append hprefix tailTrace_6533432
  have hstable : (prefixWord ++ tailWord_6533432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533432).length < 2 ^ (prefixWord ++ tailWord_6533432).sum := by decide
  have hdescent : baseEnd_6533432 < baseStart_6533432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533439 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 2, 3, 2]
def baseStart_6533439 : Nat := 118140960795 + 6533439 * 2 ^ 59
def prefixEnd_6533439 : Nat := 4983230072969 + 3 ^ 40 * 6533439 * 2
def baseEnd_6533439 : Nat := 3354794533830368623565767

theorem tailTrace_6533439 : CollatzResearch.WordTrace tailWord_6533439 prefixEnd_6533439 3354794533830368623565767 := by
  unfold tailWord_6533439
  simp only [CollatzResearch.WordTrace]
  refine ⟨238294096977473800391139371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158862731318315866927426247 238294096977473800391139371)
  ·
    refine ⟨357441145466210700586709057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238294096977473800391139371 357441145466210700586709057)
    ·
      refine ⟨268080859099658025440031793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357441145466210700586709057 268080859099658025440031793)
      ·
        refine ⟨201060644324743519080023845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268080859099658025440031793 201060644324743519080023845)
        ·
          refine ⟨37698870810889409827504471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201060644324743519080023845 37698870810889409827504471)
          ·
            refine ⟨56548306216334114741256707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37698870810889409827504471 56548306216334114741256707)
            ·
              refine ⟨84822459324501172111885061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56548306216334114741256707 84822459324501172111885061)
              ·
                refine ⟨15904211123343969770978449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84822459324501172111885061 15904211123343969770978449)
                ·
                  refine ⟨11928158342507977328233837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904211123343969770978449 11928158342507977328233837)
                  ·
                    refine ⟨4473059378440491498087689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11928158342507977328233837 4473059378440491498087689)
                    ·
                      refine ⟨3354794533830368623565767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473059378440491498087689 3354794533830368623565767)
                      ·
                        rfl

theorem cell23_6533439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_6533439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533439 prefixEnd_6533439 := by exact prefixLift 6533439
  have htrace : WordTrace (prefixWord ++ tailWord_6533439) baseStart_6533439 baseEnd_6533439 := by
    simpa [prefixWord, tailWord_6533439, baseEnd_6533439] using wordTrace_append hprefix tailTrace_6533439
  have hstable : (prefixWord ++ tailWord_6533439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533439).length < 2 ^ (prefixWord ++ tailWord_6533439).sum := by decide
  have hdescent : baseEnd_6533439 < baseStart_6533439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533452 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6533452 : Nat := 118140960795 + 6533452 * 2 ^ 59
def prefixEnd_6533452 : Nat := 4983230072969 + 3 ^ 40 * 6533452 * 2
def baseEnd_6533452 : Nat := 3354801209078877072703207

theorem tailTrace_6533452 : CollatzResearch.WordTrace tailWord_6533452 prefixEnd_6533452 3354801209078877072703207 := by
  unfold tailWord_6533452
  simp only [CollatzResearch.WordTrace]
  refine ⟨119147285563213351805681305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158863047417617802407575073 119147285563213351805681305)
  ·
    refine ⟨89360464172410013854260979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119147285563213351805681305 89360464172410013854260979)
    ·
      refine ⟨134040696258615020781391469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89360464172410013854260979 134040696258615020781391469)
      ·
        refine ⟨50265261096980632793021801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134040696258615020781391469 50265261096980632793021801)
        ·
          refine ⟨37698945822735474594766351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50265261096980632793021801 37698945822735474594766351)
          ·
            refine ⟨56548418734103211892149527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37698945822735474594766351 56548418734103211892149527)
            ·
              refine ⟨84822628101154817838224291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56548418734103211892149527 84822628101154817838224291)
              ·
                refine ⟨127233942151732226757336437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84822628101154817838224291 127233942151732226757336437)
                ·
                  refine ⟨11928182076724896258500291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127233942151732226757336437 11928182076724896258500291)
                  ·
                    refine ⟨17892273115087344387750437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11928182076724896258500291 17892273115087344387750437)
                    ·
                      refine ⟨3354801209078877072703207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17892273115087344387750437 3354801209078877072703207)
                      ·
                        rfl

theorem cell23_6533452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6533452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533452 prefixEnd_6533452 := by exact prefixLift 6533452
  have htrace : WordTrace (prefixWord ++ tailWord_6533452) baseStart_6533452 baseEnd_6533452 := by
    simpa [prefixWord, tailWord_6533452, baseEnd_6533452] using wordTrace_append hprefix tailTrace_6533452
  have hstable : (prefixWord ++ tailWord_6533452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533452).length < 2 ^ (prefixWord ++ tailWord_6533452).sum := by decide
  have hdescent : baseEnd_6533452 < baseStart_6533452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533580 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6533580 : Nat := 118140960795 + 6533580 * 2 ^ 59
def prefixEnd_6533580 : Nat := 4983230072969 + 3 ^ 40 * 6533580 * 2
def baseEnd_6533580 : Nat := 3354866934602652571902619

theorem tailTrace_6533580 : CollatzResearch.WordTrace tailWord_6533580 prefixEnd_6533580 3354866934602652571902619 := by
  unfold tailWord_6533580
  simp only [CollatzResearch.WordTrace]
  refine ⟨119149619834981490736011097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158866159779975320981348129 119149619834981490736011097)
  ·
    refine ⟨89362214876236118052008323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119149619834981490736011097 89362214876236118052008323)
    ·
      refine ⟨134043322314354177078012485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89362214876236118052008323 134043322314354177078012485)
      ·
        refine ⟨25133122933941408202127341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134043322314354177078012485 25133122933941408202127341)
        ·
          refine ⟨9424921100228028075797753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25133122933941408202127341 9424921100228028075797753)
          ·
            refine ⟨7068690825171021056848315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9424921100228028075797753 7068690825171021056848315)
            ·
              refine ⟨10603036237756531585272473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068690825171021056848315 10603036237756531585272473)
              ·
                refine ⟨7952277178317398688954355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10603036237756531585272473 7952277178317398688954355)
                ·
                  refine ⟨11928415767476098033431533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952277178317398688954355 11928415767476098033431533)
                  ·
                    refine ⟨4473155912803536762536825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11928415767476098033431533 4473155912803536762536825)
                    ·
                      refine ⟨3354866934602652571902619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473155912803536762536825 3354866934602652571902619)
                      ·
                        rfl

theorem cell23_6533580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6533580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533580 prefixEnd_6533580 := by exact prefixLift 6533580
  have htrace : WordTrace (prefixWord ++ tailWord_6533580) baseStart_6533580 baseEnd_6533580 := by
    simpa [prefixWord, tailWord_6533580, baseEnd_6533580] using wordTrace_append hprefix tailTrace_6533580
  have hstable : (prefixWord ++ tailWord_6533580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533580).length < 2 ^ (prefixWord ++ tailWord_6533580).sum := by decide
  have hdescent : baseEnd_6533580 < baseStart_6533580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533582 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_6533582 : Nat := 118140960795 + 6533582 * 2 ^ 59
def prefixEnd_6533582 : Nat := 4983230072969 + 3 ^ 40 * 6533582 * 2
def baseEnd_6533582 : Nat := 372763106840440173786401

theorem tailTrace_6533582 : CollatzResearch.WordTrace tailWord_6533582 prefixEnd_6533582 372763106840440173786401 := by
  unfold tailWord_6533582
  simp only [CollatzResearch.WordTrace]
  refine ⟨29787414076994466976699375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158866208410637157209063333 29787414076994466976699375)
  ·
    refine ⟨44681121115491700465049063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29787414076994466976699375 44681121115491700465049063)
    ·
      refine ⟨67021681673237550697573595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44681121115491700465049063 67021681673237550697573595)
      ·
        refine ⟨100532522509856326046360393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67021681673237550697573595 100532522509856326046360393)
        ·
          refine ⟨75399391882392244534770295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100532522509856326046360393 75399391882392244534770295)
          ·
            refine ⟨113099087823588366802155443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75399391882392244534770295 113099087823588366802155443)
            ·
              refine ⟨169648631735382550203233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113099087823588366802155443 169648631735382550203233165)
              ·
                refine ⟨63618236900768456326212437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169648631735382550203233165 63618236900768456326212437)
                ·
                  refine ⟨372763106840440173786401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63618236900768456326212437 372763106840440173786401)
                  ·
                    rfl

theorem cell23_6533582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_6533582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533582 prefixEnd_6533582 := by exact prefixLift 6533582
  have htrace : WordTrace (prefixWord ++ tailWord_6533582) baseStart_6533582 baseEnd_6533582 := by
    simpa [prefixWord, tailWord_6533582, baseEnd_6533582] using wordTrace_append hprefix tailTrace_6533582
  have hstable : (prefixWord ++ tailWord_6533582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533582).length < 2 ^ (prefixWord ++ tailWord_6533582).sum := by decide
  have hdescent : baseEnd_6533582 < baseStart_6533582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533610 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_6533610 : Nat := 118140960795 + 6533610 * 2 ^ 59
def prefixEnd_6533610 : Nat := 4983230072969 + 3 ^ 40 * 6533610 * 2
def baseEnd_6533610 : Nat := 3354882339022287454527481

theorem tailTrace_6533610 : CollatzResearch.WordTrace tailWord_6533610 prefixEnd_6533610 3354882339022287454527481 := by
  unfold tailWord_6533610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59575083464963574148903571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158866889239902864397076189 59575083464963574148903571)
  ·
    refine ⟨89362625197445361223355357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59575083464963574148903571 89362625197445361223355357)
    ·
      refine ⟨33510984449042010458758259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89362625197445361223355357 33510984449042010458758259)
      ·
        refine ⟨50266476673563015688137389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33510984449042010458758259 50266476673563015688137389)
        ·
          refine ⟨18849928752586130883051521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50266476673563015688137389 18849928752586130883051521)
          ·
            refine ⟨14137446564439598162288641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18849928752586130883051521 14137446564439598162288641)
            ·
              refine ⟨10603084923329698621716481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14137446564439598162288641 10603084923329698621716481)
              ·
                refine ⟨7952313692497273966287361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10603084923329698621716481 7952313692497273966287361)
                ·
                  refine ⟨5964235269372955474715521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7952313692497273966287361 5964235269372955474715521)
                  ·
                    refine ⟨4473176452029716606036641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5964235269372955474715521 4473176452029716606036641)
                    ·
                      refine ⟨3354882339022287454527481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473176452029716606036641 3354882339022287454527481)
                      ·
                        rfl

theorem cell23_6533610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_6533610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533610 prefixEnd_6533610 := by exact prefixLift 6533610
  have htrace : WordTrace (prefixWord ++ tailWord_6533610) baseStart_6533610 baseEnd_6533610 := by
    simpa [prefixWord, tailWord_6533610, baseEnd_6533610] using wordTrace_append hprefix tailTrace_6533610
  have hstable : (prefixWord ++ tailWord_6533610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533610).length < 2 ^ (prefixWord ++ tailWord_6533610).sum := by decide
  have hdescent : baseEnd_6533610 < baseStart_6533610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533619 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 7, 2]
def baseStart_6533619 : Nat := 118140960795 + 6533619 * 2 ^ 59
def prefixEnd_6533619 : Nat := 4983230072969 + 3 ^ 40 * 6533619 * 2
def baseEnd_6533619 : Nat := 3354886960348177919314939

theorem tailTrace_6533619 : CollatzResearch.WordTrace tailWord_6533619 prefixEnd_6533619 3354886960348177919314939 := by
  unfold tailWord_6533619
  simp only [CollatzResearch.WordTrace]
  refine ⟨238300662116821691132691911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158867108077881127421794607 238300662116821691132691911)
  ·
    refine ⟨357450993175232536699037867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238300662116821691132691911 357450993175232536699037867)
    ·
      refine ⟨536176489762848805048556801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357450993175232536699037867 536176489762848805048556801)
      ·
        refine ⟨402132367322136603786417601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536176489762848805048556801 402132367322136603786417601)
        ·
          refine ⟨301599275491602452839813201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402132367322136603786417601 301599275491602452839813201)
          ·
            refine ⟨226199456618701839629859901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301599275491602452839813201 226199456618701839629859901)
            ·
              refine ⟨84824796232013189861197463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226199456618701839629859901 84824796232013189861197463)
              ·
                refine ⟨127237194348019784791796195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84824796232013189861197463 127237194348019784791796195)
                ·
                  refine ⟨190855791522029677187694293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127237194348019784791796195 190855791522029677187694293)
                  ·
                    refine ⟨4473182613797570559086585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190855791522029677187694293 4473182613797570559086585)
                    ·
                      refine ⟨3354886960348177919314939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473182613797570559086585 3354886960348177919314939)
                      ·
                        rfl

theorem cell23_6533619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7, 2].length) (baseStart_6533619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533619 prefixEnd_6533619 := by exact prefixLift 6533619
  have htrace : WordTrace (prefixWord ++ tailWord_6533619) baseStart_6533619 baseEnd_6533619 := by
    simpa [prefixWord, tailWord_6533619, baseEnd_6533619] using wordTrace_append hprefix tailTrace_6533619
  have hstable : (prefixWord ++ tailWord_6533619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533619).length < 2 ^ (prefixWord ++ tailWord_6533619).sum := by decide
  have hdescent : baseEnd_6533619 < baseStart_6533619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533646 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_6533646 : Nat := 118140960795 + 6533646 * 2 ^ 59
def prefixEnd_6533646 : Nat := 4983230072969 + 3 ^ 40 * 6533646 * 2
def baseEnd_6533646 : Nat := 1118300274775283104559105

theorem tailTrace_6533646 : CollatzResearch.WordTrace tailWord_6533646 prefixEnd_6533646 1118300274775283104559105 := by
  unfold tailWord_6533646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29787705860965484342990599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158867764591815916495949861 29787705860965484342990599)
  ·
    refine ⟨44681558791448226514485899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29787705860965484342990599 44681558791448226514485899)
    ·
      refine ⟨67022338187172339771728849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44681558791448226514485899 67022338187172339771728849)
      ·
        refine ⟨50266753640379254828796637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67022338187172339771728849 50266753640379254828796637)
        ·
          refine ⟨18850032615142220560798739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50266753640379254828796637 18850032615142220560798739)
          ·
            refine ⟨28275048922713330841198109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850032615142220560798739 28275048922713330841198109)
            ·
              refine ⟨10603143346017499065449291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28275048922713330841198109 10603143346017499065449291)
              ·
                refine ⟨15904715019026248598173937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603143346017499065449291 15904715019026248598173937)
                ·
                  refine ⟨11928536264269686448630453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904715019026248598173937 11928536264269686448630453)
                  ·
                    refine ⟨1118300274775283104559105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928536264269686448630453 1118300274775283104559105)
                    ·
                      rfl

theorem cell23_6533646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_6533646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533646 prefixEnd_6533646 := by exact prefixLift 6533646
  have htrace : WordTrace (prefixWord ++ tailWord_6533646) baseStart_6533646 baseEnd_6533646 := by
    simpa [prefixWord, tailWord_6533646, baseEnd_6533646] using wordTrace_append hprefix tailTrace_6533646
  have hstable : (prefixWord ++ tailWord_6533646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533646).length < 2 ^ (prefixWord ++ tailWord_6533646).sum := by decide
  have hdescent : baseEnd_6533646 < baseStart_6533646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533649 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_6533649 : Nat := 118140960795 + 6533649 * 2 ^ 59
def prefixEnd_6533649 : Nat := 4983230072969 + 3 ^ 40 * 6533649 * 2
def baseEnd_6533649 : Nat := 3354902364767812801939801

theorem tailTrace_6533649 : CollatzResearch.WordTrace tailWord_6533649 prefixEnd_6533649 3354902364767812801939801 := by
  unfold tailWord_6533649
  simp only [CollatzResearch.WordTrace]
  refine ⟨238301756306713006256284001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158867837537808670837522667 238301756306713006256284001)
  ·
    refine ⟨178726317230034754692213001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238301756306713006256284001 178726317230034754692213001)
    ·
      refine ⟨134044737922526066019159751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178726317230034754692213001 134044737922526066019159751)
      ·
        refine ⟨201067106883789099028739627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134044737922526066019159751 201067106883789099028739627)
        ·
          refine ⟨301600660325683648543109441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201067106883789099028739627 301600660325683648543109441)
          ·
            refine ⟨226200495244262736407332081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301600660325683648543109441 226200495244262736407332081)
            ·
              refine ⟨169650371433197052305499061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226200495244262736407332081 169650371433197052305499061)
              ·
                refine ⟨15904722321862223653640537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169650371433197052305499061 15904722321862223653640537)
                ·
                  refine ⟨11928541741396667740230403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904722321862223653640537 11928541741396667740230403)
                  ·
                    refine ⟨17892812612095001610345605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11928541741396667740230403 17892812612095001610345605)
                    ·
                      refine ⟨3354902364767812801939801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17892812612095001610345605 3354902364767812801939801)
                      ·
                        rfl

theorem cell23_6533649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_6533649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533649 prefixEnd_6533649 := by exact prefixLift 6533649
  have htrace : WordTrace (prefixWord ++ tailWord_6533649) baseStart_6533649 baseEnd_6533649 := by
    simpa [prefixWord, tailWord_6533649, baseEnd_6533649] using wordTrace_append hprefix tailTrace_6533649
  have hstable : (prefixWord ++ tailWord_6533649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533649).length < 2 ^ (prefixWord ++ tailWord_6533649).sum := by decide
  have hdescent : baseEnd_6533649 < baseStart_6533649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533753 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_6533753 : Nat := 118140960795 + 6533753 * 2 ^ 59
def prefixEnd_6533753 : Nat := 4983230072969 + 3 ^ 40 * 6533753 * 2
def baseEnd_6533753 : Nat := 1118318588918626798346441

theorem tailTrace_6533753 : CollatzResearch.WordTrace tailWord_6533753 prefixEnd_6533753 1118318588918626798346441 := by
  unfold tailWord_6533753
  simp only [CollatzResearch.WordTrace]
  refine ⟨238305549498336232018069913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158870366332224154678713275 238305549498336232018069913)
  ·
    refine ⟨178729162123752174013552435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238305549498336232018069913 178729162123752174013552435)
    ·
      refine ⟨268093743185628261020328653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178729162123752174013552435 268093743185628261020328653)
      ·
        refine ⟨100535153694610597882623245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268093743185628261020328653 100535153694610597882623245)
        ·
          refine ⟨37700682635478974205983717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100535153694610597882623245 37700682635478974205983717)
          ·
            refine ⟨7068877994152307663621947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37700682635478974205983717 7068877994152307663621947)
            ·
              refine ⟨10603316991228461495432921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068877994152307663621947 10603316991228461495432921)
              ·
                refine ⟨7952487743421346121574691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10603316991228461495432921 7952487743421346121574691)
                ·
                  refine ⟨11928731615132019182362037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952487743421346121574691 11928731615132019182362037)
                  ·
                    refine ⟨1118318588918626798346441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928731615132019182362037 1118318588918626798346441)
                    ·
                      rfl

theorem cell23_6533753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_6533753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533753 prefixEnd_6533753 := by exact prefixLift 6533753
  have htrace : WordTrace (prefixWord ++ tailWord_6533753) baseStart_6533753 baseEnd_6533753 := by
    simpa [prefixWord, tailWord_6533753, baseEnd_6533753] using wordTrace_append hprefix tailTrace_6533753
  have hstable : (prefixWord ++ tailWord_6533753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533753).length < 2 ^ (prefixWord ++ tailWord_6533753).sum := by decide
  have hdescent : baseEnd_6533753 < baseStart_6533753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533756 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_6533756 : Nat := 118140960795 + 6533756 * 2 ^ 59
def prefixEnd_6533756 : Nat := 4983230072969 + 3 ^ 40 * 6533756 * 2
def baseEnd_6533756 : Nat := 3354957307197843883301809

theorem tailTrace_6533756 : CollatzResearch.WordTrace tailWord_6533756 prefixEnd_6533756 3354957307197843883301809 := by
  unfold tailWord_6533756
  simp only [CollatzResearch.WordTrace]
  refine ⟨119152829458662681765214561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158870439278216909020286081 119152829458662681765214561)
  ·
    refine ⟨89364622093997011323910921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119152829458662681765214561 89364622093997011323910921)
    ·
      refine ⟨67023466570497758492933191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89364622093997011323910921 67023466570497758492933191)
      ·
        refine ⟨100535199855746637739399787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67023466570497758492933191 100535199855746637739399787)
        ·
          refine ⟨150802799783619956609099681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100535199855746637739399787 150802799783619956609099681)
          ·
            refine ⟨113102099837714967456824761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150802799783619956609099681 113102099837714967456824761)
            ·
              refine ⟨84826574878286225592618571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113102099837714967456824761 84826574878286225592618571)
              ·
                refine ⟨127239862317429338388927857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84826574878286225592618571 127239862317429338388927857)
                ·
                  refine ⟨95429896738072003791695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127239862317429338388927857 95429896738072003791695893)
                  ·
                    refine ⟨4473276409597125177735745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95429896738072003791695893 4473276409597125177735745)
                    ·
                      refine ⟨3354957307197843883301809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473276409597125177735745 3354957307197843883301809)
                      ·
                        rfl

theorem cell23_6533756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_6533756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533756 prefixEnd_6533756 := by exact prefixLift 6533756
  have htrace : WordTrace (prefixWord ++ tailWord_6533756) baseStart_6533756 baseEnd_6533756 := by
    simpa [prefixWord, tailWord_6533756, baseEnd_6533756] using wordTrace_append hprefix tailTrace_6533756
  have hstable : (prefixWord ++ tailWord_6533756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533756).length < 2 ^ (prefixWord ++ tailWord_6533756).sum := by decide
  have hdescent : baseEnd_6533756 < baseStart_6533756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533770 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_6533770 : Nat := 118140960795 + 6533770 * 2 ^ 59
def prefixEnd_6533770 : Nat := 4983230072969 + 3 ^ 40 * 6533770 * 2
def baseEnd_6533770 : Nat := 1118321498642335609508915

theorem tailTrace_6533770 : CollatzResearch.WordTrace tailWord_6533770 prefixEnd_6533770 1118321498642335609508915 := by
  unfold tailWord_6533770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576542384818660980359691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158870779692849762614292509 59576542384818660980359691)
  ·
    refine ⟨89364813577227991470539537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59576542384818660980359691 89364813577227991470539537)
    ·
      refine ⟨67023610182920993602904653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89364813577227991470539537 67023610182920993602904653)
      ·
        refine ⟨25133853818595372601089245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67023610182920993602904653 25133853818595372601089245)
        ·
          refine ⟨9425195181973264725408467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25133853818595372601089245 9425195181973264725408467)
          ·
            refine ⟨14137792772959897088112701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425195181973264725408467 14137792772959897088112701)
            ·
              refine ⟨5301672289859961408042263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14137792772959897088112701 5301672289859961408042263)
              ·
                refine ⟨7952508434789942112063395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301672289859961408042263 7952508434789942112063395)
                ·
                  refine ⟨11928762652184913168095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7952508434789942112063395 11928762652184913168095093)
                  ·
                    refine ⟨1118321498642335609508915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928762652184913168095093 1118321498642335609508915)
                    ·
                      rfl

theorem cell23_6533770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_6533770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533770 prefixEnd_6533770 := by exact prefixLift 6533770
  have htrace : WordTrace (prefixWord ++ tailWord_6533770) baseStart_6533770 baseEnd_6533770 := by
    simpa [prefixWord, tailWord_6533770, baseEnd_6533770] using wordTrace_append hprefix tailTrace_6533770
  have hstable : (prefixWord ++ tailWord_6533770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533770).length < 2 ^ (prefixWord ++ tailWord_6533770).sum := by decide
  have hdescent : baseEnd_6533770 < baseStart_6533770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533783 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 2, 4]
def baseStart_6533783 : Nat := 118140960795 + 6533783 * 2 ^ 59
def prefixEnd_6533783 : Nat := 4983230072969 + 3 ^ 40 * 6533783 * 2
def baseEnd_6533783 : Nat := 1118323723725171759221395

theorem tailTrace_6533783 : CollatzResearch.WordTrace tailWord_6533783 prefixEnd_6533783 1118323723725171759221395 := by
  unfold tailWord_6533783
  simp only [CollatzResearch.WordTrace]
  refine ⟨238306643688227547141662003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158871095792151698094441335 238306643688227547141662003)
  ·
    refine ⟨357459965532341320712493005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238306643688227547141662003 357459965532341320712493005)
    ·
      refine ⟨134047487074627995267184877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357459965532341320712493005 134047487074627995267184877)
      ·
        refine ⟨50267807652985498225194329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134047487074627995267184877 50267807652985498225194329)
        ·
          refine ⟨37700855739739123668895747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50267807652985498225194329 37700855739739123668895747)
          ·
            refine ⟨56551283609608685503343621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37700855739739123668895747 56551283609608685503343621)
            ·
              refine ⟨10603365676801628531876929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56551283609608685503343621 10603365676801628531876929)
              ·
                refine ⟨7952524257601221398907697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10603365676801628531876929 7952524257601221398907697)
                ·
                  refine ⟨5964393193200916049180773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7952524257601221398907697 5964393193200916049180773)
                  ·
                    refine ⟨1118323723725171759221395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964393193200916049180773 1118323723725171759221395)
                    ·
                      rfl

theorem cell23_6533783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_6533783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533783 prefixEnd_6533783 := by exact prefixLift 6533783
  have htrace : WordTrace (prefixWord ++ tailWord_6533783) baseStart_6533783 baseEnd_6533783 := by
    simpa [prefixWord, tailWord_6533783, baseEnd_6533783] using wordTrace_append hprefix tailTrace_6533783
  have hstable : (prefixWord ++ tailWord_6533783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533783).length < 2 ^ (prefixWord ++ tailWord_6533783).sum := by decide
  have hdescent : baseEnd_6533783 < baseStart_6533783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533813 : List Nat := [1, 3, 3, 3, 1, 2, 3, 7]
def baseStart_6533813 : Nat := 118140960795 + 6533813 * 2 ^ 59
def prefixEnd_6533813 : Nat := 4983230072969 + 3 ^ 40 * 6533813 * 2
def baseEnd_6533813 : Nat := 124258762059079635566261

theorem tailTrace_6533813 : CollatzResearch.WordTrace tailWord_6533813 prefixEnd_6533813 124258762059079635566261 := by
  unfold tailWord_6533813
  simp only [CollatzResearch.WordTrace]
  refine ⟨238307737878118862265254093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158871825252079241510169395 238307737878118862265254093)
  ·
    refine ⟨89365401704294573349470285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238307737878118862265254093 89365401704294573349470285)
    ·
      refine ⟨33512025639110465006051357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89365401704294573349470285 33512025639110465006051357)
      ·
        refine ⟨12567009614666424377269259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33512025639110465006051357 12567009614666424377269259)
        ·
          refine ⟨18850514421999636565903889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567009614666424377269259 18850514421999636565903889)
          ·
            refine ⟨14137885816499727424427917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18850514421999636565903889 14137885816499727424427917)
            ·
              refine ⟨5301707181187397784160469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14137885816499727424427917 5301707181187397784160469)
              ·
                refine ⟨124258762059079635566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5301707181187397784160469 124258762059079635566261)
                ·
                  rfl

theorem cell23_6533813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 7].length) (baseStart_6533813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533813 prefixEnd_6533813 := by exact prefixLift 6533813
  have htrace : WordTrace (prefixWord ++ tailWord_6533813) baseStart_6533813 baseEnd_6533813 := by
    simpa [prefixWord, tailWord_6533813, baseEnd_6533813] using wordTrace_append hprefix tailTrace_6533813
  have hstable : (prefixWord ++ tailWord_6533813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533813).length < 2 ^ (prefixWord ++ tailWord_6533813).sum := by decide
  have hdescent : baseEnd_6533813 < baseStart_6533813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533830 : List Nat := [6, 1, 2, 1, 2, 1, 10]
def baseStart_6533830 : Nat := 118140960795 + 6533830 * 2 ^ 59
def prefixEnd_6533830 : Nat := 4983230072969 + 3 ^ 40 * 6533830 * 2
def baseEnd_6533830 : Nat := 41419695120571315972549

theorem tailTrace_6533830 : CollatzResearch.WordTrace tailWord_6533830 prefixEnd_6533830 41419695120571315972549 := by
  unfold tailWord_6533830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447136184970539817769467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158872238612704849445748629 7447136184970539817769467)
  ·
    refine ⟨11170704277455809726654201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447136184970539817769467 11170704277455809726654201)
    ·
      refine ⟨8378028208091857294990651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11170704277455809726654201 8378028208091857294990651)
      ·
        refine ⟨12567042312137785942485977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378028208091857294990651 12567042312137785942485977)
        ·
          refine ⟨9425281734103339456864483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567042312137785942485977 9425281734103339456864483)
          ·
            refine ⟨14137922601155009185296725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425281734103339456864483 14137922601155009185296725)
            ·
              refine ⟨41419695120571315972549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14137922601155009185296725 41419695120571315972549)
              ·
                rfl

theorem cell23_6533830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 10].length) (baseStart_6533830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533830 prefixEnd_6533830 := by exact prefixLift 6533830
  have htrace : WordTrace (prefixWord ++ tailWord_6533830) baseStart_6533830 baseEnd_6533830 := by
    simpa [prefixWord, tailWord_6533830, baseEnd_6533830] using wordTrace_append hprefix tailTrace_6533830
  have hstable : (prefixWord ++ tailWord_6533830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533830).length < 2 ^ (prefixWord ++ tailWord_6533830).sum := by decide
  have hdescent : baseEnd_6533830 < baseStart_6533830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533857 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_6533857 : Nat := 118140960795 + 6533857 * 2 ^ 59
def prefixEnd_6533857 : Nat := 4983230072969 + 3 ^ 40 * 6533857 * 2
def baseEnd_6533857 : Nat := 3355009168743947988138845

theorem tailTrace_6533857 : CollatzResearch.WordTrace tailWord_6533857 prefixEnd_6533857 3355009168743947988138845 := by
  unfold tailWord_6533857
  simp only [CollatzResearch.WordTrace]
  refine ⟨238309342689959457779855825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158872895126639638519903883 238309342689959457779855825)
  ·
    refine ⟨178732007017469593334891869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238309342689959457779855825 178732007017469593334891869)
    ·
      refine ⟨67024502631551097500584451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178732007017469593334891869 67024502631551097500584451)
      ·
        refine ⟨100536753947326646250876677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67024502631551097500584451 100536753947326646250876677)
        ·
          refine ⟨18850641365123746172039377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100536753947326646250876677 18850641365123746172039377)
          ·
            refine ⟨14137981023842809629029533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18850641365123746172039377 14137981023842809629029533)
            ·
              refine ⟨5301742883941053610886075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14137981023842809629029533 5301742883941053610886075)
              ·
                refine ⟨7952614325911580416329113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301742883941053610886075 7952614325911580416329113)
                ·
                  refine ⟨5964460744433685312246835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7952614325911580416329113 5964460744433685312246835)
                  ·
                    refine ⟨8946691116650527968370253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5964460744433685312246835 8946691116650527968370253)
                    ·
                      refine ⟨3355009168743947988138845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8946691116650527968370253 3355009168743947988138845)
                      ·
                        rfl

theorem cell23_6533857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_6533857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533857 prefixEnd_6533857 := by exact prefixLift 6533857
  have htrace : WordTrace (prefixWord ++ tailWord_6533857) baseStart_6533857 baseEnd_6533857 := by
    simpa [prefixWord, tailWord_6533857, baseEnd_6533857] using wordTrace_append hprefix tailTrace_6533857
  have hstable : (prefixWord ++ tailWord_6533857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533857).length < 2 ^ (prefixWord ++ tailWord_6533857).sum := by decide
  have hdescent : baseEnd_6533857 < baseStart_6533857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533866 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6533866 : Nat := 118140960795 + 6533866 * 2 ^ 59
def prefixEnd_6533866 : Nat := 4983230072969 + 3 ^ 40 * 6533866 * 2
def baseEnd_6533866 : Nat := 3355013790069838452926303

theorem tailTrace_6533866 : CollatzResearch.WordTrace tailWord_6533866 prefixEnd_6533866 3355013790069838452926303 := by
  unfold tailWord_6533866
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577417736731713079233363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158873113964617901544622301 59577417736731713079233363)
  ·
    refine ⟨89366126605097569618850045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59577417736731713079233363 89366126605097569618850045)
    ·
      refine ⟨33512297476911588607068767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89366126605097569618850045 33512297476911588607068767)
      ·
        refine ⟨50268446215367382910603151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33512297476911588607068767 50268446215367382910603151)
        ·
          refine ⟨75402669323051074365904727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50268446215367382910603151 75402669323051074365904727)
          ·
            refine ⟨113104003984576611548857091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75402669323051074365904727 113104003984576611548857091)
            ·
              refine ⟨169656005976864917323285637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113104003984576611548857091 169656005976864917323285637)
              ·
                refine ⟨31810501120662171998116057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169656005976864917323285637 31810501120662171998116057)
                ·
                  refine ⟨23857875840496628998587043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31810501120662171998116057 23857875840496628998587043)
                  ·
                    refine ⟨35786813760744943497880565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23857875840496628998587043 35786813760744943497880565)
                    ·
                      refine ⟨3355013790069838452926303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35786813760744943497880565 3355013790069838452926303)
                      ·
                        rfl

theorem cell23_6533866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6533866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533866 prefixEnd_6533866 := by exact prefixLift 6533866
  have htrace : WordTrace (prefixWord ++ tailWord_6533866) baseStart_6533866 baseEnd_6533866 := by
    simpa [prefixWord, tailWord_6533866, baseEnd_6533866] using wordTrace_append hprefix tailTrace_6533866
  have hstable : (prefixWord ++ tailWord_6533866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533866).length < 2 ^ (prefixWord ++ tailWord_6533866).sum := by decide
  have hdescent : baseEnd_6533866 < baseStart_6533866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533936 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_6533936 : Nat := 118140960795 + 6533936 * 2 ^ 59
def prefixEnd_6533936 : Nat := 4983230072969 + 3 ^ 40 * 6533936 * 2
def baseEnd_6533936 : Nat := 3355049733715653179050981

theorem tailTrace_6533936 : CollatzResearch.WordTrace tailWord_6533936 prefixEnd_6533936 3355049733715653179050981 := by
  unfold tailWord_6533936
  simp only [CollatzResearch.WordTrace]
  refine ⟨119156112028336627135990831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158874816037782169514654441 119156112028336627135990831)
  ·
    refine ⟨178734168042504940703986247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119156112028336627135990831 178734168042504940703986247)
    ·
      refine ⟨268101252063757411055979371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178734168042504940703986247 268101252063757411055979371)
      ·
        refine ⟨402151878095636116583969057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268101252063757411055979371 402151878095636116583969057)
        ·
          refine ⟨301613908571727087437976793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402151878095636116583969057 301613908571727087437976793)
          ·
            refine ⟨226210431428795315578482595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301613908571727087437976793 226210431428795315578482595)
            ·
              refine ⟨339315647143192973367723893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226210431428795315578482595 339315647143192973367723893)
              ·
                refine ⟨31810841919674341253224115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339315647143192973367723893 31810841919674341253224115)
                ·
                  refine ⟨47716262879511511879836173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31810841919674341253224115 47716262879511511879836173)
                  ·
                    refine ⟨17893598579816816954938565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47716262879511511879836173 17893598579816816954938565)
                    ·
                      refine ⟨3355049733715653179050981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17893598579816816954938565 3355049733715653179050981)
                      ·
                        rfl

theorem cell23_6533936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_6533936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533936 prefixEnd_6533936 := by exact prefixLift 6533936
  have htrace : WordTrace (prefixWord ++ tailWord_6533936) baseStart_6533936 baseEnd_6533936 := by
    simpa [prefixWord, tailWord_6533936, baseEnd_6533936] using wordTrace_append hprefix tailTrace_6533936
  have hstable : (prefixWord ++ tailWord_6533936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533936).length < 2 ^ (prefixWord ++ tailWord_6533936).sum := by decide
  have hdescent : baseEnd_6533936 < baseStart_6533936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533970 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_6533970 : Nat := 118140960795 + 6533970 * 2 ^ 59
def prefixEnd_6533970 : Nat := 4983230072969 + 3 ^ 40 * 6533970 * 2
def baseEnd_6533970 : Nat := 3355067192057906046025825

theorem tailTrace_6533970 : CollatzResearch.WordTrace tailWord_6533970 prefixEnd_6533970 3355067192057906046025825 := by
  unfold tailWord_6533970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59578366034637519519679841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158875642759033385385812909 59578366034637519519679841)
  ·
    refine ⟨44683774525978139639759881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59578366034637519519679841 44683774525978139639759881)
    ·
      refine ⟨33512830894483604729819911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44683774525978139639759881 33512830894483604729819911)
      ·
        refine ⟨50269246341725407094729867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33512830894483604729819911 50269246341725407094729867)
        ·
          refine ⟨75403869512588110642094801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50269246341725407094729867 75403869512588110642094801)
          ·
            refine ⟨56552902134441082981571101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75403869512588110642094801 56552902134441082981571101)
            ·
              refine ⟨21207338300415406118089163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56552902134441082981571101 21207338300415406118089163)
              ·
                refine ⟨31811007450623109177133745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21207338300415406118089163 31811007450623109177133745)
                ·
                  refine ⟨23858255587967331882850309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31811007450623109177133745 23858255587967331882850309)
                  ·
                    refine ⟨4473422922743874728034433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23858255587967331882850309 4473422922743874728034433)
                    ·
                      refine ⟨3355067192057906046025825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473422922743874728034433 3355067192057906046025825)
                      ·
                        rfl

theorem cell23_6533970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_6533970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533970 prefixEnd_6533970 := by exact prefixLift 6533970
  have htrace : WordTrace (prefixWord ++ tailWord_6533970) baseStart_6533970 baseEnd_6533970 := by
    simpa [prefixWord, tailWord_6533970, baseEnd_6533970] using wordTrace_append hprefix tailTrace_6533970
  have hstable : (prefixWord ++ tailWord_6533970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533970).length < 2 ^ (prefixWord ++ tailWord_6533970).sum := by decide
  have hdescent : baseEnd_6533970 < baseStart_6533970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533973 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6533973 : Nat := 118140960795 + 6533973 * 2 ^ 59
def prefixEnd_6533973 : Nat := 4983230072969 + 3 ^ 40 * 6533973 * 2
def baseEnd_6533973 : Nat := 3355068732499869534288311

theorem tailTrace_6533973 : CollatzResearch.WordTrace tailWord_6533973 prefixEnd_6533973 3355068732499869534288311 := by
  unfold tailWord_6533973
  simp only [CollatzResearch.WordTrace]
  refine ⟨238313573557539209591078573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158875715705026139727385715 238313573557539209591078573)
  ·
    refine ⟨89367590084077203596654465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238313573557539209591078573 89367590084077203596654465)
    ·
      refine ⟨67025692563057902697490849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89367590084077203596654465 67025692563057902697490849)
      ·
        refine ⟨50269269422293427023118137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67025692563057902697490849 50269269422293427023118137)
        ·
          refine ⟨37701952066720070267338603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50269269422293427023118137 37701952066720070267338603)
          ·
            refine ⟨56552928100080105401007905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37701952066720070267338603 56552928100080105401007905)
            ·
              refine ⟨42414696075060079050755929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56552928100080105401007905 42414696075060079050755929)
              ·
                refine ⟨31811022056295059288066947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42414696075060079050755929 31811022056295059288066947)
                ·
                  refine ⟨47716533084442588932100421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31811022056295059288066947 47716533084442588932100421)
                  ·
                    refine ⟨8946849953332985424768829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47716533084442588932100421 8946849953332985424768829)
                    ·
                      refine ⟨3355068732499869534288311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8946849953332985424768829 3355068732499869534288311)
                      ·
                        rfl

theorem cell23_6533973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6533973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533973 prefixEnd_6533973 := by exact prefixLift 6533973
  have htrace : WordTrace (prefixWord ++ tailWord_6533973) baseStart_6533973 baseEnd_6533973 := by
    simpa [prefixWord, tailWord_6533973, baseEnd_6533973] using wordTrace_append hprefix tailTrace_6533973
  have hstable : (prefixWord ++ tailWord_6533973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533973).length < 2 ^ (prefixWord ++ tailWord_6533973).sum := by decide
  have hdescent : baseEnd_6533973 < baseStart_6533973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6533980 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6533980 : Nat := 118140960795 + 6533980 * 2 ^ 59
def prefixEnd_6533980 : Nat := 4983230072969 + 3 ^ 40 * 6533980 * 2
def baseEnd_6533980 : Nat := 1118357442288150335633593

theorem tailTrace_6533980 : CollatzResearch.WordTrace tailWord_6533980 prefixEnd_6533980 1118357442288150335633593 := by
  unfold tailWord_6533980
  simp only [CollatzResearch.WordTrace]
  refine ⟨119156914434256924893291697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158875885912342566524388929 119156914434256924893291697)
  ·
    refine ⟨89367685825692693669968773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119156914434256924893291697 89367685825692693669968773)
    ·
      refine ⟨16756441092317380063119145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89367685825692693669968773 16756441092317380063119145)
      ·
        refine ⟨12567330819238035047339359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16756441092317380063119145 12567330819238035047339359)
        ·
          refine ⟨18850996228857052571009039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567330819238035047339359 18850996228857052571009039)
          ·
            refine ⟨28276494343285578856513559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850996228857052571009039 28276494343285578856513559)
            ·
              refine ⟨42414741514928368284770339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28276494343285578856513559 42414741514928368284770339)
              ·
                refine ⟨63622112272392552427155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42414741514928368284770339 63622112272392552427155509)
                ·
                  refine ⟨5964573025536801790045829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63622112272392552427155509 5964573025536801790045829)
                  ·
                    refine ⟨1118357442288150335633593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964573025536801790045829 1118357442288150335633593)
                    ·
                      rfl

theorem cell23_6533980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6533980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6533980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6533980 prefixEnd_6533980 := by exact prefixLift 6533980
  have htrace : WordTrace (prefixWord ++ tailWord_6533980) baseStart_6533980 baseEnd_6533980 := by
    simpa [prefixWord, tailWord_6533980, baseEnd_6533980] using wordTrace_append hprefix tailTrace_6533980
  have hstable : (prefixWord ++ tailWord_6533980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6533980).length < 2 ^ (prefixWord ++ tailWord_6533980).sum := by decide
  have hdescent : baseEnd_6533980 < baseStart_6533980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6533980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534014 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6534014 : Nat := 118140960795 + 6534014 * 2 ^ 59
def prefixEnd_6534014 : Nat := 4983230072969 + 3 ^ 40 * 6534014 * 2
def baseEnd_6534014 : Nat := 1118363261735567957958541

theorem tailTrace_6534014 : CollatzResearch.WordTrace tailWord_6534014 prefixEnd_6534014 1118363261735567957958541 := by
  unfold tailWord_6534014
  simp only [CollatzResearch.WordTrace]
  refine ⟨29789383618798834199165137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158876712633593782395547397 29789383618798834199165137)
  ·
    refine ⟨22342037714099125649373853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29789383618798834199165137 22342037714099125649373853)
    ·
      refine ⟨8378264142787172118515195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22342037714099125649373853 8378264142787172118515195)
      ·
        refine ⟨12567396214180758177772793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378264142787172118515195 12567396214180758177772793)
        ·
          refine ⟨9425547160635568633329595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12567396214180758177772793 9425547160635568633329595)
          ·
            refine ⟨14138320740953352949994393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425547160635568633329595 14138320740953352949994393)
            ·
              refine ⟨10603740555715014712495795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138320740953352949994393 10603740555715014712495795)
              ·
                refine ⟨15905610833572522068743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603740555715014712495795 15905610833572522068743693)
                ·
                  refine ⟨5964604062589695775778885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15905610833572522068743693 5964604062589695775778885)
                  ·
                    refine ⟨1118363261735567957958541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964604062589695775778885 1118363261735567957958541)
                    ·
                      rfl

theorem cell23_6534014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6534014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534014 prefixEnd_6534014 := by exact prefixLift 6534014
  have htrace : WordTrace (prefixWord ++ tailWord_6534014) baseStart_6534014 baseEnd_6534014 := by
    simpa [prefixWord, tailWord_6534014, baseEnd_6534014] using wordTrace_append hprefix tailTrace_6534014
  have hstable : (prefixWord ++ tailWord_6534014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534014).length < 2 ^ (prefixWord ++ tailWord_6534014).sum := by decide
  have hdescent : baseEnd_6534014 < baseStart_6534014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534016 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_6534016 : Nat := 118140960795 + 6534016 * 2 ^ 59
def prefixEnd_6534016 : Nat := 4983230072969 + 3 ^ 40 * 6534016 * 2
def baseEnd_6534016 : Nat := 3355090812168012866050613

theorem tailTrace_6534016 : CollatzResearch.WordTrace tailWord_6534016 prefixEnd_6534016 3355090812168012866050613 := by
  unfold tailWord_6534016
  simp only [CollatzResearch.WordTrace]
  refine ⟨119157570948191713967446951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158876761264255618623262601 119157570948191713967446951)
  ·
    refine ⟨178736356422287570951170427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119157570948191713967446951 178736356422287570951170427)
    ·
      refine ⟨268104534633431356426755641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178736356422287570951170427 268104534633431356426755641)
      ·
        refine ⟨201078400975073517320066731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268104534633431356426755641 201078400975073517320066731)
        ·
          refine ⟨301617601462610275980100097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201078400975073517320066731 301617601462610275980100097)
          ·
            refine ⟨226213201096957706985075073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301617601462610275980100097 226213201096957706985075073)
            ·
              refine ⟨169659900822718280238806305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226213201096957706985075073 169659900822718280238806305)
              ·
                refine ⟨127244925617038710179104729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169659900822718280238806305 127244925617038710179104729)
                ·
                  refine ⟨95433694212779032634328547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127244925617038710179104729 95433694212779032634328547)
                  ·
                    refine ⟨143150541319168548951492821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95433694212779032634328547 143150541319168548951492821)
                    ·
                      refine ⟨3355090812168012866050613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143150541319168548951492821 3355090812168012866050613)
                      ·
                        rfl

theorem cell23_6534016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_6534016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534016 prefixEnd_6534016 := by exact prefixLift 6534016
  have htrace : WordTrace (prefixWord ++ tailWord_6534016) baseStart_6534016 baseEnd_6534016 := by
    simpa [prefixWord, tailWord_6534016, baseEnd_6534016] using wordTrace_append hprefix tailTrace_6534016
  have hstable : (prefixWord ++ tailWord_6534016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534016).length < 2 ^ (prefixWord ++ tailWord_6534016).sum := by decide
  have hdescent : baseEnd_6534016 < baseStart_6534016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534073 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6534073 : Nat := 118140960795 + 6534073 * 2 ^ 59
def prefixEnd_6534073 : Nat := 4983230072969 + 3 ^ 40 * 6534073 * 2
def baseEnd_6534073 : Nat := 3355120080565319143037851

theorem tailTrace_6534073 : CollatzResearch.WordTrace tailWord_6534073 prefixEnd_6534073 3355120080565319143037851 := by
  unfold tailWord_6534073
  simp only [CollatzResearch.WordTrace]
  refine ⟨238317220857176926669718873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158878147238117951113145915 238317220857176926669718873)
  ·
    refine ⟨178737915642882695002289155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238317220857176926669718873 178737915642882695002289155)
    ·
      refine ⟨268106873464324042503433733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178737915642882695002289155 268106873464324042503433733)
      ·
        refine ⟨50270038774560757969393825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268106873464324042503433733 50270038774560757969393825)
        ·
          refine ⟨37702529080920568477045369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50270038774560757969393825 37702529080920568477045369)
          ·
            refine ⟨28276896810690426357784027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37702529080920568477045369 28276896810690426357784027)
            ·
              refine ⟨42415345216035639536676041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28276896810690426357784027 42415345216035639536676041)
              ·
                refine ⟨31811508912026729652507031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42415345216035639536676041 31811508912026729652507031)
                ·
                  refine ⟨47717263368040094478760547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31811508912026729652507031 47717263368040094478760547)
                  ·
                    refine ⟨71575895052060141718140821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47717263368040094478760547 71575895052060141718140821)
                    ·
                      refine ⟨3355120080565319143037851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71575895052060141718140821 3355120080565319143037851)
                      ·
                        rfl

theorem cell23_6534073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6534073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534073 prefixEnd_6534073 := by exact prefixLift 6534073
  have htrace : WordTrace (prefixWord ++ tailWord_6534073) baseStart_6534073 baseEnd_6534073 := by
    simpa [prefixWord, tailWord_6534073, baseEnd_6534073] using wordTrace_append hprefix tailTrace_6534073
  have hstable : (prefixWord ++ tailWord_6534073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534073).length < 2 ^ (prefixWord ++ tailWord_6534073).sum := by decide
  have hdescent : baseEnd_6534073 < baseStart_6534073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534087 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 2, 4]
def baseStart_6534087 : Nat := 118140960795 + 6534087 * 2 ^ 59
def prefixEnd_6534087 : Nat := 4983230072969 + 3 ^ 40 * 6534087 * 2
def baseEnd_6534087 : Nat := 1118375756431494029420929

theorem tailTrace_6534087 : CollatzResearch.WordTrace tailWord_6534087 prefixEnd_6534087 1118375756431494029420929 := by
  unfold tailWord_6534087
  simp only [CollatzResearch.WordTrace]
  refine ⟨238317731479126207060728515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158878487652750804707152343 238317731479126207060728515)
  ·
    refine ⟨357476597218689310591092773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238317731479126207060728515 357476597218689310591092773)
    ·
      refine ⟨67026861978504245735829895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357476597218689310591092773 67026861978504245735829895)
      ·
        refine ⟨100540292967756368603744843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67026861978504245735829895 100540292967756368603744843)
        ·
          refine ⟨150810439451634552905617265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100540292967756368603744843 150810439451634552905617265)
          ·
            refine ⟨113107829588725914679212949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150810439451634552905617265 113107829588725914679212949)
            ·
              refine ⟨5301929511971527250588107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113107829588725914679212949 5301929511971527250588107)
              ·
                refine ⟨7952894267957290875882161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5301929511971527250588107 7952894267957290875882161)
                ·
                  refine ⟨5964670700967968156911621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7952894267957290875882161 5964670700967968156911621)
                  ·
                    refine ⟨1118375756431494029420929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964670700967968156911621 1118375756431494029420929)
                    ·
                      rfl

theorem cell23_6534087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_6534087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534087 prefixEnd_6534087 := by exact prefixLift 6534087
  have htrace : WordTrace (prefixWord ++ tailWord_6534087) baseStart_6534087 baseEnd_6534087 := by
    simpa [prefixWord, tailWord_6534087, baseEnd_6534087] using wordTrace_append hprefix tailTrace_6534087
  have hstable : (prefixWord ++ tailWord_6534087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534087).length < 2 ^ (prefixWord ++ tailWord_6534087).sum := by decide
  have hdescent : baseEnd_6534087 < baseStart_6534087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534114 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6534114 : Nat := 118140960795 + 6534114 * 2 ^ 59
def prefixEnd_6534114 : Nat := 4983230072969 + 3 ^ 40 * 6534114 * 2
def baseEnd_6534114 : Nat := 3355141133272153482625163

theorem tailTrace_6534114 : CollatzResearch.WordTrace tailWord_6534114 prefixEnd_6534114 3355141133272153482625163 := by
  unfold tailWord_6534114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59579679062507097667990349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158879144166685593781307597 59579679062507097667990349)
  ·
    refine ⟨22342379648440161625496381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59579679062507097667990349 22342379648440161625496381)
    ·
      refine ⟨8378392368165060609561143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22342379648440161625496381 8378392368165060609561143)
      ·
        refine ⟨12567588552247590914341715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378392368165060609561143 12567588552247590914341715)
        ·
          refine ⟨18851382828371386371512573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567588552247590914341715 18851382828371386371512573)
          ·
            refine ⟨7069268560639269889317215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18851382828371386371512573 7069268560639269889317215)
            ·
              refine ⟨10603902840958904833975823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069268560639269889317215 10603902840958904833975823)
              ·
                refine ⟨15905854261438357250963735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10603902840958904833975823 15905854261438357250963735)
                ·
                  refine ⟨23858781392157535876445603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15905854261438357250963735 23858781392157535876445603)
                  ·
                    refine ⟨35788172088236303814668405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23858781392157535876445603 35788172088236303814668405)
                    ·
                      refine ⟨3355141133272153482625163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35788172088236303814668405 3355141133272153482625163)
                      ·
                        rfl

theorem cell23_6534114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6534114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534114 prefixEnd_6534114 := by exact prefixLift 6534114
  have htrace : WordTrace (prefixWord ++ tailWord_6534114) baseStart_6534114 baseEnd_6534114 := by
    simpa [prefixWord, tailWord_6534114, baseEnd_6534114] using wordTrace_append hprefix tailTrace_6534114
  have hstable : (prefixWord ++ tailWord_6534114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534114).length < 2 ^ (prefixWord ++ tailWord_6534114).sum := by decide
  have hdescent : baseEnd_6534114 < baseStart_6534114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534127 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_6534127 : Nat := 118140960795 + 6534127 * 2 ^ 59
def prefixEnd_6534127 : Nat := 4983230072969 + 3 ^ 40 * 6534127 * 2
def baseEnd_6534127 : Nat := 3355147808520661931762603

theorem tailTrace_6534127 : CollatzResearch.WordTrace tailWord_6534127 prefixEnd_6534127 3355147808520661931762603 := by
  unfold tailWord_6534127
  simp only [CollatzResearch.WordTrace]
  refine ⟨238319190398981293892184635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158879460265987529261456423 238319190398981293892184635)
  ·
    refine ⟨357478785598471940838276953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238319190398981293892184635 357478785598471940838276953)
    ·
      refine ⟨268109089198853955628707715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357478785598471940838276953 268109089198853955628707715)
      ·
        refine ⟨402163633798280933443061573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268109089198853955628707715 402163633798280933443061573)
        ·
          refine ⟨75405681337177675020574045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402163633798280933443061573 75405681337177675020574045)
          ·
            refine ⟨28277130501441628132715267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75405681337177675020574045 28277130501441628132715267)
            ·
              refine ⟨42415695752162442199072901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28277130501441628132715267 42415695752162442199072901)
              ·
                refine ⟨7952942953530457912326169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42415695752162442199072901 7952942953530457912326169)
                ·
                  refine ⟨5964707215147843434244627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7952942953530457912326169 5964707215147843434244627)
                  ·
                    refine ⟨8947060822721765151366941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5964707215147843434244627 8947060822721765151366941)
                    ·
                      refine ⟨3355147808520661931762603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8947060822721765151366941 3355147808520661931762603)
                      ·
                        rfl

theorem cell23_6534127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_6534127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534127 prefixEnd_6534127 := by exact prefixLift 6534127
  have htrace : WordTrace (prefixWord ++ tailWord_6534127) baseStart_6534127 baseEnd_6534127 := by
    simpa [prefixWord, tailWord_6534127, baseEnd_6534127] using wordTrace_append hprefix tailTrace_6534127
  have hstable : (prefixWord ++ tailWord_6534127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534127).length < 2 ^ (prefixWord ++ tailWord_6534127).sum := by decide
  have hdescent : baseEnd_6534127 < baseStart_6534127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534153 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_6534153 : Nat := 118140960795 + 6534153 * 2 ^ 59
def prefixEnd_6534153 : Nat := 4983230072969 + 3 ^ 40 * 6534153 * 2
def baseEnd_6534153 : Nat := 3355161159017678830037483

theorem tailTrace_6534153 : CollatzResearch.WordTrace tailWord_6534153 prefixEnd_6534153 3355161159017678830037483 := by
  unfold tailWord_6534153
  simp only [CollatzResearch.WordTrace]
  refine ⟨238320138696887100332631113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158880092464591400221754075 238320138696887100332631113)
  ·
    refine ⟨178740104022665325249473335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238320138696887100332631113 178740104022665325249473335)
    ·
      refine ⟨268110156033997987874210003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178740104022665325249473335 268110156033997987874210003)
      ·
        refine ⟨402165234050996981811315005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268110156033997987874210003 402165234050996981811315005)
        ·
          refine ⟨150811962769123868179243127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402165234050996981811315005 150811962769123868179243127)
          ·
            refine ⟨226217944153685802268864691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150811962769123868179243127 226217944153685802268864691)
            ·
              refine ⟨339326916230528703403297037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226217944153685802268864691 339326916230528703403297037)
              ·
                refine ⟨127247593586448263776236389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339326916230528703403297037 127247593586448263776236389)
                ·
                  refine ⟨23858923797459049458044323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127247593586448263776236389 23858923797459049458044323)
                  ·
                    refine ⟨35788385696188574187066485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23858923797459049458044323 35788385696188574187066485)
                    ·
                      refine ⟨3355161159017678830037483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35788385696188574187066485 3355161159017678830037483)
                      ·
                        rfl

theorem cell23_6534153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_6534153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534153 prefixEnd_6534153 := by exact prefixLift 6534153
  have htrace : WordTrace (prefixWord ++ tailWord_6534153) baseStart_6534153 baseEnd_6534153 := by
    simpa [prefixWord, tailWord_6534153, baseEnd_6534153] using wordTrace_append hprefix tailTrace_6534153
  have hstable : (prefixWord ++ tailWord_6534153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534153).length < 2 ^ (prefixWord ++ tailWord_6534153).sum := by decide
  have hdescent : baseEnd_6534153 < baseStart_6534153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534162 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6534162 : Nat := 118140960795 + 6534162 * 2 ^ 59
def prefixEnd_6534162 : Nat := 4983230072969 + 3 ^ 40 * 6534162 * 2
def baseEnd_6534162 : Nat := 3355165780343569294824943

theorem tailTrace_6534162 : CollatzResearch.WordTrace tailWord_6534162 prefixEnd_6534162 3355165780343569294824943 := by
  unfold tailWord_6534162
  simp only [CollatzResearch.WordTrace]
  refine ⟨59580116738463623717427185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158880311302569663246472493 59580116738463623717427185)
  ·
    refine ⟨44685087553847717788070389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59580116738463623717427185 44685087553847717788070389)
    ·
      refine ⟨4189226958173223542631599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44685087553847717788070389 4189226958173223542631599)
      ·
        refine ⟨6283840437259835313947399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189226958173223542631599 6283840437259835313947399)
        ·
          refine ⟨9425760655889752970921099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283840437259835313947399 9425760655889752970921099)
          ·
            refine ⟨14138640983834629456381649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425760655889752970921099 14138640983834629456381649)
            ·
              refine ⟨10603980737875972092286237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138640983834629456381649 10603980737875972092286237)
              ·
                refine ⟨3976492776703489534607339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10603980737875972092286237 3976492776703489534607339)
                ·
                  refine ⟨5964739165055234301911009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976492776703489534607339 5964739165055234301911009)
                  ·
                    refine ⟨4473554373791425726433257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5964739165055234301911009 4473554373791425726433257)
                    ·
                      refine ⟨3355165780343569294824943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473554373791425726433257 3355165780343569294824943)
                      ·
                        rfl

theorem cell23_6534162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6534162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534162 prefixEnd_6534162 := by exact prefixLift 6534162
  have htrace : WordTrace (prefixWord ++ tailWord_6534162) baseStart_6534162 baseEnd_6534162 := by
    simpa [prefixWord, tailWord_6534162, baseEnd_6534162] using wordTrace_append hprefix tailTrace_6534162
  have hstable : (prefixWord ++ tailWord_6534162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534162).length < 2 ^ (prefixWord ++ tailWord_6534162).sum := by decide
  have hdescent : baseEnd_6534162 < baseStart_6534162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534163 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_6534163 : Nat := 118140960795 + 6534163 * 2 ^ 59
def prefixEnd_6534163 : Nat := 4983230072969 + 3 ^ 40 * 6534163 * 2
def baseEnd_6534163 : Nat := 3355166293824223790912437

theorem tailTrace_6534163 : CollatzResearch.WordTrace tailWord_6534163 prefixEnd_6534163 3355166293824223790912437 := by
  unfold tailWord_6534163
  simp only [CollatzResearch.WordTrace]
  refine ⟨238320503426850872040495143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158880335617900581360330095 238320503426850872040495143)
  ·
    refine ⟨357480755140276308060742715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238320503426850872040495143 357480755140276308060742715)
    ·
      refine ⟨536221132710414462091114073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357480755140276308060742715 536221132710414462091114073)
      ·
        refine ⟨402165849532810846568335555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536221132710414462091114073 402165849532810846568335555)
        ·
          refine ⟨603248774299216269852503333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402165849532810846568335555 603248774299216269852503333)
          ·
            refine ⟨113109145181103050597344375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 603248774299216269852503333 113109145181103050597344375)
            ·
              refine ⟨169663717771654575896016563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113109145181103050597344375 169663717771654575896016563)
              ·
                refine ⟨254495576657481863844024845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169663717771654575896016563 254495576657481863844024845)
                ·
                  refine ⟨95435841246555698941509317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254495576657481863844024845 95435841246555698941509317)
                  ·
                    refine ⟨17894220233729193551532997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95435841246555698941509317 17894220233729193551532997)
                    ·
                      refine ⟨3355166293824223790912437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17894220233729193551532997 3355166293824223790912437)
                      ·
                        rfl

theorem cell23_6534163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_6534163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534163 prefixEnd_6534163 := by exact prefixLift 6534163
  have htrace : WordTrace (prefixWord ++ tailWord_6534163) baseStart_6534163 baseEnd_6534163 := by
    simpa [prefixWord, tailWord_6534163, baseEnd_6534163] using wordTrace_append hprefix tailTrace_6534163
  have hstable : (prefixWord ++ tailWord_6534163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534163).length < 2 ^ (prefixWord ++ tailWord_6534163).sum := by decide
  have hdescent : baseEnd_6534163 < baseStart_6534163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534220 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_6534220 : Nat := 118140960795 + 6534220 * 2 ^ 59
def prefixEnd_6534220 : Nat := 4983230072969 + 3 ^ 40 * 6534220 * 2
def baseEnd_6534220 : Nat := 1118398520740510022633225

theorem tailTrace_6534220 : CollatzResearch.WordTrace tailWord_6534220 prefixEnd_6534220 1118398520740510022633225 := by
  unfold tailWord_6534220
  simp only [CollatzResearch.WordTrace]
  refine ⟨119161291193822185387660057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158881721591762913850213409 119161291193822185387660057)
  ·
    refine ⟨89370968395366639040745043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119161291193822185387660057 89370968395366639040745043)
    ·
      refine ⟨134056452593049958561117565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89370968395366639040745043 134056452593049958561117565)
      ·
        refine ⟨50271169722393734460419087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134056452593049958561117565 50271169722393734460419087)
        ·
          refine ⟨75406754583590601690628631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50271169722393734460419087 75406754583590601690628631)
          ·
            refine ⟨113110131875385902535942947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75406754583590601690628631 113110131875385902535942947)
            ·
              refine ⟨169665197813078853803914421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113110131875385902535942947 169665197813078853803914421)
              ·
                refine ⟨15906112294976142544116977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169665197813078853803914421 15906112294976142544116977)
                ·
                  refine ⟨11929584221232106908087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15906112294976142544116977 11929584221232106908087733)
                  ·
                    refine ⟨1118398520740510022633225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11929584221232106908087733 1118398520740510022633225)
                    ·
                      rfl

theorem cell23_6534220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_6534220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534220 prefixEnd_6534220 := by exact prefixLift 6534220
  have htrace : WordTrace (prefixWord ++ tailWord_6534220) baseStart_6534220 baseEnd_6534220 := by
    simpa [prefixWord, tailWord_6534220, baseEnd_6534220] using wordTrace_append hprefix tailTrace_6534220
  have hstable : (prefixWord ++ tailWord_6534220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534220).length < 2 ^ (prefixWord ++ tailWord_6534220).sum := by decide
  have hdescent : baseEnd_6534220 < baseStart_6534220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534307 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 3]
def baseStart_6534307 : Nat := 118140960795 + 6534307 * 2 ^ 59
def prefixEnd_6534307 : Nat := 4983230072969 + 3 ^ 40 * 6534307 * 2
def baseEnd_6534307 : Nat := 3355240235038471227511775

theorem tailTrace_6534307 : CollatzResearch.WordTrace tailWord_6534307 prefixEnd_6534307 3355240235038471227511775 := by
  unfold tailWord_6534307
  simp only [CollatzResearch.WordTrace]
  refine ⟨238325755538329184633737175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158883837025552789755824783 238325755538329184633737175)
  ·
    refine ⟨357488633307493776950605763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238325755538329184633737175 357488633307493776950605763)
    ·
      refine ⟨536232949961240665425908645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357488633307493776950605763 536232949961240665425908645)
      ·
        refine ⟨100543678117732624767357871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536232949961240665425908645 100543678117732624767357871)
        ·
          refine ⟨150815517176598937151036807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100543678117732624767357871 150815517176598937151036807)
          ·
            refine ⟨226223275764898405726555211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150815517176598937151036807 226223275764898405726555211)
            ·
              refine ⟨339334913647347608589832817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226223275764898405726555211 339334913647347608589832817)
              ·
                refine ⟨254501185235510706442374613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339334913647347608589832817 254501185235510706442374613)
                ·
                  refine ⟨5964871528957282182243155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 254501185235510706442374613 5964871528957282182243155)
                  ·
                    refine ⟨8947307293435923273364733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5964871528957282182243155 8947307293435923273364733)
                    ·
                      refine ⟨3355240235038471227511775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8947307293435923273364733 3355240235038471227511775)
                      ·
                        rfl

theorem cell23_6534307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_6534307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534307 prefixEnd_6534307 := by exact prefixLift 6534307
  have htrace : WordTrace (prefixWord ++ tailWord_6534307) baseStart_6534307 baseEnd_6534307 := by
    simpa [prefixWord, tailWord_6534307, baseEnd_6534307] using wordTrace_append hprefix tailTrace_6534307
  have hstable : (prefixWord ++ tailWord_6534307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534307).length < 2 ^ (prefixWord ++ tailWord_6534307).sum := by decide
  have hdescent : baseEnd_6534307 < baseStart_6534307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534314 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 6]
def baseStart_6534314 : Nat := 118140960795 + 6534314 * 2 ^ 59
def prefixEnd_6534314 : Nat := 4983230072969 + 3 ^ 40 * 6534314 * 2
def baseEnd_6534314 : Nat := 372804869933672522236027

theorem tailTrace_6534314 : CollatzResearch.WordTrace tailWord_6534314 prefixEnd_6534314 372804869933672522236027 := by
  unfold tailWord_6534314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59581502712325956207310499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158884007232869216552827997 59581502712325956207310499)
  ·
    refine ⟨89372254068488934310965749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59581502712325956207310499 89372254068488934310965749)
    ·
      refine ⟨8378648818920837591653039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89372254068488934310965749 8378648818920837591653039)
      ·
        refine ⟨12567973228381256387479559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378648818920837591653039 12567973228381256387479559)
        ·
          refine ⟨18851959842571884581219339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567973228381256387479559 18851959842571884581219339)
          ·
            refine ⟨28277939763857826871829009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18851959842571884581219339 28277939763857826871829009)
            ·
              refine ⟨21208454822893370153871757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28277939763857826871829009 21208454822893370153871757)
              ·
                refine ⟨7953170558585013807701909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21208454822893370153871757 7953170558585013807701909)
                ·
                  refine ⟨372804869933672522236027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7953170558585013807701909 372804869933672522236027)
                  ·
                    rfl

theorem cell23_6534314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_6534314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534314 prefixEnd_6534314 := by exact prefixLift 6534314
  have htrace : WordTrace (prefixWord ++ tailWord_6534314) baseStart_6534314 baseEnd_6534314 := by
    simpa [prefixWord, tailWord_6534314, baseEnd_6534314] using wordTrace_append hprefix tailTrace_6534314
  have hstable : (prefixWord ++ tailWord_6534314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534314).length < 2 ^ (prefixWord ++ tailWord_6534314).sum := by decide
  have hdescent : baseEnd_6534314 < baseStart_6534314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534327 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 1, 5]
def baseStart_6534327 : Nat := 118140960795 + 6534327 * 2 ^ 59
def prefixEnd_6534327 : Nat := 4983230072969 + 3 ^ 40 * 6534327 * 2
def baseEnd_6534327 : Nat := 1118416834883853716420561

theorem tailTrace_6534327 : CollatzResearch.WordTrace tailWord_6534327 prefixEnd_6534327 1118416834883853716420561 := by
  unfold tailWord_6534327
  simp only [CollatzResearch.WordTrace]
  refine ⟨238326484998256728049465235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158884323332171152032976823 238326484998256728049465235)
  ·
    refine ⟨357489727497385092074197853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238326484998256728049465235 357489727497385092074197853)
    ·
      refine ⟨134058647811519409527824195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357489727497385092074197853 134058647811519409527824195)
      ·
        refine ⟨201087971717279114291736293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134058647811519409527824195 201087971717279114291736293)
        ·
          refine ⟨37703994696989833929700555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201087971717279114291736293 37703994696989833929700555)
          ·
            refine ⟨56555992045484750894550833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37703994696989833929700555 56555992045484750894550833)
            ·
              refine ⟨42416994034113563170913125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56555992045484750894550833 42416994034113563170913125)
              ·
                refine ⟨7953186381396293094546211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42416994034113563170913125 7953186381396293094546211)
                ·
                  refine ⟨11929779572094439641819317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953186381396293094546211 11929779572094439641819317)
                  ·
                    refine ⟨1118416834883853716420561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11929779572094439641819317 1118416834883853716420561)
                    ·
                      rfl

theorem cell23_6534327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_6534327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534327 prefixEnd_6534327 := by exact prefixLift 6534327
  have htrace : WordTrace (prefixWord ++ tailWord_6534327) baseStart_6534327 baseEnd_6534327 := by
    simpa [prefixWord, tailWord_6534327, baseEnd_6534327] using wordTrace_append hprefix tailTrace_6534327
  have hstable : (prefixWord ++ tailWord_6534327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534327).length < 2 ^ (prefixWord ++ tailWord_6534327).sum := by decide
  have hdescent : baseEnd_6534327 < baseStart_6534327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534344 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_6534344 : Nat := 118140960795 + 6534344 * 2 ^ 59
def prefixEnd_6534344 : Nat := 4983230072969 + 3 ^ 40 * 6534344 * 2
def baseEnd_6534344 : Nat := 1118419744607562527583035

theorem tailTrace_6534344 : CollatzResearch.WordTrace tailWord_6534344 prefixEnd_6534344 1118419744607562527583035 := by
  unfold tailWord_6534344
  simp only [CollatzResearch.WordTrace]
  refine ⟨119163552519597569976417043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158884736692796759968556057 119163552519597569976417043)
  ·
    refine ⟨178745328779396354964625565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119163552519597569976417043 178745328779396354964625565)
    ·
      refine ⟨67029498292273633111734587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178745328779396354964625565 67029498292273633111734587)
      ·
        refine ⟨100544247438410449667601881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67029498292273633111734587 100544247438410449667601881)
        ·
          refine ⟨75408185578807837250701411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100544247438410449667601881 75408185578807837250701411)
          ·
            refine ⟨113112278368211755876052117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75408185578807837250701411 113112278368211755876052117)
            ·
              refine ⟨5302138048509926056689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113112278368211755876052117 5302138048509926056689943)
              ·
                refine ⟨7953207072764889085034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302138048509926056689943 7953207072764889085034915)
                ·
                  refine ⟨11929810609147333627552373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953207072764889085034915 11929810609147333627552373)
                  ·
                    refine ⟨1118419744607562527583035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11929810609147333627552373 1118419744607562527583035)
                    ·
                      rfl

theorem cell23_6534344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_6534344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534344 prefixEnd_6534344 := by exact prefixLift 6534344
  have htrace : WordTrace (prefixWord ++ tailWord_6534344) baseStart_6534344 baseEnd_6534344 := by
    simpa [prefixWord, tailWord_6534344, baseEnd_6534344] using wordTrace_append hprefix tailTrace_6534344
  have hstable : (prefixWord ++ tailWord_6534344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534344).length < 2 ^ (prefixWord ++ tailWord_6534344).sum := by decide
  have hdescent : baseEnd_6534344 < baseStart_6534344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534367 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_6534367 : Nat := 118140960795 + 6534367 * 2 ^ 59
def prefixEnd_6534367 : Nat := 4983230072969 + 3 ^ 40 * 6534367 * 2
def baseEnd_6534367 : Nat := 3355271043877740992761499

theorem tailTrace_6534367 : CollatzResearch.WordTrace tailWord_6534367 prefixEnd_6534367 3355271043877740992761499 := by
  unfold tailWord_6534367
  simp only [CollatzResearch.WordTrace]
  refine ⟨238327943918111814880921355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158885295945407876587280903 238327943918111814880921355)
  ·
    refine ⟨357491915877167722321382033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238327943918111814880921355 357491915877167722321382033)
    ·
      refine ⟨268118936907875791741036525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357491915877167722321382033 268118936907875791741036525)
      ·
        refine ⟨100544601340453421902888697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268118936907875791741036525 100544601340453421902888697)
        ·
          refine ⟨75408451005340066427166523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100544601340453421902888697 75408451005340066427166523)
          ·
            refine ⟨113112676508010099640749785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75408451005340066427166523 113112676508010099640749785)
            ·
              refine ⟨84834507381007574730562339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113112676508010099640749785 84834507381007574730562339)
              ·
                refine ⟨127251761071511362095843509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84834507381007574730562339 127251761071511362095843509)
                ·
                  refine ⟨11929852600454190196485329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127251761071511362095843509 11929852600454190196485329)
                  ·
                    refine ⟨8947389450340642647363997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11929852600454190196485329 8947389450340642647363997)
                    ·
                      refine ⟨3355271043877740992761499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8947389450340642647363997 3355271043877740992761499)
                      ·
                        rfl

theorem cell23_6534367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_6534367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534367 prefixEnd_6534367 := by exact prefixLift 6534367
  have htrace : WordTrace (prefixWord ++ tailWord_6534367) baseStart_6534367 baseEnd_6534367 := by
    simpa [prefixWord, tailWord_6534367, baseEnd_6534367] using wordTrace_append hprefix tailTrace_6534367
  have hstable : (prefixWord ++ tailWord_6534367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534367).length < 2 ^ (prefixWord ++ tailWord_6534367).sum := by decide
  have hdescent : baseEnd_6534367 < baseStart_6534367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534381 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6534381 : Nat := 118140960795 + 6534381 * 2 ^ 59
def prefixEnd_6534381 : Nat := 4983230072969 + 3 ^ 40 * 6534381 * 2
def baseEnd_6534381 : Nat := 3355278232606903937986435

theorem tailTrace_6534381 : CollatzResearch.WordTrace tailWord_6534381 prefixEnd_6534381 3355278232606903937986435 := by
  unfold tailWord_6534381
  simp only [CollatzResearch.WordTrace]
  refine ⟨238328454540061095271930997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158885636360040730181287331 238328454540061095271930997)
  ·
    refine ⟨22343292613130727681743531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238328454540061095271930997 22343292613130727681743531)
    ·
      refine ⟨33514938919696091522615297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22343292613130727681743531 33514938919696091522615297)
      ·
        refine ⟨25136204189772068641961473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33514938919696091522615297 25136204189772068641961473)
        ·
          refine ⟨18852153142329051481471105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25136204189772068641961473 18852153142329051481471105)
          ·
            refine ⟨14139114856746788611103329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18852153142329051481471105 14139114856746788611103329)
            ·
              refine ⟨10604336142560091458327497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14139114856746788611103329 10604336142560091458327497)
              ·
                refine ⟨7953252106920068593745623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10604336142560091458327497 7953252106920068593745623)
                ·
                  refine ⟨11929878160380102890618435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953252106920068593745623 11929878160380102890618435)
                  ·
                    refine ⟨17894817240570154335927653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11929878160380102890618435 17894817240570154335927653)
                    ·
                      refine ⟨3355278232606903937986435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17894817240570154335927653 3355278232606903937986435)
                      ·
                        rfl

theorem cell23_6534381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6534381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534381 prefixEnd_6534381 := by exact prefixLift 6534381
  have htrace : WordTrace (prefixWord ++ tailWord_6534381) baseStart_6534381 baseEnd_6534381 := by
    simpa [prefixWord, tailWord_6534381, baseEnd_6534381] using wordTrace_append hprefix tailTrace_6534381
  have hstable : (prefixWord ++ tailWord_6534381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534381).length < 2 ^ (prefixWord ++ tailWord_6534381).sum := by decide
  have hdescent : baseEnd_6534381 < baseStart_6534381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534387 : List Nat := [1, 1, 1, 2, 2, 5, 4, 7]
def baseStart_6534387 : Nat := 118140960795 + 6534387 * 2 ^ 59
def prefixEnd_6534387 : Nat := 4983230072969 + 3 ^ 40 * 6534387 * 2
def baseEnd_6534387 : Nat := 124269678277438182018941

theorem tailTrace_6534387 : CollatzResearch.WordTrace tailWord_6534387 prefixEnd_6534387 124269678277438182018941 := by
  unfold tailWord_6534387
  simp only [CollatzResearch.WordTrace]
  refine ⟨238328673378039358296649415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158885782252026238864432943 238328673378039358296649415)
  ·
    refine ⟨357493010067059037444974123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238328673378039358296649415 357493010067059037444974123)
    ·
      refine ⟨536239515100588556167461185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357493010067059037444974123 536239515100588556167461185)
      ·
        refine ⟨402179636325441417125595889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536239515100588556167461185 402179636325441417125595889)
        ·
          refine ⟨301634727244081062844196917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402179636325441417125595889 301634727244081062844196917)
          ·
            refine ⟨28278255679132599641643461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301634727244081062844196917 28278255679132599641643461)
            ·
              refine ⟨5302172939837362432808149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28278255679132599641643461 5302172939837362432808149)
              ·
                refine ⟨124269678277438182018941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5302172939837362432808149 124269678277438182018941)
                ·
                  rfl

theorem cell23_6534387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 7].length) (baseStart_6534387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534387 prefixEnd_6534387 := by exact prefixLift 6534387
  have htrace : WordTrace (prefixWord ++ tailWord_6534387) baseStart_6534387 baseEnd_6534387 := by
    simpa [prefixWord, tailWord_6534387, baseEnd_6534387] using wordTrace_append hprefix tailTrace_6534387
  have hstable : (prefixWord ++ tailWord_6534387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534387).length < 2 ^ (prefixWord ++ tailWord_6534387).sum := by decide
  have hdescent : baseEnd_6534387 < baseStart_6534387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534400 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_6534400 : Nat := 118140960795 + 6534400 * 2 ^ 59
def prefixEnd_6534400 : Nat := 4983230072969 + 3 ^ 40 * 6534400 * 2
def baseEnd_6534400 : Nat := 1118429329579779787882949

theorem tailTrace_6534400 : CollatzResearch.WordTrace tailWord_6534400 prefixEnd_6534400 1118429329579779787882949 := by
  unfold tailWord_6534400
  simp only [CollatzResearch.WordTrace]
  refine ⟨119164573763496130758436327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158886098351328174344581769 119164573763496130758436327)
  ·
    refine ⟨178746860645244196137654491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119164573763496130758436327 178746860645244196137654491)
    ·
      refine ⟨268120290967866294206481737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178746860645244196137654491 268120290967866294206481737)
      ·
        refine ⟨201090218225899720654861303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268120290967866294206481737 201090218225899720654861303)
        ·
          refine ⟨301635327338849580982291955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201090218225899720654861303 301635327338849580982291955)
          ·
            refine ⟨452452991008274371473437933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301635327338849580982291955 452452991008274371473437933)
            ·
              refine ⟨169669871628102889302539225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452452991008274371473437933 169669871628102889302539225)
              ·
                refine ⟨127252403721077166976904419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169669871628102889302539225 127252403721077166976904419)
                ·
                  refine ⟨190878605581615750465356629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127252403721077166976904419 190878605581615750465356629)
                  ·
                    refine ⟨1118429329579779787882949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190878605581615750465356629 1118429329579779787882949)
                    ·
                      rfl

theorem cell23_6534400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_6534400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534400 prefixEnd_6534400 := by exact prefixLift 6534400
  have htrace : WordTrace (prefixWord ++ tailWord_6534400) baseStart_6534400 baseEnd_6534400 := by
    simpa [prefixWord, tailWord_6534400, baseEnd_6534400] using wordTrace_append hprefix tailTrace_6534400
  have hstable : (prefixWord ++ tailWord_6534400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534400).length < 2 ^ (prefixWord ++ tailWord_6534400).sum := by decide
  have hdescent : baseEnd_6534400 < baseStart_6534400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534458 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2]
def baseStart_6534458 : Nat := 118140960795 + 6534458 * 2 ^ 59
def prefixEnd_6534458 : Nat := 4983230072969 + 3 ^ 40 * 6534458 * 2
def baseEnd_6534458 : Nat := 3355317770617300136723581

theorem tailTrace_6534458 : CollatzResearch.WordTrace tailWord_6534458 prefixEnd_6534458 3355317770617300136723581 := by
  unfold tailWord_6534458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59582815740195534355621007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158887508640521424948322685 59582815740195534355621007)
  ·
    refine ⟨89374223610293301533431511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59582815740195534355621007 89374223610293301533431511)
    ·
      refine ⟨134061335415439952300147267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89374223610293301533431511 134061335415439952300147267)
      ·
        refine ⟨201092003123159928450220901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134061335415439952300147267 201092003123159928450220901)
        ·
          refine ⟨37704750585592486584416419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201092003123159928450220901 37704750585592486584416419)
          ·
            refine ⟨56557125878388729876624629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37704750585592486584416419 56557125878388729876624629)
            ·
              refine ⟨5302230551098943425933559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56557125878388729876624629 5302230551098943425933559)
              ·
                refine ⟨7953345826648415138900339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302230551098943425933559 7953345826648415138900339)
                ·
                  refine ⟨11930018739972622708350509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953345826648415138900339 11930018739972622708350509)
                  ·
                    refine ⟨4473757027489733515631441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11930018739972622708350509 4473757027489733515631441)
                    ·
                      refine ⟨3355317770617300136723581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473757027489733515631441 3355317770617300136723581)
                      ·
                        rfl

theorem cell23_6534458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_6534458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534458 prefixEnd_6534458 := by exact prefixLift 6534458
  have htrace : WordTrace (prefixWord ++ tailWord_6534458) baseStart_6534458 baseEnd_6534458 := by
    simpa [prefixWord, tailWord_6534458, baseEnd_6534458] using wordTrace_append hprefix tailTrace_6534458
  have hstable : (prefixWord ++ tailWord_6534458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534458).length < 2 ^ (prefixWord ++ tailWord_6534458).sum := by decide
  have hdescent : baseEnd_6534458 < baseStart_6534458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534467 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_6534467 : Nat := 118140960795 + 6534467 * 2 ^ 59
def prefixEnd_6534467 : Nat := 4983230072969 + 3 ^ 40 * 6534467 * 2
def baseEnd_6534467 : Nat := 3355322391943190601511039

theorem tailTrace_6534467 : CollatzResearch.WordTrace tailWord_6534467 prefixEnd_6534467 3355322391943190601511039 := by
  unfold tailWord_6534467
  simp only [CollatzResearch.WordTrace]
  refine ⟨238331591217749531959561655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158887727478499687973041103 238331591217749531959561655)
  ·
    refine ⟨357497386826624297939342483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238331591217749531959561655 357497386826624297939342483)
    ·
      refine ⟨536246080239936446909013725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357497386826624297939342483 536246080239936446909013725)
      ·
        refine ⟨201092280089976167590880147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536246080239936446909013725 201092280089976167590880147)
        ·
          refine ⟨301638420134964251386320221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201092280089976167590880147 301638420134964251386320221)
          ·
            refine ⟨113114407550611594269870083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301638420134964251386320221 113114407550611594269870083)
            ·
              refine ⟨169671611325917391404805125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113114407550611594269870083 169671611325917391404805125)
              ·
                refine ⟨31813427123609510888400961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169671611325917391404805125 31813427123609510888400961)
                ·
                  refine ⟨23860070342707133166300721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31813427123609510888400961 23860070342707133166300721)
                  ·
                    refine ⟨17895052757030349874725541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23860070342707133166300721 17895052757030349874725541)
                    ·
                      refine ⟨3355322391943190601511039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17895052757030349874725541 3355322391943190601511039)
                      ·
                        rfl

theorem cell23_6534467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_6534467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534467 prefixEnd_6534467 := by exact prefixLift 6534467
  have htrace : WordTrace (prefixWord ++ tailWord_6534467) baseStart_6534467 baseEnd_6534467 := by
    simpa [prefixWord, tailWord_6534467, baseEnd_6534467] using wordTrace_append hprefix tailTrace_6534467
  have hstable : (prefixWord ++ tailWord_6534467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534467).length < 2 ^ (prefixWord ++ tailWord_6534467).sum := by decide
  have hdescent : baseEnd_6534467 < baseStart_6534467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534484 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6534484 : Nat := 118140960795 + 6534484 * 2 ^ 59
def prefixEnd_6534484 : Nat := 4983230072969 + 3 ^ 40 * 6534484 * 2
def baseEnd_6534484 : Nat := 3355331121114317034998461

theorem tailTrace_6534484 : CollatzResearch.WordTrace tailWord_6534484 prefixEnd_6534484 3355331121114317034998461 := by
  unfold tailWord_6534484
  simp only [CollatzResearch.WordTrace]
  refine ⟨119166105629343971931465253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158888140839125295908620337 119166105629343971931465253)
  ·
    refine ⟨22343644805501994737149735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119166105629343971931465253 22343644805501994737149735)
    ·
      refine ⟨33515467208252992105724603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22343644805501994737149735 33515467208252992105724603)
      ·
        refine ⟨50273200812379488158586905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33515467208252992105724603 50273200812379488158586905)
        ·
          refine ⟨37704900609284616118940179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50273200812379488158586905 37704900609284616118940179)
          ·
            refine ⟨56557350913926924178410269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37704900609284616118940179 56557350913926924178410269)
            ·
              refine ⟨21209006592722596566903851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56557350913926924178410269 21209006592722596566903851)
              ·
                refine ⟨31813509889083894850355777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21209006592722596566903851 31813509889083894850355777)
                ·
                  refine ⟨23860132416812921137766833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31813509889083894850355777 23860132416812921137766833)
                  ·
                    refine ⟨17895099312609690853325125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23860132416812921137766833 17895099312609690853325125)
                    ·
                      refine ⟨3355331121114317034998461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17895099312609690853325125 3355331121114317034998461)
                      ·
                        rfl

theorem cell23_6534484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6534484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534484 prefixEnd_6534484 := by exact prefixLift 6534484
  have htrace : WordTrace (prefixWord ++ tailWord_6534484) baseStart_6534484 baseEnd_6534484 := by
    simpa [prefixWord, tailWord_6534484, baseEnd_6534484] using wordTrace_append hprefix tailTrace_6534484
  have hstable : (prefixWord ++ tailWord_6534484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534484).length < 2 ^ (prefixWord ++ tailWord_6534484).sum := by decide
  have hdescent : baseEnd_6534484 < baseStart_6534484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534527 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_6534527 : Nat := 118140960795 + 6534527 * 2 ^ 59
def prefixEnd_6534527 : Nat := 4983230072969 + 3 ^ 40 * 6534527 * 2
def baseEnd_6534527 : Nat := 3355353200782460366760763

theorem tailTrace_6534527 : CollatzResearch.WordTrace tailWord_6534527 prefixEnd_6534527 3355353200782460366760763 := by
  unfold tailWord_6534527
  simp only [CollatzResearch.WordTrace]
  refine ⟨238333779597532162206745835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158889186398354774804497223 238333779597532162206745835)
  ·
    refine ⟨357500669396298243310118753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238333779597532162206745835 357500669396298243310118753)
    ·
      refine ⟨268125502047223682482589065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357500669396298243310118753 268125502047223682482589065)
      ·
        refine ⟨201094126535417761861941799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268125502047223682482589065 201094126535417761861941799)
        ·
          refine ⟨301641189803126642792912699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201094126535417761861941799 301641189803126642792912699)
          ·
            refine ⟨452461784704689964189369049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301641189803126642792912699 452461784704689964189369049)
            ·
              refine ⟨339346338528517473142026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452461784704689964189369049 339346338528517473142026787)
              ·
                refine ⟨509019507792776209713040181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339346338528517473142026787 509019507792776209713040181)
                ·
                  refine ⟨47720578855572769660597517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509019507792776209713040181 47720578855572769660597517)
                  ·
                    refine ⟨17895217070839788622724069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47720578855572769660597517 17895217070839788622724069)
                    ·
                      refine ⟨3355353200782460366760763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17895217070839788622724069 3355353200782460366760763)
                      ·
                        rfl

theorem cell23_6534527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_6534527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534527 prefixEnd_6534527 := by exact prefixLift 6534527
  have htrace : WordTrace (prefixWord ++ tailWord_6534527) baseStart_6534527 baseEnd_6534527 := by
    simpa [prefixWord, tailWord_6534527, baseEnd_6534527] using wordTrace_append hprefix tailTrace_6534527
  have hstable : (prefixWord ++ tailWord_6534527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534527).length < 2 ^ (prefixWord ++ tailWord_6534527).sum := by decide
  have hdescent : baseEnd_6534527 < baseStart_6534527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534581 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6534581 : Nat := 118140960795 + 6534581 * 2 ^ 59
def prefixEnd_6534581 : Nat := 4983230072969 + 3 ^ 40 * 6534581 * 2
def baseEnd_6534581 : Nat := 3355380928737803155485515

theorem tailTrace_6534581 : CollatzResearch.WordTrace tailWord_6534581 prefixEnd_6534581 3355380928737803155485515 := by
  unfold tailWord_6534581
  simp only [CollatzResearch.WordTrace]
  refine ⟨238335749139336529429211597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158890499426224352952807731 238335749139336529429211597)
  ·
    refine ⟨89375905927251198535954349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238335749139336529429211597 89375905927251198535954349)
    ·
      refine ⟨33515964722719199450982881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89375905927251198535954349 33515964722719199450982881)
      ·
        refine ⟨25136973542039399588237161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33515964722719199450982881 25136973542039399588237161)
        ·
          refine ⟨18852730156529549691177871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25136973542039399588237161 18852730156529549691177871)
          ·
            refine ⟨28279095234794324536766807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18852730156529549691177871 28279095234794324536766807)
            ·
              refine ⟨42418642852191486805150211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28279095234794324536766807 42418642852191486805150211)
              ·
                refine ⟨63627964278287230207725317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42418642852191486805150211 63627964278287230207725317)
                ·
                  refine ⟨11930243302178855663948497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63627964278287230207725317 11930243302178855663948497)
                  ·
                    refine ⟨8947682476634141747961373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11930243302178855663948497 8947682476634141747961373)
                    ·
                      refine ⟨3355380928737803155485515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8947682476634141747961373 3355380928737803155485515)
                      ·
                        rfl

theorem cell23_6534581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6534581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534581 prefixEnd_6534581 := by exact prefixLift 6534581
  have htrace : WordTrace (prefixWord ++ tailWord_6534581) baseStart_6534581 baseEnd_6534581 := by
    simpa [prefixWord, tailWord_6534581, baseEnd_6534581] using wordTrace_append hprefix tailTrace_6534581
  have hstable : (prefixWord ++ tailWord_6534581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534581).length < 2 ^ (prefixWord ++ tailWord_6534581).sum := by decide
  have hdescent : baseEnd_6534581 < baseStart_6534581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534638 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_6534638 : Nat := 118140960795 + 6534638 * 2 ^ 59
def prefixEnd_6534638 : Nat := 4983230072969 + 3 ^ 40 * 6534638 * 2
def baseEnd_6534638 : Nat := 3355410197135109432472753

theorem tailTrace_6534638 : CollatzResearch.WordTrace tailWord_6534638 prefixEnd_6534638 3355410197135109432472753 := by
  unfold tailWord_6534638
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792228512516253520504571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158891885400086685442691045 29792228512516253520504571)
  ·
    refine ⟨44688342768774380280756857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29792228512516253520504571 44688342768774380280756857)
    ·
      refine ⟨33516257076580785210567643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44688342768774380280756857 33516257076580785210567643)
      ·
        refine ⟨50274385614871177815851465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33516257076580785210567643 50274385614871177815851465)
        ·
          refine ⟨37705789211153383361888599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50274385614871177815851465 37705789211153383361888599)
          ·
            refine ⟨56558683816730075042832899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37705789211153383361888599 56558683816730075042832899)
            ·
              refine ⟨84838025725095112564249349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56558683816730075042832899 84838025725095112564249349)
              ·
                refine ⟨15907129823455333605796753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84838025725095112564249349 15907129823455333605796753)
                ·
                  refine ⟨11930347367591500204347565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15907129823455333605796753 11930347367591500204347565)
                  ·
                    refine ⟨4473880262846812576630337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11930347367591500204347565 4473880262846812576630337)
                    ·
                      refine ⟨3355410197135109432472753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473880262846812576630337 3355410197135109432472753)
                      ·
                        rfl

theorem cell23_6534638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_6534638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534638 prefixEnd_6534638 := by exact prefixLift 6534638
  have htrace : WordTrace (prefixWord ++ tailWord_6534638) baseStart_6534638 baseEnd_6534638 := by
    simpa [prefixWord, tailWord_6534638, baseEnd_6534638] using wordTrace_append hprefix tailTrace_6534638
  have hstable : (prefixWord ++ tailWord_6534638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534638).length < 2 ^ (prefixWord ++ tailWord_6534638).sum := by decide
  have hdescent : baseEnd_6534638 < baseStart_6534638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534664 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6534664 : Nat := 118140960795 + 6534664 * 2 ^ 59
def prefixEnd_6534664 : Nat := 4983230072969 + 3 ^ 40 * 6534664 * 2
def baseEnd_6534664 : Nat := 3355423547632126330747633

theorem tailTrace_6534664 : CollatzResearch.WordTrace tailWord_6534664 prefixEnd_6534664 3355423547632126330747633 := by
  unfold tailWord_6534664
  simp only [CollatzResearch.WordTrace]
  refine ⟨119169388199017917302241523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158892517598690556402988697 119169388199017917302241523)
  ·
    refine ⟨178754082298526875953362285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119169388199017917302241523 178754082298526875953362285)
    ·
      refine ⟨67032780861947578482510857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178754082298526875953362285 67032780861947578482510857)
      ·
        refine ⟨50274585646460683861883143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67032780861947578482510857 50274585646460683861883143)
        ·
          refine ⟨75411878469691025792824715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50274585646460683861883143 75411878469691025792824715)
          ·
            refine ⟨113117817704536538689237073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75411878469691025792824715 113117817704536538689237073)
            ·
              refine ⟨84838363278402404016927805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113117817704536538689237073 84838363278402404016927805)
              ·
                refine ⟨31814386229400901506347927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84838363278402404016927805 31814386229400901506347927)
                ·
                  refine ⟨47721579344101352259521891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31814386229400901506347927 47721579344101352259521891)
                  ·
                    refine ⟨71582369016152028389282837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47721579344101352259521891 71582369016152028389282837)
                    ·
                      refine ⟨3355423547632126330747633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71582369016152028389282837 3355423547632126330747633)
                      ·
                        rfl

theorem cell23_6534664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6534664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534664 prefixEnd_6534664 := by exact prefixLift 6534664
  have htrace : WordTrace (prefixWord ++ tailWord_6534664) baseStart_6534664 baseEnd_6534664 := by
    simpa [prefixWord, tailWord_6534664, baseEnd_6534664] using wordTrace_append hprefix tailTrace_6534664
  have hstable : (prefixWord ++ tailWord_6534664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534664).length < 2 ^ (prefixWord ++ tailWord_6534664).sum := by decide
  have hdescent : baseEnd_6534664 < baseStart_6534664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534702 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6534702 : Nat := 118140960795 + 6534702 * 2 ^ 59
def prefixEnd_6534702 : Nat := 4983230072969 + 3 ^ 40 * 6534702 * 2
def baseEnd_6534702 : Nat := 3355443059896997182072459

theorem tailTrace_6534702 : CollatzResearch.WordTrace tailWord_6534702 prefixEnd_6534702 3355443059896997182072459 := by
  unfold tailWord_6534702
  simp only [CollatzResearch.WordTrace]
  refine ⟨29792520296487270886795795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158893441581265444729577573 29792520296487270886795795)
  ·
    refine ⟨44688780444730906330193693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29792520296487270886795795 44688780444730906330193693)
    ·
      refine ⟨16758292666774089873822635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44688780444730906330193693 16758292666774089873822635)
      ·
        refine ⟨25137439000161134810733953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16758292666774089873822635 25137439000161134810733953)
        ·
          refine ⟨18853079250120851108050465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25137439000161134810733953 18853079250120851108050465)
          ·
            refine ⟨14139809437590638331037849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18853079250120851108050465 14139809437590638331037849)
            ·
              refine ⟨10604857078192978748278387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14139809437590638331037849 10604857078192978748278387)
              ·
                refine ⟨15907285617289468122417581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604857078192978748278387 15907285617289468122417581)
                ·
                  refine ⟨5965232106483550545906593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15907285617289468122417581 5965232106483550545906593)
                  ·
                    refine ⟨4473924079862662909429945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965232106483550545906593 4473924079862662909429945)
                    ·
                      refine ⟨3355443059896997182072459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473924079862662909429945 3355443059896997182072459)
                      ·
                        rfl

theorem cell23_6534702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6534702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534702 prefixEnd_6534702 := by exact prefixLift 6534702
  have htrace : WordTrace (prefixWord ++ tailWord_6534702) baseStart_6534702 baseEnd_6534702 := by
    simpa [prefixWord, tailWord_6534702, baseEnd_6534702] using wordTrace_append hprefix tailTrace_6534702
  have hstable : (prefixWord ++ tailWord_6534702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534702).length < 2 ^ (prefixWord ++ tailWord_6534702).sum := by decide
  have hdescent : baseEnd_6534702 < baseStart_6534702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534742 : List Nat := [5, 2, 2, 2, 2, 1, 9]
def baseStart_6534742 : Nat := 118140960795 + 6534742 * 2 ^ 59
def prefixEnd_6534742 : Nat := 4983230072969 + 3 ^ 40 * 6534742 * 2
def baseEnd_6534742 : Nat := 41425476532384901550275

theorem tailTrace_6534742 : CollatzResearch.WordTrace tailWord_6534742 prefixEnd_6534742 41425476532384901550275 := by
  unfold tailWord_6534742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896351330734578370363905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158894414194502169283881653 14896351330734578370363905)
  ·
    refine ⟨11172263498050933777772929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14896351330734578370363905 11172263498050933777772929)
    ·
      refine ⟨8379197623538200333329697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11172263498050933777772929 8379197623538200333329697)
      ·
        refine ⟨6284398217653650249997273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8379197623538200333329697 6284398217653650249997273)
        ·
          refine ⟨4713298663240237687497955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6284398217653650249997273 4713298663240237687497955)
          ·
            refine ⟨7069947994860356531246933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713298663240237687497955 7069947994860356531246933)
            ·
              refine ⟨41425476532384901550275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7069947994860356531246933 41425476532384901550275)
              ·
                rfl

theorem cell23_6534742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 9].length) (baseStart_6534742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534742 prefixEnd_6534742 := by exact prefixLift 6534742
  have htrace : WordTrace (prefixWord ++ tailWord_6534742) baseStart_6534742 baseEnd_6534742 := by
    simpa [prefixWord, tailWord_6534742, baseEnd_6534742] using wordTrace_append hprefix tailTrace_6534742
  have hstable : (prefixWord ++ tailWord_6534742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534742).length < 2 ^ (prefixWord ++ tailWord_6534742).sum := by decide
  have hdescent : baseEnd_6534742 < baseStart_6534742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534792 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6534792 : Nat := 118140960795 + 6534792 * 2 ^ 59
def prefixEnd_6534792 : Nat := 4983230072969 + 3 ^ 40 * 6534792 * 2
def baseEnd_6534792 : Nat := 3355489273155901829947045

theorem tailTrace_6534792 : CollatzResearch.WordTrace tailWord_6534792 prefixEnd_6534792 3355489273155901829947045 := by
  unfold tailWord_6534792
  simp only [CollatzResearch.WordTrace]
  refine ⟨119171722470786056232571315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158895629961048074976761753 119171722470786056232571315)
  ·
    refine ⟨178757583706179084348856973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119171722470786056232571315 178757583706179084348856973)
    ·
      refine ⟨67034093889817156630821365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178757583706179084348856973 67034093889817156630821365)
      ·
        refine ⟨6284446302170358434139503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67034093889817156630821365 6284446302170358434139503)
        ·
          refine ⟨9426669453255537651209255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284446302170358434139503 9426669453255537651209255)
          ·
            refine ⟨14140004179883306476813883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9426669453255537651209255 14140004179883306476813883)
            ·
              refine ⟨21210006269824959715220825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14140004179883306476813883 21210006269824959715220825)
              ·
                refine ⟨15907504702368719786415619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21210006269824959715220825 15907504702368719786415619)
                ·
                  refine ⟨23861257053553079679623429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15907504702368719786415619 23861257053553079679623429)
                  ·
                    refine ⟨4473985697541202439929393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23861257053553079679623429 4473985697541202439929393)
                    ·
                      refine ⟨3355489273155901829947045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4473985697541202439929393 3355489273155901829947045)
                      ·
                        rfl

theorem cell23_6534792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6534792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534792 prefixEnd_6534792 := by exact prefixLift 6534792
  have htrace : WordTrace (prefixWord ++ tailWord_6534792) baseStart_6534792 baseEnd_6534792 := by
    simpa [prefixWord, tailWord_6534792, baseEnd_6534792] using wordTrace_append hprefix tailTrace_6534792
  have hstable : (prefixWord ++ tailWord_6534792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534792).length < 2 ^ (prefixWord ++ tailWord_6534792).sum := by decide
  have hdescent : baseEnd_6534792 < baseStart_6534792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534821 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_6534821 : Nat := 118140960795 + 6534821 * 2 ^ 59
def prefixEnd_6534821 : Nat := 4983230072969 + 3 ^ 40 * 6534821 * 2
def baseEnd_6534821 : Nat := 3355504164094882216484411

theorem tailTrace_6534821 : CollatzResearch.WordTrace tailWord_6534821 prefixEnd_6534821 3355504164094882216484411 := by
  unfold tailWord_6534821
  simp only [CollatzResearch.WordTrace]
  refine ⟨238344502658467050417948317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158896335105644700278632211 238344502658467050417948317)
  ·
    refine ⟨89379188496925143906730619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238344502658467050417948317 89379188496925143906730619)
    ·
      refine ⟨134068782745387715860095929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89379188496925143906730619 134068782745387715860095929)
      ·
        refine ⟨100551587059040786895071947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134068782745387715860095929 100551587059040786895071947)
        ·
          refine ⟨150827380588561180342607921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100551587059040786895071947 150827380588561180342607921)
          ·
            refine ⟨113120535441420885256955941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150827380588561180342607921 113120535441420885256955941)
            ·
              refine ⟨21210100395266415985679239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113120535441420885256955941 21210100395266415985679239)
              ·
                refine ⟨31815150592899623978518859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21210100395266415985679239 31815150592899623978518859)
                ·
                  refine ⟨47722725889349435967778289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31815150592899623978518859 47722725889349435967778289)
                  ·
                    refine ⟨35792044417012076975833717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47722725889349435967778289 35792044417012076975833717)
                    ·
                      refine ⟨3355504164094882216484411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35792044417012076975833717 3355504164094882216484411)
                      ·
                        rfl

theorem cell23_6534821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_6534821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534821 prefixEnd_6534821 := by exact prefixLift 6534821
  have htrace : WordTrace (prefixWord ++ tailWord_6534821) baseStart_6534821 baseEnd_6534821 := by
    simpa [prefixWord, tailWord_6534821, baseEnd_6534821] using wordTrace_append hprefix tailTrace_6534821
  have hstable : (prefixWord ++ tailWord_6534821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534821).length < 2 ^ (prefixWord ++ tailWord_6534821).sum := by decide
  have hdescent : baseEnd_6534821 < baseStart_6534821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534831 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_6534831 : Nat := 118140960795 + 6534831 * 2 ^ 59
def prefixEnd_6534831 : Nat := 4983230072969 + 3 ^ 40 * 6534831 * 2
def baseEnd_6534831 : Nat := 3355509298901427177359365

theorem tailTrace_6534831 : CollatzResearch.WordTrace tailWord_6534831 prefixEnd_6534831 3355509298901427177359365 := by
  unfold tailWord_6534831
  simp only [CollatzResearch.WordTrace]
  refine ⟨238344867388430822125812347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158896578258953881417208231 238344867388430822125812347)
  ·
    refine ⟨357517301082646233188718521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238344867388430822125812347 357517301082646233188718521)
    ·
      refine ⟨268137975811984674891538891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357517301082646233188718521 268137975811984674891538891)
      ·
        refine ⟨402206963717977012337308337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268137975811984674891538891 402206963717977012337308337)
        ·
          refine ⟨301655222788482759252981253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402206963717977012337308337 301655222788482759252981253)
          ·
            refine ⟨56560354272840517359933985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301655222788482759252981253 56560354272840517359933985)
            ·
              refine ⟨42420265704630388019950489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56560354272840517359933985 42420265704630388019950489)
              ·
                refine ⟨31815199278472791014962867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42420265704630388019950489 31815199278472791014962867)
                ·
                  refine ⟨47722798917709186522444301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31815199278472791014962867 47722798917709186522444301)
                  ·
                    refine ⟨17896049594140944945916613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47722798917709186522444301 17896049594140944945916613)
                    ·
                      refine ⟨3355509298901427177359365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17896049594140944945916613 3355509298901427177359365)
                      ·
                        rfl

theorem cell23_6534831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_6534831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534831 prefixEnd_6534831 := by exact prefixLift 6534831
  have htrace : WordTrace (prefixWord ++ tailWord_6534831) baseStart_6534831 baseEnd_6534831 := by
    simpa [prefixWord, tailWord_6534831, baseEnd_6534831] using wordTrace_append hprefix tailTrace_6534831
  have hstable : (prefixWord ++ tailWord_6534831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534831).length < 2 ^ (prefixWord ++ tailWord_6534831).sum := by decide
  have hdescent : baseEnd_6534831 < baseStart_6534831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534848 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2]
def baseStart_6534848 : Nat := 118140960795 + 6534848 * 2 ^ 59
def prefixEnd_6534848 : Nat := 4983230072969 + 3 ^ 40 * 6534848 * 2
def baseEnd_6534848 : Nat := 3355518028072553610846787

theorem tailTrace_6534848 : CollatzResearch.WordTrace tailWord_6534848 prefixEnd_6534848 3355518028072553610846787 := by
  unfold tailWord_6534848
  simp only [CollatzResearch.WordTrace]
  refine ⟨119172743714684617014590599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158896991619579489352787465 119172743714684617014590599)
  ·
    refine ⟨178759115572026925521885899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119172743714684617014590599 178759115572026925521885899)
    ·
      refine ⟨268138673358040388282828849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178759115572026925521885899 268138673358040388282828849)
      ·
        refine ⟨201104005018530291212121637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268138673358040388282828849 201104005018530291212121637)
        ·
          refine ⟨37707000940974429602272807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201104005018530291212121637 37707000940974429602272807)
          ·
            refine ⟨56560501411461644403409211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37707000940974429602272807 56560501411461644403409211)
            ·
              refine ⟨84840752117192466605113817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56560501411461644403409211 84840752117192466605113817)
              ·
                refine ⟨63630564087894349953835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84840752117192466605113817 63630564087894349953835363)
                ·
                  refine ⟨95445846131841524930753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63630564087894349953835363 95445846131841524930753045)
                  ·
                    refine ⟨4474024037430071481129049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95445846131841524930753045 4474024037430071481129049)
                    ·
                      refine ⟨3355518028072553610846787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474024037430071481129049 3355518028072553610846787)
                      ·
                        rfl

theorem cell23_6534848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_6534848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534848 prefixEnd_6534848 := by exact prefixLift 6534848
  have htrace : WordTrace (prefixWord ++ tailWord_6534848) baseStart_6534848 baseEnd_6534848 := by
    simpa [prefixWord, tailWord_6534848, baseEnd_6534848] using wordTrace_append hprefix tailTrace_6534848
  have hstable : (prefixWord ++ tailWord_6534848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534848).length < 2 ^ (prefixWord ++ tailWord_6534848).sum := by decide
  have hdescent : baseEnd_6534848 < baseStart_6534848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534871 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 8]
def baseStart_6534871 : Nat := 118140960795 + 6534871 * 2 ^ 59
def prefixEnd_6534871 : Nat := 4983230072969 + 3 ^ 40 * 6534871 * 2
def baseEnd_6534871 : Nat := 372836648680845224539909

theorem tailTrace_6534871 : CollatzResearch.WordTrace tailWord_6534871 prefixEnd_6534871 372836648680845224539909 := by
  unfold tailWord_6534871
  simp only [CollatzResearch.WordTrace]
  refine ⟨238346326308285908957268467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158897550872190605971512311 238346326308285908957268467)
  ·
    refine ⟨357519489462428863435902701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238346326308285908957268467 357519489462428863435902701)
    ·
      refine ⟨134069808548410823788463513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357519489462428863435902701 134069808548410823788463513)
      ·
        refine ⟨100552356411308117841347635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134069808548410823788463513 100552356411308117841347635)
        ·
          refine ⟨150828534616962176762021453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100552356411308117841347635 150828534616962176762021453)
          ·
            refine ⟨56560700481360816285758045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150828534616962176762021453 56560700481360816285758045)
            ·
              refine ⟨21210262680510306107159267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56560700481360816285758045 21210262680510306107159267)
              ·
                refine ⟨31815394020765459160738901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21210262680510306107159267 31815394020765459160738901)
                ·
                  refine ⟨372836648680845224539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31815394020765459160738901 372836648680845224539909)
                  ·
                    rfl

theorem cell23_6534871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 8].length) (baseStart_6534871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534871 prefixEnd_6534871 := by exact prefixLift 6534871
  have htrace : WordTrace (prefixWord ++ tailWord_6534871) baseStart_6534871 baseEnd_6534871 := by
    simpa [prefixWord, tailWord_6534871, baseEnd_6534871] using wordTrace_append hprefix tailTrace_6534871
  have hstable : (prefixWord ++ tailWord_6534871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534871).length < 2 ^ (prefixWord ++ tailWord_6534871).sum := by decide
  have hdescent : baseEnd_6534871 < baseStart_6534871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534898 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6534898 : Nat := 118140960795 + 6534898 * 2 ^ 59
def prefixEnd_6534898 : Nat := 4983230072969 + 3 ^ 40 * 6534898 * 2
def baseEnd_6534898 : Nat := 3355543702105278415221557

theorem tailTrace_6534898 : CollatzResearch.WordTrace tailWord_6534898 prefixEnd_6534898 3355543702105278415221557 := by
  unfold tailWord_6534898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59586827769797023142125337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158898207386125395045667565 59586827769797023142125337)
  ·
    refine ⟨44690120827347767356594003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59586827769797023142125337 44690120827347767356594003)
    ·
      refine ⟨67035181241021651034891005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44690120827347767356594003 67035181241021651034891005)
      ·
        refine ⟨25138192965383119138084127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67035181241021651034891005 25138192965383119138084127)
        ·
          refine ⟨37707289448074678707126191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25138192965383119138084127 37707289448074678707126191)
          ·
            refine ⟨56560934172112018060689287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37707289448074678707126191 56560934172112018060689287)
            ·
              refine ⟨84841401258168027091033931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56560934172112018060689287 84841401258168027091033931)
              ·
                refine ⟨127262101887252040636550897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84841401258168027091033931 127262101887252040636550897)
                ·
                  refine ⟨95446576415439030477413173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127262101887252040636550897 95446576415439030477413173)
                  ·
                    refine ⟨8948116538947409107257485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95446576415439030477413173 8948116538947409107257485)
                    ·
                      refine ⟨3355543702105278415221557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948116538947409107257485 3355543702105278415221557)
                      ·
                        rfl

theorem cell23_6534898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6534898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534898 prefixEnd_6534898 := by exact prefixLift 6534898
  have htrace : WordTrace (prefixWord ++ tailWord_6534898) baseStart_6534898 baseEnd_6534898 := by
    simpa [prefixWord, tailWord_6534898, baseEnd_6534898] using wordTrace_append hprefix tailTrace_6534898
  have hstable : (prefixWord ++ tailWord_6534898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534898).length < 2 ^ (prefixWord ++ tailWord_6534898).sum := by decide
  have hdescent : baseEnd_6534898 < baseStart_6534898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534931 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 6]
def baseStart_6534931 : Nat := 118140960795 + 6534931 * 2 ^ 59
def prefixEnd_6534931 : Nat := 4983230072969 + 3 ^ 40 * 6534931 * 2
def baseEnd_6534931 : Nat := 1118520215655625595369635

theorem tailTrace_6534931 : CollatzResearch.WordTrace tailWord_6534931 prefixEnd_6534931 1118520215655625595369635 := by
  unfold tailWord_6534931
  simp only [CollatzResearch.WordTrace]
  refine ⟨238348514688068539204452647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158899009792045692802968431 238348514688068539204452647)
  ·
    refine ⟨357522772032102808806678971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238348514688068539204452647 357522772032102808806678971)
    ·
      refine ⟨536284158048154213210018457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357522772032102808806678971 536284158048154213210018457)
      ·
        refine ⟨402213118536115659907513843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536284158048154213210018457 402213118536115659907513843)
        ·
          refine ⟨603319677804173489861270765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402213118536115659907513843 603319677804173489861270765)
          ·
            refine ⟨226244879176565058697976537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603319677804173489861270765 226244879176565058697976537)
            ·
              refine ⟨169683659382423794023482403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226244879176565058697976537 169683659382423794023482403)
              ·
                refine ⟨254525489073635691035223605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169683659382423794023482403 254525489073635691035223605)
                ·
                  refine ⟨23861764600653346034552213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254525489073635691035223605 23861764600653346034552213)
                  ·
                    refine ⟨1118520215655625595369635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23861764600653346034552213 1118520215655625595369635)
                    ·
                      rfl

theorem cell23_6534931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_6534931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534931 prefixEnd_6534931 := by exact prefixLift 6534931
  have htrace : WordTrace (prefixWord ++ tailWord_6534931) baseStart_6534931 baseEnd_6534931 := by
    simpa [prefixWord, tailWord_6534931, baseEnd_6534931] using wordTrace_append hprefix tailTrace_6534931
  have hstable : (prefixWord ++ tailWord_6534931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534931).length < 2 ^ (prefixWord ++ tailWord_6534931).sum := by decide
  have hdescent : baseEnd_6534931 < baseStart_6534931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534952 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6534952 : Nat := 118140960795 + 6534952 * 2 ^ 59
def prefixEnd_6534952 : Nat := 4983230072969 + 3 ^ 40 * 6534952 * 2
def baseEnd_6534952 : Nat := 1118523810020207067982103

theorem tailTrace_6534952 : CollatzResearch.WordTrace tailWord_6534952 prefixEnd_6534952 1118523810020207067982103 := by
  unfold tailWord_6534952
  simp only [CollatzResearch.WordTrace]
  refine ⟨119174640310496229895483555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158899520413994973193978073 119174640310496229895483555)
  ·
    refine ⟨178761960465744344843225333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119174640310496229895483555 178761960465744344843225333)
    ·
      refine ⟨16758933793663532329052375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178761960465744344843225333 16758933793663532329052375)
      ·
        refine ⟨25138400690495298493578563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16758933793663532329052375 25138400690495298493578563)
        ·
          refine ⟨37707601035742947740367845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25138400690495298493578563 37707601035742947740367845)
          ·
            refine ⟨7070175194201802701318971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37707601035742947740367845 7070175194201802701318971)
            ·
              refine ⟨10605262791302704051978457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070175194201802701318971 10605262791302704051978457)
              ·
                refine ⟨7953947093477028038983843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10605262791302704051978457 7953947093477028038983843)
                ·
                  refine ⟨11930920640215542058475765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953947093477028038983843 11930920640215542058475765)
                  ·
                    refine ⟨1118523810020207067982103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11930920640215542058475765 1118523810020207067982103)
                    ·
                      rfl

theorem cell23_6534952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6534952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534952 prefixEnd_6534952 := by exact prefixLift 6534952
  have htrace : WordTrace (prefixWord ++ tailWord_6534952) baseStart_6534952 baseEnd_6534952 := by
    simpa [prefixWord, tailWord_6534952, baseEnd_6534952] using wordTrace_append hprefix tailTrace_6534952
  have hstable : (prefixWord ++ tailWord_6534952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534952).length < 2 ^ (prefixWord ++ tailWord_6534952).sum := by decide
  have hdescent : baseEnd_6534952 < baseStart_6534952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534965 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6534965 : Nat := 118140960795 + 6534965 * 2 ^ 59
def prefixEnd_6534965 : Nat := 4983230072969 + 3 ^ 40 * 6534965 * 2
def baseEnd_6534965 : Nat := 1118526035103043217694583

theorem tailTrace_6534965 : CollatzResearch.WordTrace tailWord_6534965 prefixEnd_6534965 1118526035103043217694583 := by
  unfold tailWord_6534965
  simp only [CollatzResearch.WordTrace]
  refine ⟨238349754769945363011190349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158899836513296908674126899 238349754769945363011190349)
  ·
    refine ⟨89381158038729511129196381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238349754769945363011190349 89381158038729511129196381)
    ·
      refine ⟨33517934264523566673448643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89381158038729511129196381 33517934264523566673448643)
      ·
        refine ⟨50276901396785350010172965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33517934264523566673448643 50276901396785350010172965)
        ·
          refine ⟨9426919011897253126907431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50276901396785350010172965 9426919011897253126907431)
          ·
            refine ⟨14140378517845879690361147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9426919011897253126907431 14140378517845879690361147)
            ·
              refine ⟨21210567776768819535541721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14140378517845879690361147 21210567776768819535541721)
              ·
                refine ⟨15907925832576614651656291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21210567776768819535541721 15907925832576614651656291)
                ·
                  refine ⟨23861888748864921977484437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15907925832576614651656291 23861888748864921977484437)
                  ·
                    refine ⟨1118526035103043217694583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23861888748864921977484437 1118526035103043217694583)
                    ·
                      rfl

theorem cell23_6534965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6534965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534965 prefixEnd_6534965 := by exact prefixLift 6534965
  have htrace : WordTrace (prefixWord ++ tailWord_6534965) baseStart_6534965 baseEnd_6534965 := by
    simpa [prefixWord, tailWord_6534965, baseEnd_6534965] using wordTrace_append hprefix tailTrace_6534965
  have hstable : (prefixWord ++ tailWord_6534965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534965).length < 2 ^ (prefixWord ++ tailWord_6534965).sum := by decide
  have hdescent : baseEnd_6534965 < baseStart_6534965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534968 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6534968 : Nat := 118140960795 + 6534968 * 2 ^ 59
def prefixEnd_6534968 : Nat := 4983230072969 + 3 ^ 40 * 6534968 * 2
def baseEnd_6534968 : Nat := 3355579645751093141346235

theorem tailTrace_6534968 : CollatzResearch.WordTrace tailWord_6534968 prefixEnd_6534968 3355579645751093141346235 := by
  unfold tailWord_6534968
  simp only [CollatzResearch.WordTrace]
  refine ⟨119174932094467247261774779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158899909459289663015699705 119174932094467247261774779)
  ·
    refine ⟨178762398141700870892662169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119174932094467247261774779 178762398141700870892662169)
    ·
      refine ⟨134071798606275653169496627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178762398141700870892662169 134071798606275653169496627)
      ·
        refine ⟨201107697909413479754244941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134071798606275653169496627 201107697909413479754244941)
        ·
          refine ⟨75415386716030054907841853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201107697909413479754244941 75415386716030054907841853)
          ·
            refine ⟨28280770018511270590440695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75415386716030054907841853 28280770018511270590440695)
            ·
              refine ⟨42421155027766905885661043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28280770018511270590440695 42421155027766905885661043)
              ·
                refine ⟨63631732541650358828491565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42421155027766905885661043 63631732541650358828491565)
                ·
                  refine ⟨23861899703118884560684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63631732541650358828491565 23861899703118884560684337)
                  ·
                    refine ⟨17896424777339163420513253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23861899703118884560684337 17896424777339163420513253)
                    ·
                      refine ⟨3355579645751093141346235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17896424777339163420513253 3355579645751093141346235)
                      ·
                        rfl

theorem cell23_6534968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6534968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534968 prefixEnd_6534968 := by exact prefixLift 6534968
  have htrace : WordTrace (prefixWord ++ tailWord_6534968) baseStart_6534968 baseEnd_6534968 := by
    simpa [prefixWord, tailWord_6534968, baseEnd_6534968] using wordTrace_append hprefix tailTrace_6534968
  have hstable : (prefixWord ++ tailWord_6534968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534968).length < 2 ^ (prefixWord ++ tailWord_6534968).sum := by decide
  have hdescent : baseEnd_6534968 < baseStart_6534968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6534969 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_6534969 : Nat := 118140960795 + 6534969 * 2 ^ 59
def prefixEnd_6534969 : Nat := 4983230072969 + 3 ^ 40 * 6534969 * 2
def baseEnd_6534969 : Nat := 1118526719743915879144577

theorem tailTrace_6534969 : CollatzResearch.WordTrace tailWord_6534969 prefixEnd_6534969 1118526719743915879144577 := by
  unfold tailWord_6534969
  simp only [CollatzResearch.WordTrace]
  refine ⟨238349900661930871694335961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158899933774620581129557307 238349900661930871694335961)
  ·
    refine ⟨178762425496448153770751971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238349900661930871694335961 178762425496448153770751971)
    ·
      refine ⟨268143638244672230656127957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178762425496448153770751971 268143638244672230656127957)
      ·
        refine ⟨6284616521359505406002999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 268143638244672230656127957 6284616521359505406002999)
        ·
          refine ⟨9426924782039258109004499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284616521359505406002999 9426924782039258109004499)
          ·
            refine ⟨14140387173058887163506749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9426924782039258109004499 14140387173058887163506749)
            ·
              refine ⟨5302645189897082686315031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14140387173058887163506749 5302645189897082686315031)
              ·
                refine ⟨7953967784845624029472547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302645189897082686315031 7953967784845624029472547)
                ·
                  refine ⟨11930951677268436044208821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7953967784845624029472547 11930951677268436044208821)
                  ·
                    refine ⟨1118526719743915879144577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11930951677268436044208821 1118526719743915879144577)
                    ·
                      rfl

theorem cell23_6534969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_6534969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6534969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6534969 prefixEnd_6534969 := by exact prefixLift 6534969
  have htrace : WordTrace (prefixWord ++ tailWord_6534969) baseStart_6534969 baseEnd_6534969 := by
    simpa [prefixWord, tailWord_6534969, baseEnd_6534969] using wordTrace_append hprefix tailTrace_6534969
  have hstable : (prefixWord ++ tailWord_6534969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6534969).length < 2 ^ (prefixWord ++ tailWord_6534969).sum := by decide
  have hdescent : baseEnd_6534969 < baseStart_6534969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6534969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535022 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6535022 : Nat := 118140960795 + 6535022 * 2 ^ 59
def prefixEnd_6535022 : Nat := 4983230072969 + 3 ^ 40 * 6535022 * 2
def baseEnd_6535022 : Nat := 3355607373706435930070987

theorem tailTrace_6535022 : CollatzResearch.WordTrace tailWord_6535022 prefixEnd_6535022 3355607373706435930070987 := by
  unfold tailWord_6535022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29793979216342357718251915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158901222487159241164010213 29793979216342357718251915)
  ·
    refine ⟨44690968824513536577377873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29793979216342357718251915 44690968824513536577377873)
    ·
      refine ⟨33518226618385152433033405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44690968824513536577377873 33518226618385152433033405)
      ·
        refine ⟨12569334981894432162387527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33518226618385152433033405 12569334981894432162387527)
        ·
          refine ⟨18854002472841648243581291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12569334981894432162387527 18854002472841648243581291)
          ·
            refine ⟨28281003709262472365371937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18854002472841648243581291 28281003709262472365371937)
            ·
              refine ⟨21210752781946854274028953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28281003709262472365371937 21210752781946854274028953)
              ·
                refine ⟨15908064586460140705521715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21210752781946854274028953 15908064586460140705521715)
                ·
                  refine ⟨23862096879690211058282573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15908064586460140705521715 23862096879690211058282573)
                  ·
                    refine ⟨8948286329883829146855965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23862096879690211058282573 8948286329883829146855965)
                    ·
                      refine ⟨3355607373706435930070987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948286329883829146855965 3355607373706435930070987)
                      ·
                        rfl

theorem cell23_6535022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6535022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535022 prefixEnd_6535022 := by exact prefixLift 6535022
  have htrace : WordTrace (prefixWord ++ tailWord_6535022) baseStart_6535022 baseEnd_6535022 := by
    simpa [prefixWord, tailWord_6535022, baseEnd_6535022] using wordTrace_append hprefix tailTrace_6535022
  have hstable : (prefixWord ++ tailWord_6535022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535022).length < 2 ^ (prefixWord ++ tailWord_6535022).sum := by decide
  have hdescent : baseEnd_6535022 < baseStart_6535022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535079 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6535079 : Nat := 118140960795 + 6535079 * 2 ^ 59
def prefixEnd_6535079 : Nat := 4983230072969 + 3 ^ 40 * 6535079 * 2
def baseEnd_6535079 : Nat := 3355636642103742207058225

theorem tailTrace_6535079 : CollatzResearch.WordTrace tailWord_6535079 prefixEnd_6535079 3355636642103742207058225 := by
  unfold tailWord_6535079
  simp only [CollatzResearch.WordTrace]
  refine ⟨238353912691532360480840291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158902608461021573653893527 238353912691532360480840291)
  ·
    refine ⟨357530869037298540721260437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238353912691532360480840291 357530869037298540721260437)
    ·
      refine ⟨16759259486123369096309083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357530869037298540721260437 16759259486123369096309083)
      ·
        refine ⟨25138889229185053644463625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16759259486123369096309083 25138889229185053644463625)
        ·
          refine ⟨18854166921888790233347719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25138889229185053644463625 18854166921888790233347719)
          ·
            refine ⟨28281250382833185350021579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18854166921888790233347719 28281250382833185350021579)
            ·
              refine ⟨42421875574249778025032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28281250382833185350021579 42421875574249778025032369)
              ·
                refine ⟨31816406680687333518774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42421875574249778025032369 31816406680687333518774277)
                ·
                  refine ⟨5965576252628875034770177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31816406680687333518774277 5965576252628875034770177)
                  ·
                    refine ⟨4474182189471656276077633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965576252628875034770177 4474182189471656276077633)
                    ·
                      refine ⟨3355636642103742207058225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474182189471656276077633 3355636642103742207058225)
                      ·
                        rfl

theorem cell23_6535079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6535079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535079 prefixEnd_6535079 := by exact prefixLift 6535079
  have htrace : WordTrace (prefixWord ++ tailWord_6535079) baseStart_6535079 baseEnd_6535079 := by
    simpa [prefixWord, tailWord_6535079, baseEnd_6535079] using wordTrace_append hprefix tailTrace_6535079
  have hstable : (prefixWord ++ tailWord_6535079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535079).length < 2 ^ (prefixWord ++ tailWord_6535079).sum := by decide
  have hdescent : baseEnd_6535079 < baseStart_6535079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535098 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_6535098 : Nat := 118140960795 + 6535098 * 2 ^ 59
def prefixEnd_6535098 : Nat := 4983230072969 + 3 ^ 40 * 6535098 * 2
def baseEnd_6535098 : Nat := 1118548799412059210906879

theorem tailTrace_6535098 : CollatzResearch.WordTrace tailWord_6535098 prefixEnd_6535098 1118548799412059210906879 := by
  unfold tailWord_6535098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59588651419615881681445487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158903070452309017817187965 59588651419615881681445487)
  ·
    refine ⟨89382977129423822522168231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59588651419615881681445487 89382977129423822522168231)
    ·
      refine ⟨134074465694135733783252347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89382977129423822522168231 134074465694135733783252347)
      ·
        refine ⟨201111698541203600674878521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134074465694135733783252347 201111698541203600674878521)
        ·
          refine ⟨150833773905902700506158891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201111698541203600674878521 150833773905902700506158891)
          ·
            refine ⟨226250660858854050759238337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150833773905902700506158891 226250660858854050759238337)
            ·
              refine ⟨169687995644140538069428753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226250660858854050759238337 169687995644140538069428753)
              ·
                refine ⟨127265996733105403552071565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169687995644140538069428753 127265996733105403552071565)
                ·
                  refine ⟨47724748774914526332026837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127265996733105403552071565 47724748774914526332026837)
                  ·
                    refine ⟨1118548799412059210906879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47724748774914526332026837 1118548799412059210906879)
                    ·
                      rfl

theorem cell23_6535098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_6535098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535098 prefixEnd_6535098 := by exact prefixLift 6535098
  have htrace : WordTrace (prefixWord ++ tailWord_6535098) baseStart_6535098 baseEnd_6535098 := by
    simpa [prefixWord, tailWord_6535098, baseEnd_6535098] using wordTrace_append hprefix tailTrace_6535098
  have hstable : (prefixWord ++ tailWord_6535098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535098).length < 2 ^ (prefixWord ++ tailWord_6535098).sum := by decide
  have hdescent : baseEnd_6535098 < baseStart_6535098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535102 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_6535102 : Nat := 118140960795 + 6535102 * 2 ^ 59
def prefixEnd_6535102 : Nat := 4983230072969 + 3 ^ 40 * 6535102 * 2
def baseEnd_6535102 : Nat := 372849828017643957452291

theorem tailTrace_6535102 : CollatzResearch.WordTrace tailWord_6535102 prefixEnd_6535102 372849828017643957452291 := by
  unfold tailWord_6535102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29794343946306129426115945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158903167713632690272618373 29794343946306129426115945)
  ·
    refine ⟨22345757959729597069586959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29794343946306129426115945 22345757959729597069586959)
    ·
      refine ⟨33518636939594395604380439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22345757959729597069586959 33518636939594395604380439)
      ·
        refine ⟨50277955409391593406570659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33518636939594395604380439 50277955409391593406570659)
        ·
          refine ⟨75416933114087390109855989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50277955409391593406570659 75416933114087390109855989)
          ·
            refine ⟨7070337479445692822798999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75416933114087390109855989 7070337479445692822798999)
            ·
              refine ⟨10605506219168539234198499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070337479445692822798999 10605506219168539234198499)
              ·
                refine ⟨15908259328752808851297749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10605506219168539234198499 15908259328752808851297749)
                ·
                  refine ⟨372849828017643957452291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15908259328752808851297749 372849828017643957452291)
                  ·
                    rfl

theorem cell23_6535102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_6535102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535102 prefixEnd_6535102 := by exact prefixLift 6535102
  have htrace : WordTrace (prefixWord ++ tailWord_6535102) baseStart_6535102 baseEnd_6535102 := by
    simpa [prefixWord, tailWord_6535102, baseEnd_6535102] using wordTrace_append hprefix tailTrace_6535102
  have hstable : (prefixWord ++ tailWord_6535102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535102).length < 2 ^ (prefixWord ++ tailWord_6535102).sum := by decide
  have hdescent : baseEnd_6535102 < baseStart_6535102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535196 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6535196 : Nat := 118140960795 + 6535196 * 2 ^ 59
def prefixEnd_6535196 : Nat := 4983230072969 + 3 ^ 40 * 6535196 * 2
def baseEnd_6535196 : Nat := 1118565573113439416431729

theorem tailTrace_6535196 : CollatzResearch.WordTrace tailWord_6535196 prefixEnd_6535196 1118565573113439416431729 := by
  unfold tailWord_6535196
  simp only [CollatzResearch.WordTrace]
  refine ⟨119179090016054244731424721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158905453354738992975232961 119179090016054244731424721)
  ·
    refine ⟨89384317512040683548568541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119179090016054244731424721 89384317512040683548568541)
    ·
      refine ⟨33519119067015256330713203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89384317512040683548568541 33519119067015256330713203)
      ·
        refine ⟨50278678600522884496069805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33519119067015256330713203 50278678600522884496069805)
        ·
          refine ⟨18854504475196081686026177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50278678600522884496069805 18854504475196081686026177)
          ·
            refine ⟨14140878356397061264519633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18854504475196081686026177 14140878356397061264519633)
            ·
              refine ⟨10605658767297795948389725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14140878356397061264519633 10605658767297795948389725)
              ·
                refine ⟨3977122037736673480646147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10605658767297795948389725 3977122037736673480646147)
                ·
                  refine ⟨5965683056605010220969221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977122037736673480646147 5965683056605010220969221)
                  ·
                    refine ⟨1118565573113439416431729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5965683056605010220969221 1118565573113439416431729)
                    ·
                      rfl

theorem cell23_6535196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6535196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535196 prefixEnd_6535196 := by exact prefixLift 6535196
  have htrace : WordTrace (prefixWord ++ tailWord_6535196) baseStart_6535196 baseEnd_6535196 := by
    simpa [prefixWord, tailWord_6535196, baseEnd_6535196] using wordTrace_append hprefix tailTrace_6535196
  have hstable : (prefixWord ++ tailWord_6535196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535196).length < 2 ^ (prefixWord ++ tailWord_6535196).sum := by decide
  have hdescent : baseEnd_6535196 < baseStart_6535196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535235 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 6]
def baseStart_6535235 : Nat := 118140960795 + 6535235 * 2 ^ 59
def prefixEnd_6535235 : Nat := 4983230072969 + 3 ^ 40 * 6535235 * 2
def baseEnd_6535235 : Nat := 1118572248361947865569169

theorem tailTrace_6535235 : CollatzResearch.WordTrace tailWord_6535235 prefixEnd_6535235 1118572248361947865569169 := by
  unfold tailWord_6535235
  simp only [CollatzResearch.WordTrace]
  refine ⟨238359602478967199123519159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158906401652644799415679439 238359602478967199123519159)
  ·
    refine ⟨357539403718450798685278739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238359602478967199123519159 357539403718450798685278739)
    ·
      refine ⟨536309105577676198027918109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357539403718450798685278739 536309105577676198027918109)
      ·
        refine ⟨201115914591628574260469291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536309105577676198027918109 201115914591628574260469291)
        ·
          refine ⟨301673871887442861390703937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201115914591628574260469291 301673871887442861390703937)
          ·
            refine ⟨226255403915582146043027953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301673871887442861390703937 226255403915582146043027953)
            ·
              refine ⟨169691552936686609532270965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226255403915582146043027953 169691552936686609532270965)
              ·
                refine ⟨15908583087814369643650403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169691552936686609532270965 15908583087814369643650403)
                ·
                  refine ⟨23862874631721554465475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15908583087814369643650403 23862874631721554465475605)
                  ·
                    refine ⟨1118572248361947865569169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23862874631721554465475605 1118572248361947865569169)
                    ·
                      rfl

theorem cell23_6535235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_6535235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535235 prefixEnd_6535235 := by exact prefixLift 6535235
  have htrace : WordTrace (prefixWord ++ tailWord_6535235) baseStart_6535235 baseEnd_6535235 := by
    simpa [prefixWord, tailWord_6535235, baseEnd_6535235] using wordTrace_append hprefix tailTrace_6535235
  have hstable : (prefixWord ++ tailWord_6535235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535235).length < 2 ^ (prefixWord ++ tailWord_6535235).sum := by decide
  have hdescent : baseEnd_6535235 < baseStart_6535235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535242 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_6535242 : Nat := 118140960795 + 6535242 * 2 ^ 59
def prefixEnd_6535242 : Nat := 4983230072969 + 3 ^ 40 * 6535242 * 2
def baseEnd_6535242 : Nat := 3355720339450425069319975

theorem tailTrace_6535242 : CollatzResearch.WordTrace tailWord_6535242 prefixEnd_6535242 3355720339450425069319975 := by
  unfold tailWord_6535242
  simp only [CollatzResearch.WordTrace]
  refine ⟨59589964447485459829755995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158906571859961226212682653 59589964447485459829755995)
  ·
    refine ⟨89384946671228189744633993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59589964447485459829755995 89384946671228189744633993)
    ·
      refine ⟨67038710003421142308475495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89384946671228189744633993 67038710003421142308475495)
      ·
        refine ⟨100558065005131713462713243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67038710003421142308475495 100558065005131713462713243)
        ·
          refine ⟨150837097507697570194069865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100558065005131713462713243 150837097507697570194069865)
          ·
            refine ⟨113127823130773177645552399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150837097507697570194069865 113127823130773177645552399)
            ·
              refine ⟨169691734696159766468328599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113127823130773177645552399 169691734696159766468328599)
              ·
                refine ⟨254537602044239649702492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169691734696159766468328599 254537602044239649702492899)
                ·
                  refine ⟨381806403066359474553739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254537602044239649702492899 381806403066359474553739349)
                  ·
                    refine ⟨4474293785933900092426633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 381806403066359474553739349 4474293785933900092426633)
                    ·
                      refine ⟨3355720339450425069319975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474293785933900092426633 3355720339450425069319975)
                      ·
                        rfl

theorem cell23_6535242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_6535242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535242 prefixEnd_6535242 := by exact prefixLift 6535242
  have htrace : WordTrace (prefixWord ++ tailWord_6535242) baseStart_6535242 baseEnd_6535242 := by
    simpa [prefixWord, tailWord_6535242, baseEnd_6535242] using wordTrace_append hprefix tailTrace_6535242
  have hstable : (prefixWord ++ tailWord_6535242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535242).length < 2 ^ (prefixWord ++ tailWord_6535242).sum := by decide
  have hdescent : baseEnd_6535242 < baseStart_6535242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535253 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6535253 : Nat := 118140960795 + 6535253 * 2 ^ 59
def prefixEnd_6535253 : Nat := 4983230072969 + 3 ^ 40 * 6535253 * 2
def baseEnd_6535253 : Nat := 3355725987737624526282425

theorem tailTrace_6535253 : CollatzResearch.WordTrace tailWord_6535253 prefixEnd_6535253 3355725987737624526282425 := by
  unfold tailWord_6535253
  simp only [CollatzResearch.WordTrace]
  refine ⟨238360258992901988197674413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158906839328601325465116275 238360258992901988197674413)
  ·
    refine ⟨89385097122338245574127905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238360258992901988197674413 89385097122338245574127905)
    ·
      refine ⟨67038822841753684180595929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89385097122338245574127905 67038822841753684180595929)
      ·
        refine ⟨50279117131315263135446947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67038822841753684180595929 50279117131315263135446947)
        ·
          refine ⟨75418675696972894703170421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50279117131315263135446947 75418675696972894703170421)
          ·
            refine ⟨7070500846591208878422227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75418675696972894703170421 7070500846591208878422227)
            ·
              refine ⟨10605751269886813317633341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070500846591208878422227 10605751269886813317633341)
              ·
                refine ⟨3977156726207554994112503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10605751269886813317633341 3977156726207554994112503)
                ·
                  refine ⟨5965735089311332491168755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977156726207554994112503 5965735089311332491168755)
                  ·
                    refine ⟨8948602633966998736753133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5965735089311332491168755 8948602633966998736753133)
                    ·
                      refine ⟨3355725987737624526282425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948602633966998736753133 3355725987737624526282425)
                      ·
                        rfl

theorem cell23_6535253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6535253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535253 prefixEnd_6535253 := by exact prefixLift 6535253
  have htrace : WordTrace (prefixWord ++ tailWord_6535253) baseStart_6535253 baseEnd_6535253 := by
    simpa [prefixWord, tailWord_6535253, baseEnd_6535253] using wordTrace_append hprefix tailTrace_6535253
  have hstable : (prefixWord ++ tailWord_6535253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535253).length < 2 ^ (prefixWord ++ tailWord_6535253).sum := by decide
  have hdescent : baseEnd_6535253 < baseStart_6535253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535276 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_6535276 : Nat := 118140960795 + 6535276 * 2 ^ 59
def prefixEnd_6535276 : Nat := 4983230072969 + 3 ^ 40 * 6535276 * 2
def baseEnd_6535276 : Nat := 3355737797792677936294819

theorem tailTrace_6535276 : CollatzResearch.WordTrace tailWord_6535276 prefixEnd_6535276 3355737797792677936294819 := by
  unfold tailWord_6535276
  simp only [CollatzResearch.WordTrace]
  refine ⟨119180548935909331562880841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158907398581212442083841121 119180548935909331562880841)
  ·
    refine ⟨89385411701931998672160631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119180548935909331562880841 89385411701931998672160631)
    ·
      refine ⟨134078117552897998008240947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89385411701931998672160631 134078117552897998008240947)
      ·
        refine ⟨201117176329346997012361421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134078117552897998008240947 201117176329346997012361421)
        ·
          refine ⟨75418941123505123879635533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201117176329346997012361421 75418941123505123879635533)
          ·
            refine ⟨28282102921314421454863325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75418941123505123879635533 28282102921314421454863325)
            ·
              refine ⟨10605788595492908045573747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28282102921314421454863325 10605788595492908045573747)
              ·
                refine ⟨15908682893239362068360621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10605788595492908045573747 15908682893239362068360621)
                ·
                  refine ⟨5965756084964760775635233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15908682893239362068360621 5965756084964760775635233)
                  ·
                    refine ⟨4474317063723570581726425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965756084964760775635233 4474317063723570581726425)
                    ·
                      refine ⟨3355737797792677936294819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474317063723570581726425 3355737797792677936294819)
                      ·
                        rfl

theorem cell23_6535276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_6535276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535276 prefixEnd_6535276 := by exact prefixLift 6535276
  have htrace : WordTrace (prefixWord ++ tailWord_6535276) baseStart_6535276 baseEnd_6535276 := by
    simpa [prefixWord, tailWord_6535276, baseEnd_6535276] using wordTrace_append hprefix tailTrace_6535276
  have hstable : (prefixWord ++ tailWord_6535276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535276).length < 2 ^ (prefixWord ++ tailWord_6535276).sum := by decide
  have hdescent : baseEnd_6535276 < baseStart_6535276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535282 : List Nat := [3, 2, 1, 2, 2, 3, 2, 8]
def baseStart_6535282 : Nat := 118140960795 + 6535282 * 2 ^ 59
def prefixEnd_6535282 : Nat := 4983230072969 + 3 ^ 40 * 6535282 * 2
def baseEnd_6535282 : Nat := 124286699210244626400733

theorem tailTrace_6535282 : CollatzResearch.WordTrace tailWord_6535282 prefixEnd_6535282 124286699210244626400733 := by
  unfold tailWord_6535282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59590329177449231537620025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158907544473197950766986733 59590329177449231537620025)
  ·
    refine ⟨44692746883086923653215019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59590329177449231537620025 44692746883086923653215019)
    ·
      refine ⟨67039120324630385479822529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44692746883086923653215019 67039120324630385479822529)
      ·
        refine ⟨50279340243472789109866897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67039120324630385479822529 50279340243472789109866897)
        ·
          refine ⟨37709505182604591832400173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50279340243472789109866897 37709505182604591832400173)
          ·
            refine ⟨14141064443476721937150065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37709505182604591832400173 14141064443476721937150065)
            ·
              refine ⟨10605798332607541452862549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14141064443476721937150065 10605798332607541452862549)
              ·
                refine ⟨124286699210244626400733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10605798332607541452862549 124286699210244626400733)
                ·
                  rfl

theorem cell23_6535282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_6535282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535282 prefixEnd_6535282 := by exact prefixLift 6535282
  have htrace : WordTrace (prefixWord ++ tailWord_6535282) baseStart_6535282 baseEnd_6535282 := by
    simpa [prefixWord, tailWord_6535282, baseEnd_6535282] using wordTrace_append hprefix tailTrace_6535282
  have hstable : (prefixWord ++ tailWord_6535282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535282).length < 2 ^ (prefixWord ++ tailWord_6535282).sum := by decide
  have hdescent : baseEnd_6535282 < baseStart_6535282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535286 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6535286 : Nat := 118140960795 + 6535286 * 2 ^ 59
def prefixEnd_6535286 : Nat := 4983230072969 + 3 ^ 40 * 6535286 * 2
def baseEnd_6535286 : Nat := 1118580977533074299056591

theorem tailTrace_6535286 : CollatzResearch.WordTrace tailWord_6535286 prefixEnd_6535286 1118580977533074299056591 := by
  unfold tailWord_6535286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897591412611402177101607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158907641734521623222417141 14897591412611402177101607)
  ·
    refine ⟨22346387118917103265652411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14897591412611402177101607 22346387118917103265652411)
    ·
      refine ⟨33519580678375654898478617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22346387118917103265652411 33519580678375654898478617)
      ·
        refine ⟨25139685508781741173858963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33519580678375654898478617 25139685508781741173858963)
        ·
          refine ⟨37709528263172611760788445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25139685508781741173858963 37709528263172611760788445)
          ·
            refine ⟨14141073098689729410295667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37709528263172611760788445 14141073098689729410295667)
            ·
              refine ⟨21211609648034594115443501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14141073098689729410295667 21211609648034594115443501)
              ·
                refine ⟨7954353618012972793291313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21211609648034594115443501 7954353618012972793291313)
                ·
                  refine ⟨5965765213509729594968485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7954353618012972793291313 5965765213509729594968485)
                  ·
                    refine ⟨1118580977533074299056591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5965765213509729594968485 1118580977533074299056591)
                    ·
                      rfl

theorem cell23_6535286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6535286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535286 prefixEnd_6535286 := by exact prefixLift 6535286
  have htrace : WordTrace (prefixWord ++ tailWord_6535286) baseStart_6535286 baseEnd_6535286 := by
    simpa [prefixWord, tailWord_6535286, baseEnd_6535286] using wordTrace_append hprefix tailTrace_6535286
  have hstable : (prefixWord ++ tailWord_6535286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535286).length < 2 ^ (prefixWord ++ tailWord_6535286).sum := by decide
  have hdescent : baseEnd_6535286 < baseStart_6535286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535327 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6535327 : Nat := 118140960795 + 6535327 * 2 ^ 59
def prefixEnd_6535327 : Nat := 4983230072969 + 3 ^ 40 * 6535327 * 2
def baseEnd_6535327 : Nat := 3355763985306057236757085

theorem tailTrace_6535327 : CollatzResearch.WordTrace tailWord_6535327 prefixEnd_6535327 3355763985306057236757085 := by
  unfold tailWord_6535327
  simp only [CollatzResearch.WordTrace]
  refine ⟨238362957994633898835868235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158908638663089265890578823 238362957994633898835868235)
  ·
    refine ⟨357544436991950848253802353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238362957994633898835868235 357544436991950848253802353)
    ·
      refine ⟨268158327743963136190351765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357544436991950848253802353 268158327743963136190351765)
      ·
        refine ⟨12569921612998272008922739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 268158327743963136190351765 12569921612998272008922739)
        ·
          refine ⟨18854882419497408013384109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12569921612998272008922739 18854882419497408013384109)
          ·
            refine ⟨7070580907311528005019041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18854882419497408013384109 7070580907311528005019041)
            ·
              refine ⟨5302935680483646003764281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7070580907311528005019041 5302935680483646003764281)
              ·
                refine ⟨3977201760362734502823211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5302935680483646003764281 3977201760362734502823211)
                ·
                  refine ⟨5965802640544101754234817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977201760362734502823211 5965802640544101754234817)
                  ·
                    refine ⟨4474351980408076315676113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965802640544101754234817 4474351980408076315676113)
                    ·
                      refine ⟨3355763985306057236757085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474351980408076315676113 3355763985306057236757085)
                      ·
                        rfl

theorem cell23_6535327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6535327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535327 prefixEnd_6535327 := by exact prefixLift 6535327
  have htrace : WordTrace (prefixWord ++ tailWord_6535327) baseStart_6535327 baseEnd_6535327 := by
    simpa [prefixWord, tailWord_6535327, baseEnd_6535327] using wordTrace_append hprefix tailTrace_6535327
  have hstable : (prefixWord ++ tailWord_6535327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535327).length < 2 ^ (prefixWord ++ tailWord_6535327).sum := by decide
  have hdescent : baseEnd_6535327 < baseStart_6535327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535352 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_6535352 : Nat := 118140960795 + 6535352 * 2 ^ 59
def prefixEnd_6535352 : Nat := 4983230072969 + 3 ^ 40 * 6535352 * 2
def baseEnd_6535352 : Nat := 3355776822322419638944469

theorem tailTrace_6535352 : CollatzResearch.WordTrace tailWord_6535352 prefixEnd_6535352 3355776822322419638944469 := by
  unfold tailWord_6535352
  simp only [CollatzResearch.WordTrace]
  refine ⟨119181934909771664052764155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158909246546362218737018873 119181934909771664052764155)
  ·
    refine ⟨178772902364657496079146233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119181934909771664052764155 178772902364657496079146233)
    ·
      refine ⟨134079676773493122059359675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178772902364657496079146233 134079676773493122059359675)
      ·
        refine ⟨201119515160239683089039513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134079676773493122059359675 201119515160239683089039513)
        ·
          refine ⟨150839636370179762316779635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201119515160239683089039513 150839636370179762316779635)
          ·
            refine ⟨226259454555269643475169453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150839636370179762316779635 226259454555269643475169453)
            ·
              refine ⟨84847295458226116303188545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226259454555269643475169453 84847295458226116303188545)
              ·
                refine ⟨63635471593669587227391409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84847295458226116303188545 63635471593669587227391409)
                ·
                  refine ⟨47726603695252190420543557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63635471593669587227391409 47726603695252190420543557)
                  ·
                    refine ⟨8948738192859785703851917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47726603695252190420543557 8948738192859785703851917)
                    ·
                      refine ⟨3355776822322419638944469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948738192859785703851917 3355776822322419638944469)
                      ·
                        rfl

theorem cell23_6535352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_6535352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535352 prefixEnd_6535352 := by exact prefixLift 6535352
  have htrace : WordTrace (prefixWord ++ tailWord_6535352) baseStart_6535352 baseEnd_6535352 := by
    simpa [prefixWord, tailWord_6535352, baseEnd_6535352] using wordTrace_append hprefix tailTrace_6535352
  have hstable : (prefixWord ++ tailWord_6535352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535352).length < 2 ^ (prefixWord ++ tailWord_6535352).sum := by decide
  have hdescent : baseEnd_6535352 < baseStart_6535352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535389 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 7]
def baseStart_6535389 : Nat := 118140960795 + 6535389 * 2 ^ 59
def prefixEnd_6535389 : Nat := 4983230072969 + 3 ^ 40 * 6535389 * 2
def baseEnd_6535389 : Nat := 372866202345181777131311

theorem tailTrace_6535389 : CollatzResearch.WordTrace tailWord_6535389 prefixEnd_6535389 372866202345181777131311 := by
  unfold tailWord_6535389
  simp only [CollatzResearch.WordTrace]
  refine ⟨238365219320409283424625221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158910146213606188949750147 238365219320409283424625221)
  ·
    refine ⟨44693478622576740642117229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238365219320409283424625221 44693478622576740642117229)
    ·
      refine ⟨16760054483466277740793961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44693478622576740642117229 16760054483466277740793961)
      ·
        refine ⟨12570040862599708305595471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16760054483466277740793961 12570040862599708305595471)
        ·
          refine ⟨18855061293899562458393207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12570040862599708305595471 18855061293899562458393207)
          ·
            refine ⟨28282591940849343687589811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18855061293899562458393207 28282591940849343687589811)
            ·
              refine ⟨42423887911274015531384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28282591940849343687589811 42423887911274015531384717)
              ·
                refine ⟨15908957966727755824269269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42423887911274015531384717 15908957966727755824269269)
                ·
                  refine ⟨372866202345181777131311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15908957966727755824269269 372866202345181777131311)
                  ·
                    rfl

theorem cell23_6535389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_6535389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535389 prefixEnd_6535389 := by exact prefixLift 6535389
  have htrace : WordTrace (prefixWord ++ tailWord_6535389) baseStart_6535389 baseEnd_6535389 := by
    simpa [prefixWord, tailWord_6535389, baseEnd_6535389] using wordTrace_append hprefix tailTrace_6535389
  have hstable : (prefixWord ++ tailWord_6535389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535389).length < 2 ^ (prefixWord ++ tailWord_6535389).sum := by decide
  have hdescent : baseEnd_6535389 < baseStart_6535389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535394 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6535394 : Nat := 118140960795 + 6535394 * 2 ^ 59
def prefixEnd_6535394 : Nat := 4983230072969 + 3 ^ 40 * 6535394 * 2
def baseEnd_6535394 : Nat := 3355798388509908474619277

theorem tailTrace_6535394 : CollatzResearch.WordTrace tailWord_6535394 prefixEnd_6535394 3355798388509908474619277 := by
  unfold tailWord_6535394
  simp only [CollatzResearch.WordTrace]
  refine ⟨59591350421347792319639309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158910267790260779519038157 59591350421347792319639309)
  ·
    refine ⟨22346756408005422119864741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59591350421347792319639309 22346756408005422119864741)
    ·
      refine ⟨4190016826501016647474639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22346756408005422119864741 4190016826501016647474639)
      ·
        refine ⟨6285025239751524971211959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190016826501016647474639 6285025239751524971211959)
        ·
          refine ⟨9427537859627287456817939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285025239751524971211959 9427537859627287456817939)
          ·
            refine ⟨14141306789440931185226909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427537859627287456817939 14141306789440931185226909)
            ·
              refine ⟨5302990046040349194460091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14141306789440931185226909 5302990046040349194460091)
              ·
                refine ⟨7954485069060523791690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302990046040349194460091 7954485069060523791690137)
                ·
                  refine ⟨5965863801795392843767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7954485069060523791690137 5965863801795392843767603)
                  ·
                    refine ⟨8948795702693089265651405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5965863801795392843767603 8948795702693089265651405)
                    ·
                      refine ⟨3355798388509908474619277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948795702693089265651405 3355798388509908474619277)
                      ·
                        rfl

theorem cell23_6535394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6535394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535394 prefixEnd_6535394 := by exact prefixLift 6535394
  have htrace : WordTrace (prefixWord ++ tailWord_6535394) baseStart_6535394 baseEnd_6535394 := by
    simpa [prefixWord, tailWord_6535394, baseEnd_6535394] using wordTrace_append hprefix tailTrace_6535394
  have hstable : (prefixWord ++ tailWord_6535394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535394).length < 2 ^ (prefixWord ++ tailWord_6535394).sum := by decide
  have hdescent : baseEnd_6535394 < baseStart_6535394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535400 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6535400 : Nat := 118140960795 + 6535400 * 2 ^ 59
def prefixEnd_6535400 : Nat := 4983230072969 + 3 ^ 40 * 6535400 * 2
def baseEnd_6535400 : Nat := 3355801469393835451144249

theorem tailTrace_6535400 : CollatzResearch.WordTrace tailWord_6535400 prefixEnd_6535400 3355801469393835451144249 := by
  unfold tailWord_6535400
  simp only [CollatzResearch.WordTrace]
  refine ⟨119182810261684716151637827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158910413682246288202183769 119182810261684716151637827)
  ·
    refine ⟨178774215392527074227456741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119182810261684716151637827 178774215392527074227456741)
    ·
      refine ⟨33520165386098826417648139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178774215392527074227456741 33520165386098826417648139)
      ·
        refine ⟨50280248079148239626472209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33520165386098826417648139 50280248079148239626472209)
        ·
          refine ⟨37710186059361179719854157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50280248079148239626472209 37710186059361179719854157)
          ·
            refine ⟨14141319772260442394945309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37710186059361179719854157 14141319772260442394945309)
            ·
              refine ⟨5302994914597665898104491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14141319772260442394945309 5302994914597665898104491)
              ·
                refine ⟨7954492371896498847156737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5302994914597665898104491 7954492371896498847156737)
                ·
                  refine ⟨5965869278922374135367553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7954492371896498847156737 5965869278922374135367553)
                  ·
                    refine ⟨4474401959191780601525665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5965869278922374135367553 4474401959191780601525665)
                    ·
                      refine ⟨3355801469393835451144249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474401959191780601525665 3355801469393835451144249)
                      ·
                        rfl

theorem cell23_6535400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6535400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535400 prefixEnd_6535400 := by exact prefixLift 6535400
  have htrace : WordTrace (prefixWord ++ tailWord_6535400) baseStart_6535400 baseEnd_6535400 := by
    simpa [prefixWord, tailWord_6535400, baseEnd_6535400] using wordTrace_append hprefix tailTrace_6535400
  have hstable : (prefixWord ++ tailWord_6535400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535400).length < 2 ^ (prefixWord ++ tailWord_6535400).sum := by decide
  have hdescent : baseEnd_6535400 < baseStart_6535400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535402 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_6535402 : Nat := 118140960795 + 6535402 * 2 ^ 59
def prefixEnd_6535402 : Nat := 4983230072969 + 3 ^ 40 * 6535402 * 2
def baseEnd_6535402 : Nat := 1118600832118381481106413

theorem tailTrace_6535402 : CollatzResearch.WordTrace tailWord_6535402 prefixEnd_6535402 1118600832118381481106413 := by
  unfold tailWord_6535402
  simp only [CollatzResearch.WordTrace]
  refine ⟨59591423367340546661212115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158910462312908124429898973 59591423367340546661212115)
  ·
    refine ⟨89387135051010819991818173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59591423367340546661212115 89387135051010819991818173)
    ·
      refine ⟨33520175644129057496931815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89387135051010819991818173 33520175644129057496931815)
      ·
        refine ⟨50280263466193586245397723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33520175644129057496931815 50280263466193586245397723)
        ·
          refine ⟨75420395199290379368096585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50280263466193586245397723 75420395199290379368096585)
          ·
            refine ⟨56565296399467784526072439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75420395199290379368096585 56565296399467784526072439)
            ·
              refine ⟨84847944599201676789108659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56565296399467784526072439 84847944599201676789108659)
              ·
                refine ⟨127271916898802515183662989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84847944599201676789108659 127271916898802515183662989)
                ·
                  refine ⟨47726968837050943193873621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127271916898802515183662989 47726968837050943193873621)
                  ·
                    refine ⟨1118600832118381481106413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47726968837050943193873621 1118600832118381481106413)
                    ·
                      rfl

theorem cell23_6535402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_6535402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535402 prefixEnd_6535402 := by exact prefixLift 6535402
  have htrace : WordTrace (prefixWord ++ tailWord_6535402) baseStart_6535402 baseEnd_6535402 := by
    simpa [prefixWord, tailWord_6535402, baseEnd_6535402] using wordTrace_append hprefix tailTrace_6535402
  have hstable : (prefixWord ++ tailWord_6535402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535402).length < 2 ^ (prefixWord ++ tailWord_6535402).sum := by decide
  have hdescent : baseEnd_6535402 < baseStart_6535402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535409 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_6535409 : Nat := 118140960795 + 6535409 * 2 ^ 59
def prefixEnd_6535409 : Nat := 4983230072969 + 3 ^ 40 * 6535409 * 2
def baseEnd_6535409 : Nat := 3355806090719725915931707

theorem tailTrace_6535409 : CollatzResearch.WordTrace tailWord_6535409 prefixEnd_6535409 3355806090719725915931707 := by
  unfold tailWord_6535409
  simp only [CollatzResearch.WordTrace]
  refine ⟨238365948780336826840353281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158910632520224551226902187 238365948780336826840353281)
  ·
    refine ⟨178774461585252620130264961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238365948780336826840353281 178774461585252620130264961)
    ·
      refine ⟨134080846188939465097698721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178774461585252620130264961 134080846188939465097698721)
      ·
        refine ⟨100560634641704598823274041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134080846188939465097698721 100560634641704598823274041)
        ·
          refine ⟨75420475981278449117455531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100560634641704598823274041 75420475981278449117455531)
          ·
            refine ⟨113130713971917673676183297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75420475981278449117455531 113130713971917673676183297)
            ·
              refine ⟨84848035478938255257137473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113130713971917673676183297 84848035478938255257137473)
              ·
                refine ⟨63636026609203691442853105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84848035478938255257137473 63636026609203691442853105)
                ·
                  refine ⟨47727019956902768582139829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63636026609203691442853105 47727019956902768582139829)
                  ·
                    refine ⟨4474408120959634554575609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47727019956902768582139829 4474408120959634554575609)
                    ·
                      refine ⟨3355806090719725915931707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474408120959634554575609 3355806090719725915931707)
                      ·
                        rfl

theorem cell23_6535409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_6535409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535409 prefixEnd_6535409 := by exact prefixLift 6535409
  have htrace : WordTrace (prefixWord ++ tailWord_6535409) baseStart_6535409 baseEnd_6535409 := by
    simpa [prefixWord, tailWord_6535409, baseEnd_6535409] using wordTrace_append hprefix tailTrace_6535409
  have hstable : (prefixWord ++ tailWord_6535409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535409).length < 2 ^ (prefixWord ++ tailWord_6535409).sum := by decide
  have hdescent : baseEnd_6535409 < baseStart_6535409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535439 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 4, 4, 2]
def baseStart_6535439 : Nat := 118140960795 + 6535439 * 2 ^ 59
def prefixEnd_6535439 : Nat := 4983230072969 + 3 ^ 40 * 6535439 * 2
def baseEnd_6535439 : Nat := 3355821495139360798556569

theorem tailTrace_6535439 : CollatzResearch.WordTrace tailWord_6535439 prefixEnd_6535439 3355821495139360798556569 := by
  unfold tailWord_6535439
  simp only [CollatzResearch.WordTrace]
  refine ⟨238367042970228141963945371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158911361980152094642630247 238367042970228141963945371)
  ·
    refine ⟨357550564455342212945918057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238367042970228141963945371 357550564455342212945918057)
    ·
      refine ⟨268162923341506659709438543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357550564455342212945918057 268162923341506659709438543)
      ·
        refine ⟨402244385012259989564157815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268162923341506659709438543 402244385012259989564157815)
        ·
          refine ⟨603366577518389984346236723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402244385012259989564157815 603366577518389984346236723)
          ·
            refine ⟨905049866277584976519355085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603366577518389984346236723 905049866277584976519355085)
            ·
              refine ⟨339393699854094366194758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905049866277584976519355085 339393699854094366194758157)
              ·
                refine ⟨127272637445285387323034309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339393699854094366194758157 127272637445285387323034309)
                ·
                  refine ⟨23863619520991010123068933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127272637445285387323034309 23863619520991010123068933)
                  ·
                    refine ⟨4474428660185814398075425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23863619520991010123068933 4474428660185814398075425)
                    ·
                      refine ⟨3355821495139360798556569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474428660185814398075425 3355821495139360798556569)
                      ·
                        rfl

theorem cell23_6535439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4, 2].length) (baseStart_6535439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535439 prefixEnd_6535439 := by exact prefixLift 6535439
  have htrace : WordTrace (prefixWord ++ tailWord_6535439) baseStart_6535439 baseEnd_6535439 := by
    simpa [prefixWord, tailWord_6535439, baseEnd_6535439] using wordTrace_append hprefix tailTrace_6535439
  have hstable : (prefixWord ++ tailWord_6535439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535439).length < 2 ^ (prefixWord ++ tailWord_6535439).sum := by decide
  have hdescent : baseEnd_6535439 < baseStart_6535439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535459 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3]
def baseStart_6535459 : Nat := 118140960795 + 6535459 * 2 ^ 59
def prefixEnd_6535459 : Nat := 4983230072969 + 3 ^ 40 * 6535459 * 2
def baseEnd_6535459 : Nat := 3355831764752450720306477

theorem tailTrace_6535459 : CollatzResearch.WordTrace tailWord_6535459 prefixEnd_6535459 3355831764752450720306477 := by
  unfold tailWord_6535459
  simp only [CollatzResearch.WordTrace]
  refine ⟨238367772430155685379673431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158911848286770456919782287 238367772430155685379673431)
  ·
    refine ⟨357551658645233528069510147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238367772430155685379673431 357551658645233528069510147)
    ·
      refine ⟨536327487967850292104265221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357551658645233528069510147 536327487967850292104265221)
      ·
        refine ⟨100561403993971929769549729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536327487967850292104265221 100561403993971929769549729)
        ·
          refine ⟨75421052995478947327162297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100561403993971929769549729 75421052995478947327162297)
          ·
            refine ⟨56565789746609210495371723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75421052995478947327162297 56565789746609210495371723)
            ·
              refine ⟨84848684619913815743057585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56565789746609210495371723 84848684619913815743057585)
              ·
                refine ⟨63636513464935361807293189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84848684619913815743057585 63636513464935361807293189)
                ·
                  refine ⟨11931846274675380338867473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63636513464935361807293189 11931846274675380338867473)
                  ·
                    refine ⟨8948884706006535254150605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11931846274675380338867473 8948884706006535254150605)
                    ·
                      refine ⟨3355831764752450720306477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8948884706006535254150605 3355831764752450720306477)
                      ·
                        rfl

theorem cell23_6535459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_6535459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535459 prefixEnd_6535459 := by exact prefixLift 6535459
  have htrace : WordTrace (prefixWord ++ tailWord_6535459) baseStart_6535459 baseEnd_6535459 := by
    simpa [prefixWord, tailWord_6535459, baseEnd_6535459] using wordTrace_append hprefix tailTrace_6535459
  have hstable : (prefixWord ++ tailWord_6535459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535459).length < 2 ^ (prefixWord ++ tailWord_6535459).sum := by decide
  have hdescent : baseEnd_6535459 < baseStart_6535459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535529 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_6535529 : Nat := 118140960795 + 6535529 * 2 ^ 59
def prefixEnd_6535529 : Nat := 4983230072969 + 3 ^ 40 * 6535529 * 2
def baseEnd_6535529 : Nat := 3355867708398265446431155

theorem tailTrace_6535529 : CollatzResearch.WordTrace tailWord_6535529 prefixEnd_6535529 3355867708398265446431155 := by
  unfold tailWord_6535529
  simp only [CollatzResearch.WordTrace]
  refine ⟨238370325539902087334721641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158913550359934724889814427 238370325539902087334721641)
  ·
    refine ⟨178777744154926565501041231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238370325539902087334721641 178777744154926565501041231)
    ·
      refine ⟨268166616232389848251561847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178777744154926565501041231 268166616232389848251561847)
      ·
        refine ⟨402249924348584772377342771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268166616232389848251561847 402249924348584772377342771)
        ·
          refine ⟨603374886522877158566014157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402249924348584772377342771 603374886522877158566014157)
          ·
            refine ⟨226265582446078934462255309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 603374886522877158566014157 226265582446078934462255309)
            ·
              refine ⟨84849593417279600423345741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226265582446078934462255309 84849593417279600423345741)
              ·
                refine ⟨31818597531479850158754653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84849593417279600423345741 31818597531479850158754653)
                ·
                  refine ⟨11931974074304943809532995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31818597531479850158754653 11931974074304943809532995)
                  ·
                    refine ⟨17897961111457415714299493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11931974074304943809532995 17897961111457415714299493)
                    ·
                      refine ⟨3355867708398265446431155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17897961111457415714299493 3355867708398265446431155)
                      ·
                        rfl

theorem cell23_6535529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_6535529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535529 prefixEnd_6535529 := by exact prefixLift 6535529
  have htrace : WordTrace (prefixWord ++ tailWord_6535529) baseStart_6535529 baseEnd_6535529 := by
    simpa [prefixWord, tailWord_6535529, baseEnd_6535529] using wordTrace_append hprefix tailTrace_6535529
  have hstable : (prefixWord ++ tailWord_6535529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535529).length < 2 ^ (prefixWord ++ tailWord_6535529).sum := by decide
  have hdescent : baseEnd_6535529 < baseStart_6535529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535539 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 6, 4]
def baseStart_6535539 : Nat := 118140960795 + 6535539 * 2 ^ 59
def prefixEnd_6535539 : Nat := 4983230072969 + 3 ^ 40 * 6535539 * 2
def baseEnd_6535539 : Nat := 1118624281068270135768703

theorem tailTrace_6535539 : CollatzResearch.WordTrace tailWord_6535539 prefixEnd_6535539 1118624281068270135768703 := by
  unfold tailWord_6535539
  simp only [CollatzResearch.WordTrace]
  refine ⟨238370690269865859042585671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158913793513243906028390447 238370690269865859042585671)
  ·
    refine ⟨357556035404798788563878507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238370690269865859042585671 357556035404798788563878507)
    ·
      refine ⟨536334053107198182845817761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357556035404798788563878507 536334053107198182845817761)
      ·
        refine ⟨402250539830398637134363321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536334053107198182845817761 402250539830398637134363321)
        ·
          refine ⟨301687904872798977850772491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402250539830398637134363321 301687904872798977850772491)
          ·
            refine ⟨452531857309198466776158737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301687904872798977850772491 452531857309198466776158737)
            ·
              refine ⟨339398892981898850082119053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452531857309198466776158737 339398892981898850082119053)
              ·
                refine ⟨127274584868212068780794645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339398892981898850082119053 127274584868212068780794645)
                ·
                  refine ⟨5965996165697440724099749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127274584868212068780794645 5965996165697440724099749)
                  ·
                    refine ⟨1118624281068270135768703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5965996165697440724099749 1118624281068270135768703)
                    ·
                      rfl

theorem cell23_6535539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 4].length) (baseStart_6535539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535539 prefixEnd_6535539 := by exact prefixLift 6535539
  have htrace : WordTrace (prefixWord ++ tailWord_6535539) baseStart_6535539 baseEnd_6535539 := by
    simpa [prefixWord, tailWord_6535539, baseEnd_6535539] using wordTrace_append hprefix tailTrace_6535539
  have hstable : (prefixWord ++ tailWord_6535539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535539).length < 2 ^ (prefixWord ++ tailWord_6535539).sum := by decide
  have hdescent : baseEnd_6535539 < baseStart_6535539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535556 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6535556 : Nat := 118140960795 + 6535556 * 2 ^ 59
def prefixEnd_6535556 : Nat := 4983230072969 + 3 ^ 40 * 6535556 * 2
def baseEnd_6535556 : Nat := 1118627190791978946931177

theorem tailTrace_6535556 : CollatzResearch.WordTrace tailWord_6535556 prefixEnd_6535556 1118627190791978946931177 := by
  unfold tailWord_6535556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119185655155402135472977261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158914206873869513963969681 119185655155402135472977261)
  ·
    refine ⟨44694620683275800802366473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119185655155402135472977261 44694620683275800802366473)
    ·
      refine ⟨33520965512456850601774855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44694620683275800802366473 33520965512456850601774855)
      ·
        refine ⟨50281448268685275902662283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33520965512456850601774855 50281448268685275902662283)
        ·
          refine ⟨75422172403027913853993425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50281448268685275902662283 75422172403027913853993425)
          ·
            refine ⟨56566629302270935390495069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75422172403027913853993425 56566629302270935390495069)
            ·
              refine ⟨21212485988351600771435651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56566629302270935390495069 21212485988351600771435651)
              ·
                refine ⟨31818728982527401157153477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21212485988351600771435651 31818728982527401157153477)
                ·
                  refine ⟨5966011684223887716966277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31818728982527401157153477 5966011684223887716966277)
                  ·
                    refine ⟨1118627190791978946931177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966011684223887716966277 1118627190791978946931177)
                    ·
                      rfl

theorem cell23_6535556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6535556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535556 prefixEnd_6535556 := by exact prefixLift 6535556
  have htrace : WordTrace (prefixWord ++ tailWord_6535556) baseStart_6535556 baseEnd_6535556 := by
    simpa [prefixWord, tailWord_6535556, baseEnd_6535556] using wordTrace_append hprefix tailTrace_6535556
  have hstable : (prefixWord ++ tailWord_6535556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535556).length < 2 ^ (prefixWord ++ tailWord_6535556).sum := by decide
  have hdescent : baseEnd_6535556 < baseStart_6535556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535559 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_6535559 : Nat := 118140960795 + 6535559 * 2 ^ 59
def prefixEnd_6535559 : Nat := 4983230072969 + 3 ^ 40 * 6535559 * 2
def baseEnd_6535559 : Nat := 3355883112817900329056017

theorem tailTrace_6535559 : CollatzResearch.WordTrace tailWord_6535559 prefixEnd_6535559 3355883112817900329056017 := by
  unfold tailWord_6535559
  simp only [CollatzResearch.WordTrace]
  refine ⟨238371419729793402458313731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158914279819862268305542487 238371419729793402458313731)
  ·
    refine ⟨357557129594690103687470597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238371419729793402458313731 357557129594690103687470597)
    ·
      refine ⟨67041961799004394441400737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357557129594690103687470597 67041961799004394441400737)
      ·
        refine ⟨50281471349253295831050553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67041961799004394441400737 50281471349253295831050553)
        ·
          refine ⟨37711103511939971873287915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50281471349253295831050553 37711103511939971873287915)
          ·
            refine ⟨56566655267909957809931873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37711103511939971873287915 56566655267909957809931873)
            ·
              refine ⟨42424991450932468357448905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56566655267909957809931873 42424991450932468357448905)
              ·
                refine ⟨31818743588199351268086679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42424991450932468357448905 31818743588199351268086679)
                ·
                  refine ⟨47728115382299026902130019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31818743588199351268086679 47728115382299026902130019)
                  ·
                    refine ⟨71592173073448540353195029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47728115382299026902130019 71592173073448540353195029)
                    ·
                      refine ⟨3355883112817900329056017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71592173073448540353195029 3355883112817900329056017)
                      ·
                        rfl

theorem cell23_6535559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_6535559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535559 prefixEnd_6535559 := by exact prefixLift 6535559
  have htrace : WordTrace (prefixWord ++ tailWord_6535559) baseStart_6535559 baseEnd_6535559 := by
    simpa [prefixWord, tailWord_6535559, baseEnd_6535559] using wordTrace_append hprefix tailTrace_6535559
  have hstable : (prefixWord ++ tailWord_6535559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535559).length < 2 ^ (prefixWord ++ tailWord_6535559).sum := by decide
  have hdescent : baseEnd_6535559 < baseStart_6535559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535563 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 3, 2, 2]
def baseStart_6535563 : Nat := 118140960795 + 6535563 * 2 ^ 59
def prefixEnd_6535563 : Nat := 4983230072969 + 3 ^ 40 * 6535563 * 2
def baseEnd_6535563 : Nat := 3355885166740518313405999

theorem tailTrace_6535563 : CollatzResearch.WordTrace tailWord_6535563 prefixEnd_6535563 3355885166740518313405999 := by
  unfold tailWord_6535563
  simp only [CollatzResearch.WordTrace]
  refine ⟨238371565621778911141459343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158914377081185940760972895 238371565621778911141459343)
  ·
    refine ⟨357557348432668366712189015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238371565621778911141459343 357557348432668366712189015)
    ·
      refine ⟨536336022649002550068283523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357557348432668366712189015 536336022649002550068283523)
      ·
        refine ⟨804504033973503825102425285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536336022649002550068283523 804504033973503825102425285)
        ·
          refine ⟨150844506370031967206704741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 804504033973503825102425285 150844506370031967206704741)
          ·
            refine ⟨28283344944380993851257139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150844506370031967206704741 28283344944380993851257139)
            ·
              refine ⟨42425017416571490776885709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28283344944380993851257139 42425017416571490776885709)
              ·
                refine ⟨15909381531214309041332141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42425017416571490776885709 15909381531214309041332141)
                ·
                  refine ⟨5966018074205365890499553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15909381531214309041332141 5966018074205365890499553)
                  ·
                    refine ⟨4474513555654024417874665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966018074205365890499553 4474513555654024417874665)
                    ·
                      refine ⟨3355885166740518313405999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474513555654024417874665 3355885166740518313405999)
                      ·
                        rfl

theorem cell23_6535563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 3, 2, 2].length) (baseStart_6535563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535563 prefixEnd_6535563 := by exact prefixLift 6535563
  have htrace : WordTrace (prefixWord ++ tailWord_6535563) baseStart_6535563 baseEnd_6535563 := by
    simpa [prefixWord, tailWord_6535563, baseEnd_6535563] using wordTrace_append hprefix tailTrace_6535563
  have hstable : (prefixWord ++ tailWord_6535563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535563).length < 2 ^ (prefixWord ++ tailWord_6535563).sum := by decide
  have hdescent : baseEnd_6535563 < baseStart_6535563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535566 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6535566 : Nat := 118140960795 + 6535566 * 2 ^ 59
def prefixEnd_6535566 : Nat := 4983230072969 + 3 ^ 40 * 6535566 * 2
def baseEnd_6535566 : Nat := 3355886707182481801668485

theorem tailTrace_6535566 : CollatzResearch.WordTrace tailWord_6535566 prefixEnd_6535566 3355886707182481801668485 := by
  unfold tailWord_6535566
  simp only [CollatzResearch.WordTrace]
  refine ⟨29796459380096005331727319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158914450027178695102545701 29796459380096005331727319)
  ·
    refine ⟨44694689070144007997590979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29796459380096005331727319 44694689070144007997590979)
    ·
      refine ⟨67042033605216011996386469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44694689070144007997590979 67042033605216011996386469)
      ·
        refine ⟨12570381300978002249322463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67042033605216011996386469 12570381300978002249322463)
        ·
          refine ⟨18855571951467003373983695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12570381300978002249322463 18855571951467003373983695)
          ·
            refine ⟨28283357927200505060975543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18855571951467003373983695 28283357927200505060975543)
            ·
              refine ⟨42425036890800757591463315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28283357927200505060975543 42425036890800757591463315)
              ·
                refine ⟨63637555336201136387194973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42425036890800757591463315 63637555336201136387194973)
                ·
                  refine ⟨23864083251075426145198115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63637555336201136387194973 23864083251075426145198115)
                  ·
                    refine ⟨35796124876613139217797173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23864083251075426145198115 35796124876613139217797173)
                    ·
                      refine ⟨3355886707182481801668485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35796124876613139217797173 3355886707182481801668485)
                      ·
                        rfl

theorem cell23_6535566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6535566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535566 prefixEnd_6535566 := by exact prefixLift 6535566
  have htrace : WordTrace (prefixWord ++ tailWord_6535566) baseStart_6535566 baseEnd_6535566 := by
    simpa [prefixWord, tailWord_6535566, baseEnd_6535566] using wordTrace_append hprefix tailTrace_6535566
  have hstable : (prefixWord ++ tailWord_6535566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535566).length < 2 ^ (prefixWord ++ tailWord_6535566).sum := by decide
  have hdescent : baseEnd_6535566 < baseStart_6535566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535576 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6535576 : Nat := 118140960795 + 6535576 * 2 ^ 59
def prefixEnd_6535576 : Nat := 4983230072969 + 3 ^ 40 * 6535576 * 2
def baseEnd_6535576 : Nat := 3355891841989026762543439

theorem tailTrace_6535576 : CollatzResearch.WordTrace tailWord_6535576 prefixEnd_6535576 3355891841989026762543439 := by
  unfold tailWord_6535576
  simp only [CollatzResearch.WordTrace]
  refine ⟨119186019885365907180841291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158914693180487876241121721 119186019885365907180841291)
  ·
    refine ⟨178779029828048860771261937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119186019885365907180841291 178779029828048860771261937)
    ·
      refine ⟨134084272371036645578446453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178779029828048860771261937 134084272371036645578446453)
      ·
        refine ⟨12570400534784685522979355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134084272371036645578446453 12570400534784685522979355)
        ·
          refine ⟨18855600802177028284469033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12570400534784685522979355 18855600802177028284469033)
          ·
            refine ⟨14141700601632771213351775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18855600802177028284469033 14141700601632771213351775)
            ·
              refine ⟨21212550902449156820027663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14141700601632771213351775 21212550902449156820027663)
              ·
                refine ⟨31818826353673735230041495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21212550902449156820027663 31818826353673735230041495)
                ·
                  refine ⟨47728239530510602845062243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31818826353673735230041495 47728239530510602845062243)
                  ·
                    refine ⟨71592359295765904267593365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47728239530510602845062243 71592359295765904267593365)
                    ·
                      refine ⟨3355891841989026762543439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71592359295765904267593365 3355891841989026762543439)
                      ·
                        rfl

theorem cell23_6535576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6535576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535576 prefixEnd_6535576 := by exact prefixLift 6535576
  have htrace : WordTrace (prefixWord ++ tailWord_6535576) baseStart_6535576 baseEnd_6535576 := by
    simpa [prefixWord, tailWord_6535576, baseEnd_6535576] using wordTrace_append hprefix tailTrace_6535576
  have hstable : (prefixWord ++ tailWord_6535576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535576).length < 2 ^ (prefixWord ++ tailWord_6535576).sum := by decide
  have hdescent : baseEnd_6535576 < baseStart_6535576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535583 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6535583 : Nat := 118140960795 + 6535583 * 2 ^ 59
def prefixEnd_6535583 : Nat := 4983230072969 + 3 ^ 40 * 6535583 * 2
def baseEnd_6535583 : Nat := 3355895436353608235155907

theorem tailTrace_6535583 : CollatzResearch.WordTrace tailWord_6535583 prefixEnd_6535583 3355895436353608235155907 := by
  unfold tailWord_6535583
  simp only [CollatzResearch.WordTrace]
  refine ⟨238372295081706454557187403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158914863387804303038124935 238372295081706454557187403)
  ·
    refine ⟨357558442622559681835781105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238372295081706454557187403 357558442622559681835781105)
    ·
      refine ⟨268168831966919761376835829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357558442622559681835781105 268168831966919761376835829)
      ·
        refine ⟨25140827996898727629078359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268168831966919761376835829 25140827996898727629078359)
        ·
          refine ⟨37711241995348091443617539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25140827996898727629078359 37711241995348091443617539)
          ·
            refine ⟨56566862993022137165426309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37711241995348091443617539 56566862993022137165426309)
            ·
              refine ⟨10606286811191650718517433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56566862993022137165426309 10606286811191650718517433)
              ·
                refine ⟨7954715108393738038888075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606286811191650718517433 7954715108393738038888075)
                ·
                  refine ⟨11932072662590607058332113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954715108393738038888075 11932072662590607058332113)
                  ·
                    refine ⟨8949054496942955293749085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11932072662590607058332113 8949054496942955293749085)
                    ·
                      refine ⟨3355895436353608235155907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8949054496942955293749085 3355895436353608235155907)
                      ·
                        rfl

theorem cell23_6535583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6535583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535583 prefixEnd_6535583 := by exact prefixLift 6535583
  have htrace : WordTrace (prefixWord ++ tailWord_6535583) baseStart_6535583 baseEnd_6535583 := by
    simpa [prefixWord, tailWord_6535583, baseEnd_6535583] using wordTrace_append hprefix tailTrace_6535583
  have hstable : (prefixWord ++ tailWord_6535583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535583).length < 2 ^ (prefixWord ++ tailWord_6535583).sum := by decide
  have hdescent : baseEnd_6535583 < baseStart_6535583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535613 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6535613 : Nat := 118140960795 + 6535613 * 2 ^ 59
def prefixEnd_6535613 : Nat := 4983230072969 + 3 ^ 40 * 6535613 * 2
def baseEnd_6535613 : Nat := 3355910840773243117780769

theorem tailTrace_6535613 : CollatzResearch.WordTrace tailWord_6535613 prefixEnd_6535613 3355910840773243117780769 := by
  unfold tailWord_6535613
  simp only [CollatzResearch.WordTrace]
  refine ⟨238373389271597769680779493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158915592847731846453852995 238373389271597769680779493)
  ·
    refine ⟨44695010488424581815146155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238373389271597769680779493 44695010488424581815146155)
    ·
      refine ⟨67042515732636872722719233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44695010488424581815146155 67042515732636872722719233)
      ·
        refine ⟨50281886799477654542039425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67042515732636872722719233 50281886799477654542039425)
        ·
          refine ⟨37711415099608240906529569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50281886799477654542039425 37711415099608240906529569)
          ·
            refine ⟨28283561324706180679897177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37711415099608240906529569 28283561324706180679897177)
            ·
              refine ⟨21212670993529635509922883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28283561324706180679897177 21212670993529635509922883)
              ·
                refine ⟨31819006490294453264884325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21212670993529635509922883 31819006490294453264884325)
                ·
                  refine ⟨5966063716930209987165811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31819006490294453264884325 5966063716930209987165811)
                  ·
                    refine ⟨8949095575395314980748717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966063716930209987165811 8949095575395314980748717)
                    ·
                      refine ⟨3355910840773243117780769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8949095575395314980748717 3355910840773243117780769)
                      ·
                        rfl

theorem cell23_6535613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6535613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535613 prefixEnd_6535613 := by exact prefixLift 6535613
  have htrace : WordTrace (prefixWord ++ tailWord_6535613) baseStart_6535613 baseEnd_6535613 := by
    simpa [prefixWord, tailWord_6535613, baseEnd_6535613] using wordTrace_append hprefix tailTrace_6535613
  have hstable : (prefixWord ++ tailWord_6535613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535613).length < 2 ^ (prefixWord ++ tailWord_6535613).sum := by decide
  have hdescent : baseEnd_6535613 < baseStart_6535613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535619 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_6535619 : Nat := 118140960795 + 6535619 * 2 ^ 59
def prefixEnd_6535619 : Nat := 4983230072969 + 3 ^ 40 * 6535619 * 2
def baseEnd_6535619 : Nat := 3355913921657170094305741

theorem tailTrace_6535619 : CollatzResearch.WordTrace tailWord_6535619 prefixEnd_6535619 3355913921657170094305741 := by
  unfold tailWord_6535619
  simp only [CollatzResearch.WordTrace]
  refine ⟨238373608109576032705497911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158915738739717355136998607 238373608109576032705497911)
  ·
    refine ⟨357560412164364049058246867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238373608109576032705497911 357560412164364049058246867)
    ·
      refine ⟨536340618246546073587370301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357560412164364049058246867 536340618246546073587370301)
      ·
        refine ⟨201127731842454777595263863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536340618246546073587370301 201127731842454777595263863)
        ·
          refine ⟨301691597763682166392895795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201127731842454777595263863 301691597763682166392895795)
          ·
            refine ⟨452537396645523249589343693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301691597763682166392895795 452537396645523249589343693)
            ·
              refine ⟨169701523742071218596003885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452537396645523249589343693 169701523742071218596003885)
              ·
                refine ⟨63638071403276706973501457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169701523742071218596003885 63638071403276706973501457)
                ·
                  refine ⟨47728553552457530230126093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63638071403276706973501457 47728553552457530230126093)
                  ·
                    refine ⟨17898207582171573836297285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47728553552457530230126093 17898207582171573836297285)
                    ·
                      refine ⟨3355913921657170094305741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17898207582171573836297285 3355913921657170094305741)
                      ·
                        rfl

theorem cell23_6535619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_6535619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535619 prefixEnd_6535619 := by exact prefixLift 6535619
  have htrace : WordTrace (prefixWord ++ tailWord_6535619) baseStart_6535619 baseEnd_6535619 := by
    simpa [prefixWord, tailWord_6535619, baseEnd_6535619] using wordTrace_append hprefix tailTrace_6535619
  have hstable : (prefixWord ++ tailWord_6535619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535619).length < 2 ^ (prefixWord ++ tailWord_6535619).sum := by decide
  have hdescent : baseEnd_6535619 < baseStart_6535619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535634 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6535634 : Nat := 118140960795 + 6535634 * 2 ^ 59
def prefixEnd_6535634 : Nat := 4983230072969 + 3 ^ 40 * 6535634 * 2
def baseEnd_6535634 : Nat := 3355921623866987535618173

theorem tailTrace_6535634 : CollatzResearch.WordTrace tailWord_6535634 prefixEnd_6535634 3355921623866987535618173 := by
  unfold tailWord_6535634
  simp only [CollatzResearch.WordTrace]
  refine ⟨59593538801130422566823489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158916103469681126844862637 59593538801130422566823489)
  ·
    refine ⟨44695154100847816925117617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59593538801130422566823489 44695154100847816925117617)
    ·
      refine ⟨33521365575635862693838213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44695154100847816925117617 33521365575635862693838213)
      ·
        refine ⟨6285256045431724255094665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33521365575635862693838213 6285256045431724255094665)
        ·
          refine ⟨4713942034073793191320999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6285256045431724255094665 4713942034073793191320999)
          ·
            refine ⟨7070913051110689786981499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713942034073793191320999 7070913051110689786981499)
            ·
              refine ⟨10606369576666034680472249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070913051110689786981499 10606369576666034680472249)
              ·
                refine ⟨7954777182499526010354187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606369576666034680472249 7954777182499526010354187)
                ·
                  refine ⟨11932165773749289015531281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7954777182499526010354187 11932165773749289015531281)
                  ·
                    refine ⟨8949124330311966761648461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11932165773749289015531281 8949124330311966761648461)
                    ·
                      refine ⟨3355921623866987535618173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8949124330311966761648461 3355921623866987535618173)
                      ·
                        rfl

theorem cell23_6535634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6535634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535634 prefixEnd_6535634 := by exact prefixLift 6535634
  have htrace : WordTrace (prefixWord ++ tailWord_6535634) baseStart_6535634 baseEnd_6535634 := by
    simpa [prefixWord, tailWord_6535634, baseEnd_6535634] using wordTrace_append hprefix tailTrace_6535634
  have hstable : (prefixWord ++ tailWord_6535634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535634).length < 2 ^ (prefixWord ++ tailWord_6535634).sum := by decide
  have hdescent : baseEnd_6535634 < baseStart_6535634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535656 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6535656 : Nat := 118140960795 + 6535656 * 2 ^ 59
def prefixEnd_6535656 : Nat := 4983230072969 + 3 ^ 40 * 6535656 * 2
def baseEnd_6535656 : Nat := 3355932920441386449543071

theorem tailTrace_6535656 : CollatzResearch.WordTrace tailWord_6535656 prefixEnd_6535656 3355932920441386449543071 := by
  unfold tailWord_6535656
  simp only [CollatzResearch.WordTrace]
  refine ⟨119187478805220994012297411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158916638406961325349729881 119187478805220994012297411)
  ·
    refine ⟨178781218207831491018446117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119187478805220994012297411 178781218207831491018446117)
    ·
      refine ⟨33521478413968404565958647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178781218207831491018446117 33521478413968404565958647)
      ·
        refine ⟨50282217620952606848937971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33521478413968404565958647 50282217620952606848937971)
        ·
          refine ⟨75423326431428910273406957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50282217620952606848937971 75423326431428910273406957)
          ·
            refine ⟨28283747411785841352527609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75423326431428910273406957 28283747411785841352527609)
            ·
              refine ⟨21212810558839381014395707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28283747411785841352527609 21212810558839381014395707)
              ·
                refine ⟨31819215838259071521593561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21212810558839381014395707 31819215838259071521593561)
                ·
                  refine ⟨23864411878694303641195171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31819215838259071521593561 23864411878694303641195171)
                  ·
                    refine ⟨35796617818041455461792757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23864411878694303641195171 35796617818041455461792757)
                    ·
                      refine ⟨3355932920441386449543071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35796617818041455461792757 3355932920441386449543071)
                      ·
                        rfl

theorem cell23_6535656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6535656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535656 prefixEnd_6535656 := by exact prefixLift 6535656
  have htrace : WordTrace (prefixWord ++ tailWord_6535656) baseStart_6535656 baseEnd_6535656 := by
    simpa [prefixWord, tailWord_6535656, baseEnd_6535656] using wordTrace_append hprefix tailTrace_6535656
  have hstable : (prefixWord ++ tailWord_6535656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535656).length < 2 ^ (prefixWord ++ tailWord_6535656).sum := by decide
  have hdescent : baseEnd_6535656 < baseStart_6535656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535743 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 2, 4, 2]
def baseStart_6535743 : Nat := 118140960795 + 6535743 * 2 ^ 59
def prefixEnd_6535743 : Nat := 4983230072969 + 3 ^ 40 * 6535743 * 2
def baseEnd_6535743 : Nat := 3355977593258327609155171

theorem tailTrace_6535743 : CollatzResearch.WordTrace tailWord_6535743 prefixEnd_6535743 3355977593258327609155171 := by
  unfold tailWord_6535743
  simp only [CollatzResearch.WordTrace]
  refine ⟨238378130761126801883011883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158918753840751201255341255 238378130761126801883011883)
  ·
    refine ⟨357567196141690202824517825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238378130761126801883011883 357567196141690202824517825)
    ·
      refine ⟨268175397106267652118388369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357567196141690202824517825 268175397106267652118388369)
      ·
        refine ⟨201131547829700739088791277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268175397106267652118388369 201131547829700739088791277)
        ·
          refine ⟨75424330436137777158296729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201131547829700739088791277 75424330436137777158296729)
          ·
            refine ⟨56568247827103332868722547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75424330436137777158296729 56568247827103332868722547)
            ·
              refine ⟨84852371740654999303083821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56568247827103332868722547 84852371740654999303083821)
              ·
                refine ⟨31819639402745624738656433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84852371740654999303083821 31819639402745624738656433)
                ·
                  refine ⟨23864729552059218553992325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31819639402745624738656433 23864729552059218553992325)
                  ·
                    refine ⟨4474636791011103478873561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23864729552059218553992325 4474636791011103478873561)
                    ·
                      refine ⟨3355977593258327609155171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474636791011103478873561 3355977593258327609155171)
                      ·
                        rfl

theorem cell23_6535743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_6535743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535743 prefixEnd_6535743 := by exact prefixLift 6535743
  have htrace : WordTrace (prefixWord ++ tailWord_6535743) baseStart_6535743 baseEnd_6535743 := by
    simpa [prefixWord, tailWord_6535743, baseEnd_6535743] using wordTrace_append hprefix tailTrace_6535743
  have hstable : (prefixWord ++ tailWord_6535743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535743).length < 2 ^ (prefixWord ++ tailWord_6535743).sum := by decide
  have hdescent : baseEnd_6535743 < baseStart_6535743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535756 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6535756 : Nat := 118140960795 + 6535756 * 2 ^ 59
def prefixEnd_6535756 : Nat := 4983230072969 + 3 ^ 40 * 6535756 * 2
def baseEnd_6535756 : Nat := 3355984268506836058292611

theorem tailTrace_6535756 : CollatzResearch.WordTrace tailWord_6535756 prefixEnd_6535756 3355984268506836058292611 := by
  unfold tailWord_6535756
  simp only [CollatzResearch.WordTrace]
  refine ⟨119189302455039852551617561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158919069940053136735490081 119189302455039852551617561)
  ·
    refine ⟨89391976841279889413713171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119189302455039852551617561 89391976841279889413713171)
    ·
      refine ⟨134087965261919834120569757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89391976841279889413713171 134087965261919834120569757)
      ·
        refine ⟨50282986973219937795213659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134087965261919834120569757 50282986973219937795213659)
        ·
          refine ⟨75424480459829906692820489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50282986973219937795213659 75424480459829906692820489)
          ·
            refine ⟨56568360344872430019615367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75424480459829906692820489 56568360344872430019615367)
            ·
              refine ⟨84852540517308645029423051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56568360344872430019615367 84852540517308645029423051)
              ·
                refine ⟨127278810775962967544134577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84852540517308645029423051 127278810775962967544134577)
                ·
                  refine ⟨95459108081972225658100933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127278810775962967544134577 95459108081972225658100933)
                  ·
                    refine ⟨17898582765369792310893925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95459108081972225658100933 17898582765369792310893925)
                    ·
                      refine ⟨3355984268506836058292611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17898582765369792310893925 3355984268506836058292611)
                      ·
                        rfl

theorem cell23_6535756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6535756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535756 prefixEnd_6535756 := by exact prefixLift 6535756
  have htrace : WordTrace (prefixWord ++ tailWord_6535756) baseStart_6535756 baseEnd_6535756 := by
    simpa [prefixWord, tailWord_6535756, baseEnd_6535756] using wordTrace_append hprefix tailTrace_6535756
  have hstable : (prefixWord ++ tailWord_6535756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535756).length < 2 ^ (prefixWord ++ tailWord_6535756).sum := by decide
  have hdescent : baseEnd_6535756 < baseStart_6535756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535774 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6535774 : Nat := 118140960795 + 6535774 * 2 ^ 59
def prefixEnd_6535774 : Nat := 4983230072969 + 3 ^ 40 * 6535774 * 2
def baseEnd_6535774 : Nat := 1118664503719538995955843

theorem tailTrace_6535774 : CollatzResearch.WordTrace tailWord_6535774 prefixEnd_6535774 1118664503719538995955843 := by
  unfold tailWord_6535774
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797407678001811772173797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158919507616009662784926917 29797407678001811772173797)
  ·
    refine ⟨5587013939625339707282587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29797407678001811772173797 5587013939625339707282587)
    ·
      refine ⟨8380520909438009560923881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587013939625339707282587 8380520909438009560923881)
      ·
        refine ⟨6285390682078507170692911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8380520909438009560923881 6285390682078507170692911)
        ·
          refine ⟨9428086023117760756039367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285390682078507170692911 9428086023117760756039367)
          ·
            refine ⟨14142129034676641134059051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9428086023117760756039367 14142129034676641134059051)
            ·
              refine ⟨21213193552014961701088577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14142129034676641134059051 21213193552014961701088577)
              ·
                refine ⟨15909895164011221275816433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21213193552014961701088577 15909895164011221275816433)
                ·
                  refine ⟨11932421373008415956862325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15909895164011221275816433 11932421373008415956862325)
                  ·
                    refine ⟨1118664503719538995955843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11932421373008415956862325 1118664503719538995955843)
                    ·
                      rfl

theorem cell23_6535774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6535774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535774 prefixEnd_6535774 := by exact prefixLift 6535774
  have htrace : WordTrace (prefixWord ++ tailWord_6535774) baseStart_6535774 baseEnd_6535774 := by
    simpa [prefixWord, tailWord_6535774, baseEnd_6535774] using wordTrace_append hprefix tailTrace_6535774
  have hstable : (prefixWord ++ tailWord_6535774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535774).length < 2 ^ (prefixWord ++ tailWord_6535774).sum := by decide
  have hdescent : baseEnd_6535774 < baseStart_6535774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535803 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 5, 2]
def baseStart_6535803 : Nat := 118140960795 + 6535803 * 2 ^ 59
def prefixEnd_6535803 : Nat := 4983230072969 + 3 ^ 40 * 6535803 * 2
def baseEnd_6535803 : Nat := 3356008402097597374404895

theorem tailTrace_6535803 : CollatzResearch.WordTrace tailWord_6535803 prefixEnd_6535803 3356008402097597374404895 := by
  unfold tailWord_6535803
  simp only [CollatzResearch.WordTrace]
  refine ⟨238380319140909432130196063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158920212760606288086797375 238380319140909432130196063)
  ·
    refine ⟨357570478711364148195294095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238380319140909432130196063 357570478711364148195294095)
    ·
      refine ⟨536355718067046222292941143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357570478711364148195294095 536355718067046222292941143)
      ·
        refine ⟨804533577100569333439411715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536355718067046222292941143 804533577100569333439411715)
        ·
          refine ⟨1206800365650854000159117573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804533577100569333439411715 1206800365650854000159117573)
          ·
            refine ⟨226275068559535125029834545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1206800365650854000159117573 226275068559535125029834545)
            ·
              refine ⟨169706301419651343772375909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226275068559535125029834545 169706301419651343772375909)
              ·
                refine ⟨31819931516184626957320483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169706301419651343772375909 31819931516184626957320483)
                ·
                  refine ⟨47729897274276940435980725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31819931516184626957320483 47729897274276940435980725)
                  ·
                    refine ⟨4474677869463463165873193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47729897274276940435980725 4474677869463463165873193)
                    ·
                      refine ⟨3356008402097597374404895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474677869463463165873193 3356008402097597374404895)
                      ·
                        rfl

theorem cell23_6535803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 5, 2].length) (baseStart_6535803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535803 prefixEnd_6535803 := by exact prefixLift 6535803
  have htrace : WordTrace (prefixWord ++ tailWord_6535803) baseStart_6535803 baseEnd_6535803 := by
    simpa [prefixWord, tailWord_6535803, baseEnd_6535803] using wordTrace_append hprefix tailTrace_6535803
  have hstable : (prefixWord ++ tailWord_6535803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535803).length < 2 ^ (prefixWord ++ tailWord_6535803).sum := by decide
  have hdescent : baseEnd_6535803 < baseStart_6535803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535813 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_6535813 : Nat := 118140960795 + 6535813 * 2 ^ 59
def prefixEnd_6535813 : Nat := 4983230072969 + 3 ^ 40 * 6535813 * 2
def baseEnd_6535813 : Nat := 1118671178968047445093283

theorem tailTrace_6535813 : CollatzResearch.WordTrace tailWord_6535813 prefixEnd_6535813 1118671178968047445093283 := by
  unfold tailWord_6535813
  simp only [CollatzResearch.WordTrace]
  refine ⟨238380683870873203838060093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158920455913915469225373395 238380683870873203838060093)
  ·
    refine ⟨89392756451577451439272535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238380683870873203838060093 89392756451577451439272535)
    ·
      refine ⟨134089134677366177158908803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89392756451577451439272535 134089134677366177158908803)
      ·
        refine ⟨201133702016049265738363205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134089134677366177158908803 201133702016049265738363205)
        ·
          refine ⟨37712569128009237325943101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201133702016049265738363205 37712569128009237325943101)
          ·
            refine ⟨14142213423003463997228663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37712569128009237325943101 14142213423003463997228663)
            ·
              refine ⟨21213320134505195995842995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14142213423003463997228663 21213320134505195995842995)
              ·
                refine ⟨31819980201757793993764493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21213320134505195995842995 31819980201757793993764493)
                ·
                  refine ⟨11932492575659172747661685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31819980201757793993764493 11932492575659172747661685)
                  ·
                    refine ⟨1118671178968047445093283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11932492575659172747661685 1118671178968047445093283)
                    ·
                      rfl

theorem cell23_6535813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_6535813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535813 prefixEnd_6535813 := by exact prefixLift 6535813
  have htrace : WordTrace (prefixWord ++ tailWord_6535813) baseStart_6535813 baseEnd_6535813 := by
    simpa [prefixWord, tailWord_6535813, baseEnd_6535813] using wordTrace_append hprefix tailTrace_6535813
  have hstable : (prefixWord ++ tailWord_6535813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535813).length < 2 ^ (prefixWord ++ tailWord_6535813).sum := by decide
  have hdescent : baseEnd_6535813 < baseStart_6535813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535870 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_6535870 : Nat := 118140960795 + 6535870 * 2 ^ 59
def prefixEnd_6535870 : Nat := 4983230072969 + 3 ^ 40 * 6535870 * 2
def baseEnd_6535870 : Nat := 3356042805301448612267087

theorem tailTrace_6535870 : CollatzResearch.WordTrace tailWord_6535870 prefixEnd_6535870 3356042805301448612267087 := by
  unfold tailWord_6535870
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797845353958337821610633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158921841887777801715256709 29797845353958337821610633)
  ·
    refine ⟨22348384015468753366207975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29797845353958337821610633 22348384015468753366207975)
    ·
      refine ⟨33522576023203130049311963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22348384015468753366207975 33522576023203130049311963)
      ·
        refine ⟨50283864034804695073967945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33522576023203130049311963 50283864034804695073967945)
        ·
          refine ⟨37712898026103521305475959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50283864034804695073967945 37712898026103521305475959)
          ·
            refine ⟨56569347039155281958213939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37712898026103521305475959 56569347039155281958213939)
            ·
              refine ⟨84854020558732922937320909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56569347039155281958213939 84854020558732922937320909)
              ·
                refine ⟨31820257709524846101495341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84854020558732922937320909 31820257709524846101495341)
                ·
                  refine ⟨11932596641071817288060753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31820257709524846101495341 11932596641071817288060753)
                  ·
                    refine ⟨8949447480803862966045565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11932596641071817288060753 8949447480803862966045565)
                    ·
                      refine ⟨3356042805301448612267087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8949447480803862966045565 3356042805301448612267087)
                      ·
                        rfl

theorem cell23_6535870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_6535870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535870 prefixEnd_6535870 := by exact prefixLift 6535870
  have htrace : WordTrace (prefixWord ++ tailWord_6535870) baseStart_6535870 baseEnd_6535870 := by
    simpa [prefixWord, tailWord_6535870, baseEnd_6535870] using wordTrace_append hprefix tailTrace_6535870
  have hstable : (prefixWord ++ tailWord_6535870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535870).length < 2 ^ (prefixWord ++ tailWord_6535870).sum := by decide
  have hdescent : baseEnd_6535870 < baseStart_6535870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535884 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6535884 : Nat := 118140960795 + 6535884 * 2 ^ 59
def prefixEnd_6535884 : Nat := 4983230072969 + 3 ^ 40 * 6535884 * 2
def baseEnd_6535884 : Nat := 3356049994030611557492023

theorem tailTrace_6535884 : CollatzResearch.WordTrace tailWord_6535884 prefixEnd_6535884 3356049994030611557492023 := by
  unfold tailWord_6535884
  simp only [CollatzResearch.WordTrace]
  refine ⟨119191636726807991481947353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158922182302410655309263137 119191636726807991481947353)
  ·
    refine ⟨89393727545105993611460515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119191636726807991481947353 89393727545105993611460515)
    ·
      refine ⟨134090591317658990417190773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89393727545105993611460515 134090591317658990417190773)
      ·
        refine ⟨12570992936030530351611635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134090591317658990417190773 12570992936030530351611635)
        ·
          refine ⟨18856489404045795527417453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12570992936030530351611635 18856489404045795527417453)
          ·
            refine ⟨7071183526517173322781545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18856489404045795527417453 7071183526517173322781545)
            ·
              refine ⟨5303387644887879992086159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071183526517173322781545 5303387644887879992086159)
              ·
                refine ⟨7955081467331819988129239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303387644887879992086159 7955081467331819988129239)
                ·
                  refine ⟨11932622200997729982193859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7955081467331819988129239 11932622200997729982193859)
                  ·
                    refine ⟨17898933301496594973290789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11932622200997729982193859 17898933301496594973290789)
                    ·
                      refine ⟨3356049994030611557492023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17898933301496594973290789 3356049994030611557492023)
                      ·
                        rfl

theorem cell23_6535884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6535884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535884 prefixEnd_6535884 := by exact prefixLift 6535884
  have htrace : WordTrace (prefixWord ++ tailWord_6535884) baseStart_6535884 baseEnd_6535884 := by
    simpa [prefixWord, tailWord_6535884, baseEnd_6535884] using wordTrace_append hprefix tailTrace_6535884
  have hstable : (prefixWord ++ tailWord_6535884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535884).length < 2 ^ (prefixWord ++ tailWord_6535884).sum := by decide
  have hdescent : baseEnd_6535884 < baseStart_6535884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535953 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_6535953 : Nat := 118140960795 + 6535953 * 2 ^ 59
def prefixEnd_6535953 : Nat := 4983230072969 + 3 ^ 40 * 6535953 * 2
def baseEnd_6535953 : Nat := 3356085424195771787529205

theorem tailTrace_6535953 : CollatzResearch.WordTrace tailWord_6535953 prefixEnd_6535953 3356085424195771787529205 := by
  unfold tailWord_6535953
  simp only [CollatzResearch.WordTrace]
  refine ⟨238385790090366007748156513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158923860060244005165437675 238385790090366007748156513)
  ·
    refine ⟨178789342567774505811117385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238385790090366007748156513 178789342567774505811117385)
    ·
      refine ⟨134092006925830879358338039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178789342567774505811117385 134092006925830879358338039)
      ·
        refine ⟨201138010388746319037507059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134092006925830879358338039 201138010388746319037507059)
        ·
          refine ⟨301707015583119478556260589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201138010388746319037507059 301707015583119478556260589)
          ·
            refine ⟨113140130843669804458597721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301707015583119478556260589 113140130843669804458597721)
            ·
              refine ⟨84855098132752353343948291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113140130843669804458597721 84855098132752353343948291)
              ·
                refine ⟨127282647199128530015922437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84855098132752353343948291 127282647199128530015922437)
                ·
                  refine ⟨23865496349836599377985457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127282647199128530015922437 23865496349836599377985457)
                  ·
                    refine ⟨17899122262377449533489093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23865496349836599377985457 17899122262377449533489093)
                    ·
                      refine ⟨3356085424195771787529205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17899122262377449533489093 3356085424195771787529205)
                      ·
                        rfl

theorem cell23_6535953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_6535953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535953 prefixEnd_6535953 := by exact prefixLift 6535953
  have htrace : WordTrace (prefixWord ++ tailWord_6535953) baseStart_6535953 baseEnd_6535953 := by
    simpa [prefixWord, tailWord_6535953, baseEnd_6535953] using wordTrace_append hprefix tailTrace_6535953
  have hstable : (prefixWord ++ tailWord_6535953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535953).length < 2 ^ (prefixWord ++ tailWord_6535953).sum := by decide
  have hdescent : baseEnd_6535953 < baseStart_6535953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535957 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_6535957 : Nat := 118140960795 + 6535957 * 2 ^ 59
def prefixEnd_6535957 : Nat := 4983230072969 + 3 ^ 40 * 6535957 * 2
def baseEnd_6535957 : Nat := 3356087478118389771879187

theorem tailTrace_6535957 : CollatzResearch.WordTrace tailWord_6535957 prefixEnd_6535957 3356087478118389771879187 := by
  unfold tailWord_6535957
  simp only [CollatzResearch.WordTrace]
  refine ⟨238385935982351516431302125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158923957321567677620868083 238385935982351516431302125)
  ·
    refine ⟨89394725993381818661738297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238385935982351516431302125 89394725993381818661738297)
    ·
      refine ⟨67046044495036363996303723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89394725993381818661738297 67046044495036363996303723)
      ·
        refine ⟨100569066742554545994455585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67046044495036363996303723 100569066742554545994455585)
        ·
          refine ⟨75426800056915909495841689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100569066742554545994455585 75426800056915909495841689)
          ·
            refine ⟨56570100042686932121881267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75426800056915909495841689 56570100042686932121881267)
            ·
              refine ⟨84855150064030398182821901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56570100042686932121881267 84855150064030398182821901)
              ·
                refine ⟨31820681274011399318558213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84855150064030398182821901 31820681274011399318558213)
                ·
                  refine ⟨5966377738877137372229665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31820681274011399318558213 5966377738877137372229665)
                  ·
                    refine ⟨4474783304157853029172249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966377738877137372229665 4474783304157853029172249)
                    ·
                      refine ⟨3356087478118389771879187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474783304157853029172249 3356087478118389771879187)
                      ·
                        rfl

theorem cell23_6535957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_6535957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535957 prefixEnd_6535957 := by exact prefixLift 6535957
  have htrace : WordTrace (prefixWord ++ tailWord_6535957) baseStart_6535957 baseEnd_6535957 := by
    simpa [prefixWord, tailWord_6535957, baseEnd_6535957] using wordTrace_append hprefix tailTrace_6535957
  have hstable : (prefixWord ++ tailWord_6535957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535957).length < 2 ^ (prefixWord ++ tailWord_6535957).sum := by decide
  have hdescent : baseEnd_6535957 < baseStart_6535957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6535978 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6535978 : Nat := 118140960795 + 6535978 * 2 ^ 59
def prefixEnd_6535978 : Nat := 4983230072969 + 3 ^ 40 * 6535978 * 2
def baseEnd_6535978 : Nat := 3356098261212134189716591

theorem tailTrace_6535978 : CollatzResearch.WordTrace tailWord_6535978 prefixEnd_6535978 3356098261212134189716591 := by
  unfold tailWord_6535978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596675478818859254454147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158924467943516958011877725 59596675478818859254454147)
  ·
    refine ⟨89395013218228288881681221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59596675478818859254454147 89395013218228288881681221)
    ·
      refine ⟨16761564978417804165315229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89395013218228288881681221 16761564978417804165315229)
      ·
        refine ⟨6285586866906676561993211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16761564978417804165315229 6285586866906676561993211)
        ·
          refine ⟨9428380300360014842989817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285586866906676561993211 9428380300360014842989817)
          ·
            refine ⟨7071285225270011132242363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9428380300360014842989817 7071285225270011132242363)
            ·
              refine ⟨10606927837905016698363545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7071285225270011132242363 10606927837905016698363545)
              ·
                refine ⟨7955195878428762523772659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606927837905016698363545 7955195878428762523772659)
                ·
                  refine ⟨11932793817643143785658989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7955195878428762523772659 11932793817643143785658989)
                  ·
                    refine ⟨4474797681616178919622121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11932793817643143785658989 4474797681616178919622121)
                    ·
                      refine ⟨3356098261212134189716591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474797681616178919622121 3356098261212134189716591)
                      ·
                        rfl

theorem cell23_6535978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6535978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6535978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6535978 prefixEnd_6535978 := by exact prefixLift 6535978
  have htrace : WordTrace (prefixWord ++ tailWord_6535978) baseStart_6535978 baseEnd_6535978 := by
    simpa [prefixWord, tailWord_6535978, baseEnd_6535978] using wordTrace_append hprefix tailTrace_6535978
  have hstable : (prefixWord ++ tailWord_6535978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6535978).length < 2 ^ (prefixWord ++ tailWord_6535978).sum := by decide
  have hdescent : baseEnd_6535978 < baseStart_6535978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6535978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536000 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2]
def baseStart_6536000 : Nat := 118140960795 + 6536000 * 2 ^ 59
def prefixEnd_6536000 : Nat := 4983230072969 + 3 ^ 40 * 6536000 * 2
def baseEnd_6536000 : Nat := 3356109557786533103641489

theorem tailTrace_6536000 : CollatzResearch.WordTrace tailWord_6536000 prefixEnd_6536000 3356109557786533103641489 := by
  unfold tailWord_6536000
  simp only [CollatzResearch.WordTrace]
  refine ⟨119193752160597867387558727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158925002880797156516744969 119193752160597867387558727)
  ·
    refine ⟨178790628240896801081338091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119193752160597867387558727 178790628240896801081338091)
    ·
      refine ⟨268185942361345201622007137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178790628240896801081338091 268185942361345201622007137)
      ·
        refine ⟨201139456771008901216505353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268185942361345201622007137 201139456771008901216505353)
        ·
          refine ⟨150854592578256675912379015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201139456771008901216505353 150854592578256675912379015)
          ·
            refine ⟨226281888867385013868568523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150854592578256675912379015 226281888867385013868568523)
            ·
              refine ⟨339422833301077520802852785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226281888867385013868568523 339422833301077520802852785)
              ·
                refine ⟨254567124975808140602139589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339422833301077520802852785 254567124975808140602139589)
                ·
                  refine ⟨47731335932964026362901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254567124975808140602139589 47731335932964026362901173)
                  ·
                    refine ⟨4474812743715377471521985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47731335932964026362901173 4474812743715377471521985)
                    ·
                      refine ⟨3356109557786533103641489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474812743715377471521985 3356109557786533103641489)
                      ·
                        rfl

theorem cell23_6536000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_6536000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536000 prefixEnd_6536000 := by exact prefixLift 6536000
  have htrace : WordTrace (prefixWord ++ tailWord_6536000) baseStart_6536000 baseEnd_6536000 := by
    simpa [prefixWord, tailWord_6536000, baseEnd_6536000] using wordTrace_append hprefix tailTrace_6536000
  have hstable : (prefixWord ++ tailWord_6536000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536000).length < 2 ^ (prefixWord ++ tailWord_6536000).sum := by decide
  have hdescent : baseEnd_6536000 < baseStart_6536000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536003 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_6536003 : Nat := 118140960795 + 6536003 * 2 ^ 59
def prefixEnd_6536003 : Nat := 4983230072969 + 3 ^ 40 * 6536003 * 2
def baseEnd_6536003 : Nat := 3356111098228496591903975

theorem tailTrace_6536003 : CollatzResearch.WordTrace tailWord_6536003 prefixEnd_6536003 3356111098228496591903975 := by
  unfold tailWord_6536003
  simp only [CollatzResearch.WordTrace]
  refine ⟨238387613740184866287476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158925075826789910858317775 238387613740184866287476663)
  ·
    refine ⟨357581420610277299431214995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238387613740184866287476663 357581420610277299431214995)
    ·
      refine ⟨536372130915415949146822493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357581420610277299431214995 536372130915415949146822493)
      ·
        refine ⟨201139549093280980930058435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536372130915415949146822493 201139549093280980930058435)
        ·
          refine ⟨301709323639921471395087653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201139549093280980930058435 301709323639921471395087653)
          ·
            refine ⟨56570498182485275886578935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301709323639921471395087653 56570498182485275886578935)
            ·
              refine ⟨84855747273727913829868403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56570498182485275886578935 84855747273727913829868403)
              ·
                refine ⟨127283620910591870744802605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84855747273727913829868403 127283620910591870744802605)
                ·
                  refine ⟨47731357841471951529300977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127283620910591870744802605 47731357841471951529300977)
                  ·
                    refine ⟨35798518381103963646975733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47731357841471951529300977 35798518381103963646975733)
                    ·
                      refine ⟨3356111098228496591903975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35798518381103963646975733 3356111098228496591903975)
                      ·
                        rfl

theorem cell23_6536003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_6536003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536003 prefixEnd_6536003 := by exact prefixLift 6536003
  have htrace : WordTrace (prefixWord ++ tailWord_6536003) baseStart_6536003 baseEnd_6536003 := by
    simpa [prefixWord, tailWord_6536003, baseEnd_6536003] using wordTrace_append hprefix tailTrace_6536003
  have hstable : (prefixWord ++ tailWord_6536003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536003).length < 2 ^ (prefixWord ++ tailWord_6536003).sum := by decide
  have hdescent : baseEnd_6536003 < baseStart_6536003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536074 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_6536074 : Nat := 118140960795 + 6536074 * 2 ^ 59
def prefixEnd_6536074 : Nat := 4983230072969 + 3 ^ 40 * 6536074 * 2
def baseEnd_6536074 : Nat := 1118715851784988604705383

theorem tailTrace_6536074 : CollatzResearch.WordTrace tailWord_6536074 prefixEnd_6536074 1118715851784988604705383 := by
  unfold tailWord_6536074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59597550830731911353327819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158926802215285096942207517 59597550830731911353327819)
  ·
    refine ⟨89396326246097867029991729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59597550830731911353327819 89396326246097867029991729)
    ·
      refine ⟨67047244684573400272493797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89396326246097867029991729 67047244684573400272493797)
      ·
        refine ⟨12571358378357512551092587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67047244684573400272493797 12571358378357512551092587)
        ·
          refine ⟨18857037567536268826638881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571358378357512551092587 18857037567536268826638881)
          ·
            refine ⟨14142778175652201619979161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18857037567536268826638881 14142778175652201619979161)
            ·
              refine ⟨10607083631739151214984371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14142778175652201619979161 10607083631739151214984371)
              ·
                refine ⟨15910625447608726822476557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10607083631739151214984371 15910625447608726822476557)
                ·
                  refine ⟨5966484542853272558428709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15910625447608726822476557 5966484542853272558428709)
                  ·
                    refine ⟨1118715851784988604705383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966484542853272558428709 1118715851784988604705383)
                    ·
                      rfl

theorem cell23_6536074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_6536074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536074 prefixEnd_6536074 := by exact prefixLift 6536074
  have htrace : WordTrace (prefixWord ++ tailWord_6536074) baseStart_6536074 baseEnd_6536074 := by
    simpa [prefixWord, tailWord_6536074, baseEnd_6536074] using wordTrace_append hprefix tailTrace_6536074
  have hstable : (prefixWord ++ tailWord_6536074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536074).length < 2 ^ (prefixWord ++ tailWord_6536074).sum := by decide
  have hdescent : baseEnd_6536074 < baseStart_6536074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536083 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 9]
def baseStart_6536083 : Nat := 118140960795 + 6536083 * 2 ^ 59
def prefixEnd_6536083 : Nat := 4983230072969 + 3 ^ 40 * 6536083 * 2
def baseEnd_6536083 : Nat := 1118717392226952092967869

theorem tailTrace_6536083 : CollatzResearch.WordTrace tailWord_6536083 prefixEnd_6536083 1118717392226952092967869 := by
  unfold tailWord_6536083
  simp only [CollatzResearch.WordTrace]
  refine ⟨238390531579895039950388903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158927021053263359966925935 238390531579895039950388903)
  ·
    refine ⟨357585797369842559925583355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238390531579895039950388903 357585797369842559925583355)
    ·
      refine ⟨536378696054763839888375033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357585797369842559925583355 536378696054763839888375033)
      ·
        refine ⟨402284022041072879916281275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536378696054763839888375033 402284022041072879916281275)
        ·
          refine ⟨603426033061609319874421913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402284022041072879916281275 603426033061609319874421913)
          ·
            refine ⟨452569524796206989905816435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603426033061609319874421913 452569524796206989905816435)
            ·
              refine ⟨678854287194310484858724653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452569524796206989905816435 678854287194310484858724653)
              ·
                refine ⟨254570357697866431822021745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678854287194310484858724653 254570357697866431822021745)
                ·
                  refine ⟨190927768273399823866516309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254570357697866431822021745 190927768273399823866516309)
                  ·
                    refine ⟨1118717392226952092967869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190927768273399823866516309 1118717392226952092967869)
                    ·
                      rfl

theorem cell23_6536083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_6536083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536083 prefixEnd_6536083 := by exact prefixLift 6536083
  have htrace : WordTrace (prefixWord ++ tailWord_6536083) baseStart_6536083 baseEnd_6536083 := by
    simpa [prefixWord, tailWord_6536083, baseEnd_6536083] using wordTrace_append hprefix tailTrace_6536083
  have hstable : (prefixWord ++ tailWord_6536083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536083).length < 2 ^ (prefixWord ++ tailWord_6536083).sum := by decide
  have hdescent : baseEnd_6536083 < baseStart_6536083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536087 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 6]
def baseStart_6536087 : Nat := 118140960795 + 6536087 * 2 ^ 59
def prefixEnd_6536087 : Nat := 4983230072969 + 3 ^ 40 * 6536087 * 2
def baseEnd_6536087 : Nat := 372906025622608251472621

theorem tailTrace_6536087 : CollatzResearch.WordTrace tailWord_6536087 prefixEnd_6536087 372906025622608251472621 := by
  unfold tailWord_6536087
  simp only [CollatzResearch.WordTrace]
  refine ⟨238390677471880548633534515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158927118314587032422356343 238390677471880548633534515)
  ·
    refine ⟨357586016207820822950301773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238390677471880548633534515 357586016207820822950301773)
    ·
      refine ⟨134094756077932808606363165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357586016207820822950301773 134094756077932808606363165)
      ·
        refine ⟨50285533529224803227386187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134094756077932808606363165 50285533529224803227386187)
        ·
          refine ⟨75428300293837204841079281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50285533529224803227386187 75428300293837204841079281)
          ·
            refine ⟨56571225220377903630809461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75428300293837204841079281 56571225220377903630809461)
            ·
              refine ⟨5303552364410428465388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56571225220377903630809461 5303552364410428465388387)
              ·
                refine ⟨7955328546615642698082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303552364410428465388387 7955328546615642698082581)
                ·
                  refine ⟨372906025622608251472621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7955328546615642698082581 372906025622608251472621)
                  ·
                    rfl

theorem cell23_6536087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 6].length) (baseStart_6536087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536087 prefixEnd_6536087 := by exact prefixLift 6536087
  have htrace : WordTrace (prefixWord ++ tailWord_6536087) baseStart_6536087 baseEnd_6536087 := by
    simpa [prefixWord, tailWord_6536087, baseEnd_6536087] using wordTrace_append hprefix tailTrace_6536087
  have hstable : (prefixWord ++ tailWord_6536087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536087).length < 2 ^ (prefixWord ++ tailWord_6536087).sum := by decide
  have hdescent : baseEnd_6536087 < baseStart_6536087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536117 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6536117 : Nat := 118140960795 + 6536117 * 2 ^ 59
def prefixEnd_6536117 : Nat := 4983230072969 + 3 ^ 40 * 6536117 * 2
def baseEnd_6536117 : Nat := 1118723211674369715292817

theorem tailTrace_6536117 : CollatzResearch.WordTrace tailWord_6536117 prefixEnd_6536117 1118723211674369715292817 := by
  unfold tailWord_6536117
  simp only [CollatzResearch.WordTrace]
  refine ⟨238391771661771863757126605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158927847774514575838084403 238391771661771863757126605)
  ·
    refine ⟨89396914373164448908922477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238391771661771863757126605 89396914373164448908922477)
    ·
      refine ⟨33523842889936668340845929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89396914373164448908922477 33523842889936668340845929)
      ·
        refine ⟨25142882167452501255634447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33523842889936668340845929 25142882167452501255634447)
        ·
          refine ⟨37714323251178751883451671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25142882167452501255634447 37714323251178751883451671)
          ·
            refine ⟨56571484876768127825177507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37714323251178751883451671 56571484876768127825177507)
            ·
              refine ⟨84857227315152191737766261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56571484876768127825177507 84857227315152191737766261)
              ·
                refine ⟨7955365060795517975415587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84857227315152191737766261 7955365060795517975415587)
                ·
                  refine ⟨11933047591193276963123381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7955365060795517975415587 11933047591193276963123381)
                  ·
                    refine ⟨1118723211674369715292817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11933047591193276963123381 1118723211674369715292817)
                    ·
                      rfl

theorem cell23_6536117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6536117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536117 prefixEnd_6536117 := by exact prefixLift 6536117
  have htrace : WordTrace (prefixWord ++ tailWord_6536117) baseStart_6536117 baseEnd_6536117 := by
    simpa [prefixWord, tailWord_6536117, baseEnd_6536117] using wordTrace_append hprefix tailTrace_6536117
  have hstable : (prefixWord ++ tailWord_6536117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536117).length < 2 ^ (prefixWord ++ tailWord_6536117).sum := by decide
  have hdescent : baseEnd_6536117 < baseStart_6536117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536154 : List Nat := [3, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_6536154 : Nat := 118140960795 + 6536154 * 2 ^ 59
def prefixEnd_6536154 : Nat := 4983230072969 + 3 ^ 40 * 6536154 * 2
def baseEnd_6536154 : Nat := 3356188633807325501115781

theorem tailTrace_6536154 : CollatzResearch.WordTrace tailWord_6536154 prefixEnd_6536154 3356188633807325501115781 := by
  unfold tailWord_6536154
  simp only [CollatzResearch.WordTrace]
  refine ⟨59598280290659454769055879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158928747441758546050815677 59598280290659454769055879)
  ·
    refine ⟨89397420435989182153583819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59598280290659454769055879 89397420435989182153583819)
    ·
      refine ⟨134096130653983773230375729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89397420435989182153583819 134096130653983773230375729)
      ·
        refine ⟨100572097990487829922781797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134096130653983773230375729 100572097990487829922781797)
        ·
          refine ⟨18857268373216468110521587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100572097990487829922781797 18857268373216468110521587)
          ·
            refine ⟨28285902559824702165782381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857268373216468110521587 28285902559824702165782381)
            ·
              refine ⟨10607213459934263312168393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28285902559824702165782381 10607213459934263312168393)
              ·
                refine ⟨7955410094950697484126295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10607213459934263312168393 7955410094950697484126295)
                ·
                  refine ⟨11933115142426046226189443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7955410094950697484126295 11933115142426046226189443)
                  ·
                    refine ⟨17899672713639069339284165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11933115142426046226189443 17899672713639069339284165)
                    ·
                      refine ⟨3356188633807325501115781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17899672713639069339284165 3356188633807325501115781)
                      ·
                        rfl

theorem cell23_6536154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_6536154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536154 prefixEnd_6536154 := by exact prefixLift 6536154
  have htrace : WordTrace (prefixWord ++ tailWord_6536154) baseStart_6536154 baseEnd_6536154 := by
    simpa [prefixWord, tailWord_6536154, baseEnd_6536154] using wordTrace_append hprefix tailTrace_6536154
  have hstable : (prefixWord ++ tailWord_6536154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536154).length < 2 ^ (prefixWord ++ tailWord_6536154).sum := by decide
  have hdescent : baseEnd_6536154 < baseStart_6536154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536167 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6536167 : Nat := 118140960795 + 6536167 * 2 ^ 59
def prefixEnd_6536167 : Nat := 4983230072969 + 3 ^ 40 * 6536167 * 2
def baseEnd_6536167 : Nat := 3356195309055833950253221

theorem tailTrace_6536167 : CollatzResearch.WordTrace tailWord_6536167 prefixEnd_6536167 3356195309055833950253221 := by
  unfold tailWord_6536167
  simp only [CollatzResearch.WordTrace]
  refine ⟨238393595311590722296446755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158929063541060481530964503 238393595311590722296446755)
  ·
    refine ⟨357590392967386083444670133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238393595311590722296446755 357590392967386083444670133)
    ·
      refine ⟨33524099340692445322937825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357590392967386083444670133 33524099340692445322937825)
      ·
        refine ⟨25143074505519333992203369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33524099340692445322937825 25143074505519333992203369)
        ·
          refine ⟨18857305879139500494152527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25143074505519333992203369 18857305879139500494152527)
          ·
            refine ⟨28285958818709250741228791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857305879139500494152527 28285958818709250741228791)
            ·
              refine ⟨42428938228063876111843187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28285958818709250741228791 42428938228063876111843187)
              ·
                refine ⟨63643407342095814167764781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42428938228063876111843187 63643407342095814167764781)
                ·
                  refine ⟨23866277753285930312911793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63643407342095814167764781 23866277753285930312911793)
                  ·
                    refine ⟨17899708314964447734683845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23866277753285930312911793 17899708314964447734683845)
                    ·
                      refine ⟨3356195309055833950253221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17899708314964447734683845 3356195309055833950253221)
                      ·
                        rfl

theorem cell23_6536167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6536167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536167 prefixEnd_6536167 := by exact prefixLift 6536167
  have htrace : WordTrace (prefixWord ++ tailWord_6536167) baseStart_6536167 baseEnd_6536167 := by
    simpa [prefixWord, tailWord_6536167, baseEnd_6536167] using wordTrace_append hprefix tailTrace_6536167
  have hstable : (prefixWord ++ tailWord_6536167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536167).length < 2 ^ (prefixWord ++ tailWord_6536167).sum := by decide
  have hdescent : baseEnd_6536167 < baseStart_6536167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536188 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_6536188 : Nat := 118140960795 + 6536188 * 2 ^ 59
def prefixEnd_6536188 : Nat := 4983230072969 + 3 ^ 40 * 6536188 * 2
def baseEnd_6536188 : Nat := 3356206092149578368090625

theorem tailTrace_6536188 : CollatzResearch.WordTrace tailWord_6536188 prefixEnd_6536188 3356206092149578368090625 := by
  unfold tailWord_6536188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119197180622257321441480609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158929574163009761921974145 119197180622257321441480609)
  ·
    refine ⟨89397885466692991081110457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119197180622257321441480609 89397885466692991081110457)
    ·
      refine ⟨67048414100019743310832843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89397885466692991081110457 67048414100019743310832843)
      ·
        refine ⟨100572621150029614966249265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67048414100019743310832843 100572621150029614966249265)
        ·
          refine ⟨75429465862522211224686949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100572621150029614966249265 75429465862522211224686949)
          ·
            refine ⟨14143024849222914604628803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75429465862522211224686949 14143024849222914604628803)
            ·
              refine ⟨21214537273834371906943205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14143024849222914604628803 21214537273834371906943205)
              ·
                refine ⟨3977725738843944732551851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21214537273834371906943205 3977725738843944732551851)
                ·
                  refine ⟨5966588608265917098827777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977725738843944732551851 5966588608265917098827777)
                  ·
                    refine ⟨4474941456199437824120833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966588608265917098827777 4474941456199437824120833)
                    ·
                      refine ⟨3356206092149578368090625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474941456199437824120833 3356206092149578368090625)
                      ·
                        rfl

theorem cell23_6536188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_6536188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536188 prefixEnd_6536188 := by exact prefixLift 6536188
  have htrace : WordTrace (prefixWord ++ tailWord_6536188) baseStart_6536188 baseEnd_6536188 := by
    simpa [prefixWord, tailWord_6536188, baseEnd_6536188] using wordTrace_append hprefix tailTrace_6536188
  have hstable : (prefixWord ++ tailWord_6536188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536188).length < 2 ^ (prefixWord ++ tailWord_6536188).sum := by decide
  have hdescent : baseEnd_6536188 < baseStart_6536188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536204 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_6536204 : Nat := 118140960795 + 6536204 * 2 ^ 59
def prefixEnd_6536204 : Nat := 4983230072969 + 3 ^ 40 * 6536204 * 2
def baseEnd_6536204 : Nat := 3356214307840050305490551

theorem tailTrace_6536204 : CollatzResearch.WordTrace tailWord_6536204 prefixEnd_6536204 3356214307840050305490551 := by
  unfold tailWord_6536204
  simp only [CollatzResearch.WordTrace]
  refine ⟨119197472406228338807771833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158929963208304451743695777 119197472406228338807771833)
  ·
    refine ⟨89398104304671254105828875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119197472406228338807771833 89398104304671254105828875)
    ·
      refine ⟨134097156457006881158743313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89398104304671254105828875 134097156457006881158743313)
      ·
        refine ⟨100572867342755160869057485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134097156457006881158743313 100572867342755160869057485)
        ·
          refine ⟨37714825253533185325896557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100572867342755160869057485 37714825253533185325896557)
          ·
            refine ⟨14143059470074944497211209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37714825253533185325896557 14143059470074944497211209)
            ·
              refine ⟨10607294602556208372908407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14143059470074944497211209 10607294602556208372908407)
              ·
                refine ⟨15910941903834312559362611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10607294602556208372908407 15910941903834312559362611)
                ·
                  refine ⟨23866412855751468839043917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15910941903834312559362611 23866412855751468839043917)
                  ·
                    refine ⟨8949904820906800814641469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23866412855751468839043917 8949904820906800814641469)
                    ·
                      refine ⟨3356214307840050305490551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8949904820906800814641469 3356214307840050305490551)
                      ·
                        rfl

theorem cell23_6536204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_6536204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536204 prefixEnd_6536204 := by exact prefixLift 6536204
  have htrace : WordTrace (prefixWord ++ tailWord_6536204) baseStart_6536204 baseEnd_6536204 := by
    simpa [prefixWord, tailWord_6536204, baseEnd_6536204] using wordTrace_append hprefix tailTrace_6536204
  have hstable : (prefixWord ++ tailWord_6536204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536204).length < 2 ^ (prefixWord ++ tailWord_6536204).sum := by decide
  have hdescent : baseEnd_6536204 < baseStart_6536204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536254 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_6536254 : Nat := 118140960795 + 6536254 * 2 ^ 59
def prefixEnd_6536254 : Nat := 4983230072969 + 3 ^ 40 * 6536254 * 2
def baseEnd_6536254 : Nat := 1118746660624258369955107

theorem tailTrace_6536254 : CollatzResearch.WordTrace tailWord_6536254 prefixEnd_6536254 1118746660624258369955107 := by
  unfold tailWord_6536254
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799596057784442019357977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158931178974850357436575877 29799596057784442019357977)
  ·
    refine ⟨22349697043338331514518483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29799596057784442019357977 22349697043338331514518483)
    ·
      refine ⟨33524545565007497271777725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22349697043338331514518483 33524545565007497271777725)
      ·
        refine ⟨12571704586877811476916647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33524545565007497271777725 12571704586877811476916647)
        ·
          refine ⟨18857556880316717215374971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571704586877811476916647 18857556880316717215374971)
          ·
            refine ⟨28286335320475075823062457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857556880316717215374971 28286335320475075823062457)
            ·
              refine ⟨21214751490356306867296843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28286335320475075823062457 21214751490356306867296843)
              ·
                refine ⟨31822127235534460300945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21214751490356306867296843 31822127235534460300945265)
                ·
                  refine ⟨23866595426650845225708949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31822127235534460300945265 23866595426650845225708949)
                  ·
                    refine ⟨1118746660624258369955107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23866595426650845225708949 1118746660624258369955107)
                    ·
                      rfl

theorem cell23_6536254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_6536254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536254 prefixEnd_6536254 := by exact prefixLift 6536254
  have htrace : WordTrace (prefixWord ++ tailWord_6536254) baseStart_6536254 baseEnd_6536254 := by
    simpa [prefixWord, tailWord_6536254, baseEnd_6536254] using wordTrace_append hprefix tailTrace_6536254
  have hstable : (prefixWord ++ tailWord_6536254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536254).length < 2 ^ (prefixWord ++ tailWord_6536254).sum := by decide
  have hdescent : baseEnd_6536254 < baseStart_6536254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536261 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_6536261 : Nat := 118140960795 + 6536261 * 2 ^ 59
def prefixEnd_6536261 : Nat := 4983230072969 + 3 ^ 40 * 6536261 * 2
def baseEnd_6536261 : Nat := 3356243576237356582477789

theorem tailTrace_6536261 : CollatzResearch.WordTrace tailWord_6536261 prefixEnd_6536261 3356243576237356582477789 := by
  unfold tailWord_6536261
  simp only [CollatzResearch.WordTrace]
  refine ⟨238397023773250176350368637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158931349182166784233579091 238397023773250176350368637)
  ·
    refine ⟨89398883914968816131388239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238397023773250176350368637 89398883914968816131388239)
    ·
      refine ⟨134098325872453224197082359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89398883914968816131388239 134098325872453224197082359)
      ·
        refine ⟨201147488808679836295623539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134098325872453224197082359 201147488808679836295623539)
        ·
          refine ⟨301721233213019754443435309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201147488808679836295623539 301721233213019754443435309)
          ·
            refine ⟨113145462454882407916288241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301721233213019754443435309 113145462454882407916288241)
            ·
              refine ⟨84859096841161805937216181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113145462454882407916288241 84859096841161805937216181)
              ·
                refine ⟨7955540328858919306614017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84859096841161805937216181 7955540328858919306614017)
                ·
                  refine ⟨5966655246644189479960513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955540328858919306614017 5966655246644189479960513)
                  ·
                    refine ⟨4474991434983142109970385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5966655246644189479960513 4474991434983142109970385)
                    ·
                      refine ⟨3356243576237356582477789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4474991434983142109970385 3356243576237356582477789)
                      ·
                        rfl

theorem cell23_6536261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_6536261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536261 prefixEnd_6536261 := by exact prefixLift 6536261
  have htrace : WordTrace (prefixWord ++ tailWord_6536261) baseStart_6536261 baseEnd_6536261 := by
    simpa [prefixWord, tailWord_6536261, baseEnd_6536261] using wordTrace_append hprefix tailTrace_6536261
  have hstable : (prefixWord ++ tailWord_6536261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536261).length < 2 ^ (prefixWord ++ tailWord_6536261).sum := by decide
  have hdescent : baseEnd_6536261 < baseStart_6536261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536297 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_6536297 : Nat := 118140960795 + 6536297 * 2 ^ 59
def prefixEnd_6536297 : Nat := 4983230072969 + 3 ^ 40 * 6536297 * 2
def baseEnd_6536297 : Nat := 1118754020513639480542541

theorem tailTrace_6536297 : CollatzResearch.WordTrace tailWord_6536297 prefixEnd_6536297 1118754020513639480542541 := by
  unfold tailWord_6536297
  simp only [CollatzResearch.WordTrace]
  refine ⟨238398336801119754498679145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158932224534079836332452763 238398336801119754498679145)
  ·
    refine ⟨178798752600839815874009359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238398336801119754498679145 178798752600839815874009359)
    ·
      refine ⟨268198128901259723811014039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178798752600839815874009359 268198128901259723811014039)
      ·
        refine ⟨402297193351889585716521059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268198128901259723811014039 402297193351889585716521059)
        ·
          refine ⟨603445790027834378574781589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402297193351889585716521059 603445790027834378574781589)
          ·
            refine ⟨28286521407554736495692887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 603445790027834378574781589 28286521407554736495692887)
            ·
              refine ⟨42429782111332104743539331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28286521407554736495692887 42429782111332104743539331)
              ·
                refine ⟨63644673166998157115308997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42429782111332104743539331 63644673166998157115308997)
                ·
                  refine ⟨11933376218812154459120437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63644673166998157115308997 11933376218812154459120437)
                  ·
                    refine ⟨1118754020513639480542541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11933376218812154459120437 1118754020513639480542541)
                    ·
                      rfl

theorem cell23_6536297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_6536297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536297 prefixEnd_6536297 := by exact prefixLift 6536297
  have htrace : WordTrace (prefixWord ++ tailWord_6536297) baseStart_6536297 baseEnd_6536297 := by
    simpa [prefixWord, tailWord_6536297, baseEnd_6536297] using wordTrace_append hprefix tailTrace_6536297
  have hstable : (prefixWord ++ tailWord_6536297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536297).length < 2 ^ (prefixWord ++ tailWord_6536297).sum := by decide
  have hdescent : baseEnd_6536297 < baseStart_6536297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536304 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2]
def baseStart_6536304 : Nat := 118140960795 + 6536304 * 2 ^ 59
def prefixEnd_6536304 : Nat := 4983230072969 + 3 ^ 40 * 6536304 * 2
def baseEnd_6536304 : Nat := 3356265655905499914240091

theorem tailTrace_6536304 : CollatzResearch.WordTrace tailWord_6536304 prefixEnd_6536304 3356265655905499914240091 := by
  unfold tailWord_6536304
  simp only [CollatzResearch.WordTrace]
  refine ⟨119199296056047197347091983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158932394741396263129455977 119199296056047197347091983)
  ·
    refine ⟨178798944084070796020637975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119199296056047197347091983 178798944084070796020637975)
    ·
      refine ⟨268198416126106194030956963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178798944084070796020637975 268198416126106194030956963)
      ·
        refine ⟨402297624189159291046435445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268198416126106194030956963 402297624189159291046435445)
        ·
          refine ⟨37715402267733683535603323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 402297624189159291046435445 37715402267733683535603323)
          ·
            refine ⟨56573103401600525303404985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37715402267733683535603323 56573103401600525303404985)
            ·
              refine ⟨42429827551200393977553739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56573103401600525303404985 42429827551200393977553739)
              ·
                refine ⟨63644741326800590966330609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42429827551200393977553739 63644741326800590966330609)
                ·
                  refine ⟨47733555995100443224747957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63644741326800590966330609 47733555995100443224747957)
                  ·
                    refine ⟨4475020874540666552320121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47733555995100443224747957 4475020874540666552320121)
                    ·
                      refine ⟨3356265655905499914240091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475020874540666552320121 3356265655905499914240091)
                      ·
                        rfl

theorem cell23_6536304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2].length) (baseStart_6536304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536304 prefixEnd_6536304 := by exact prefixLift 6536304
  have htrace : WordTrace (prefixWord ++ tailWord_6536304) baseStart_6536304 baseEnd_6536304 := by
    simpa [prefixWord, tailWord_6536304, baseEnd_6536304] using wordTrace_append hprefix tailTrace_6536304
  have hstable : (prefixWord ++ tailWord_6536304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536304).length < 2 ^ (prefixWord ++ tailWord_6536304).sum := by decide
  have hdescent : baseEnd_6536304 < baseStart_6536304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536408 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 6]
def baseStart_6536408 : Nat := 118140960795 + 6536408 * 2 ^ 59
def prefixEnd_6536408 : Nat := 4983230072969 + 3 ^ 40 * 6536408 * 2
def baseEnd_6536408 : Nat := 372924339765951945259957

theorem tailTrace_6536408 : CollatzResearch.WordTrace tailWord_6536408 prefixEnd_6536408 372924339765951945259957 := by
  unfold tailWord_6536408
  simp only [CollatzResearch.WordTrace]
  refine ⟨119201192651858810227984939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158934923535811746970646585 119201192651858810227984939)
  ·
    refine ⟨178801788977788215341977409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119201192651858810227984939 178801788977788215341977409)
    ·
      refine ⟨134101341733341161506483057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178801788977788215341977409 134101341733341161506483057)
      ·
        refine ⟨100576006300005871129862293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134101341733341161506483057 100576006300005871129862293)
        ·
          refine ⟨4714500295312775209212295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100576006300005871129862293 4714500295312775209212295)
          ·
            refine ⟨7071750442969162813818443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4714500295312775209212295 7071750442969162813818443)
            ·
              refine ⟨10607625664453744220727665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7071750442969162813818443 10607625664453744220727665)
              ·
                refine ⟨7955719248340308165545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10607625664453744220727665 7955719248340308165545749)
                ·
                  refine ⟨372924339765951945259957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7955719248340308165545749 372924339765951945259957)
                  ·
                    rfl

theorem cell23_6536408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_6536408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536408 prefixEnd_6536408 := by exact prefixLift 6536408
  have htrace : WordTrace (prefixWord ++ tailWord_6536408) baseStart_6536408 baseEnd_6536408 := by
    simpa [prefixWord, tailWord_6536408, baseEnd_6536408] using wordTrace_append hprefix tailTrace_6536408
  have hstable : (prefixWord ++ tailWord_6536408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536408).length < 2 ^ (prefixWord ++ tailWord_6536408).sum := by decide
  have hdescent : baseEnd_6536408 < baseStart_6536408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536441 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6536441 : Nat := 118140960795 + 6536441 * 2 ^ 59
def prefixEnd_6536441 : Nat := 4983230072969 + 3 ^ 40 * 6536441 * 2
def baseEnd_6536441 : Nat := 3356336002755165878226961

theorem tailTrace_6536441 : CollatzResearch.WordTrace tailWord_6536441 prefixEnd_6536441 3356336002755165878226961 := by
  unfold tailWord_6536441
  simp only [CollatzResearch.WordTrace]
  refine ⟨238403588912598067091921177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158935725941732044727947451 238403588912598067091921177)
  ·
    refine ⟨178802691684448550318940883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238403588912598067091921177 178802691684448550318940883)
    ·
      refine ⟨268204037526672825478411325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178802691684448550318940883 268204037526672825478411325)
      ·
        refine ⟨100576514072502309554404247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268204037526672825478411325 100576514072502309554404247)
        ·
          refine ⟨150864771108753464331606371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100576514072502309554404247 150864771108753464331606371)
          ·
            refine ⟨226297156663130196497409557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150864771108753464331606371 226297156663130196497409557)
            ·
              refine ⟨10607679218584227960816073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226297156663130196497409557 10607679218584227960816073)
              ·
                refine ⟨7955759413938170970612055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10607679218584227960816073 7955759413938170970612055)
                ·
                  refine ⟨11933639120907256455918083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7955759413938170970612055 11933639120907256455918083)
                  ·
                    refine ⟨17900458681360884683877125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11933639120907256455918083 17900458681360884683877125)
                    ·
                      refine ⟨3356336002755165878226961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17900458681360884683877125 3356336002755165878226961)
                      ·
                        rfl

theorem cell23_6536441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6536441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536441 prefixEnd_6536441 := by exact prefixLift 6536441
  have htrace : WordTrace (prefixWord ++ tailWord_6536441) baseStart_6536441 baseEnd_6536441 := by
    simpa [prefixWord, tailWord_6536441, baseEnd_6536441] using wordTrace_append hprefix tailTrace_6536441
  have hstable : (prefixWord ++ tailWord_6536441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536441).length < 2 ^ (prefixWord ++ tailWord_6536441).sum := by decide
  have hdescent : baseEnd_6536441 < baseStart_6536441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536452 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6536452 : Nat := 118140960795 + 6536452 * 2 ^ 59
def prefixEnd_6536452 : Nat := 4983230072969 + 3 ^ 40 * 6536452 * 2
def baseEnd_6536452 : Nat := 3356341651042365335189411

theorem tailTrace_6536452 : CollatzResearch.WordTrace tailWord_6536452 prefixEnd_6536452 3356341651042365335189411 := by
  unfold tailWord_6536452
  simp only [CollatzResearch.WordTrace]
  refine ⟨119201995057779107985285805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158935993410372143980381073 119201995057779107985285805)
  ·
    refine ⟨44700748146667165494482177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119201995057779107985285805 44700748146667165494482177)
    ·
      refine ⟨33525561110000374120861633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44700748146667165494482177 33525561110000374120861633)
      ·
        refine ⟨25144170832500280590646225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33525561110000374120861633 25144170832500280590646225)
        ·
          refine ⟨18858128124375210442984669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25144170832500280590646225 18858128124375210442984669)
          ·
            refine ⟨7071798046640703916119251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18858128124375210442984669 7071798046640703916119251)
            ·
              refine ⟨10607697069961055874178877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7071798046640703916119251 10607697069961055874178877)
              ·
                refine ⟨3977886401235395952817079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10607697069961055874178877 3977886401235395952817079)
                ·
                  refine ⟨5966829601853093929225619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977886401235395952817079 5966829601853093929225619)
                  ·
                    refine ⟨8950244402779640893838429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5966829601853093929225619 8950244402779640893838429)
                    ·
                      refine ⟨3356341651042365335189411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950244402779640893838429 3356341651042365335189411)
                      ·
                        rfl

theorem cell23_6536452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6536452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536452 prefixEnd_6536452 := by exact prefixLift 6536452
  have htrace : WordTrace (prefixWord ++ tailWord_6536452) baseStart_6536452 baseEnd_6536452 := by
    simpa [prefixWord, tailWord_6536452, baseEnd_6536452] using wordTrace_append hprefix tailTrace_6536452
  have hstable : (prefixWord ++ tailWord_6536452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536452).length < 2 ^ (prefixWord ++ tailWord_6536452).sum := by decide
  have hdescent : baseEnd_6536452 < baseStart_6536452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536484 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6536484 : Nat := 118140960795 + 6536484 * 2 ^ 59
def prefixEnd_6536484 : Nat := 4983230072969 + 3 ^ 40 * 6536484 * 2
def baseEnd_6536484 : Nat := 3356358082423309209989263

theorem tailTrace_6536484 : CollatzResearch.WordTrace tailWord_6536484 prefixEnd_6536484 3356358082423309209989263 := by
  unfold tailWord_6536484
  simp only [CollatzResearch.WordTrace]
  refine ⟨119202578625721142717868253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158936771500961523623824337 119202578625721142717868253)
  ·
    refine ⟨44700966984645428519200595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119202578625721142717868253 44700966984645428519200595)
    ·
      refine ⟨67051450476968142778800893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44700966984645428519200595 67051450476968142778800893)
      ·
        refine ⟨25144293928863053542050335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67051450476968142778800893 25144293928863053542050335)
        ·
          refine ⟨37716440893294580313075503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25144293928863053542050335 37716440893294580313075503)
          ·
            refine ⟨56574661339941870469613255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37716440893294580313075503 56574661339941870469613255)
            ·
              refine ⟨84861992009912805704419883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56574661339941870469613255 84861992009912805704419883)
              ·
                refine ⟨127292988014869208556629825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84861992009912805704419883 127292988014869208556629825)
                ·
                  refine ⟨95469741011151906417472369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127292988014869208556629825 95469741011151906417472369)
                  ·
                    refine ⟨71602305758363929813104277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95469741011151906417472369 71602305758363929813104277)
                    ·
                      refine ⟨3356358082423309209989263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71602305758363929813104277 3356358082423309209989263)
                      ·
                        rfl

theorem cell23_6536484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6536484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536484 prefixEnd_6536484 := by exact prefixLift 6536484
  have htrace : WordTrace (prefixWord ++ tailWord_6536484) baseStart_6536484 baseEnd_6536484 := by
    simpa [prefixWord, tailWord_6536484, baseEnd_6536484] using wordTrace_append hprefix tailTrace_6536484
  have hstable : (prefixWord ++ tailWord_6536484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536484).length < 2 ^ (prefixWord ++ tailWord_6536484).sum := by decide
  have hdescent : baseEnd_6536484 < baseStart_6536484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536485 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_6536485 : Nat := 118140960795 + 6536485 * 2 ^ 59
def prefixEnd_6536485 : Nat := 4983230072969 + 3 ^ 40 * 6536485 * 2
def baseEnd_6536485 : Nat := 1118786198634654568692253

theorem tailTrace_6536485 : CollatzResearch.WordTrace tailWord_6536485 prefixEnd_6536485 1118786198634654568692253 := by
  unfold tailWord_6536485
  simp only [CollatzResearch.WordTrace]
  refine ⟨238405193724438662606522909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158936795816292441737681939 238405193724438662606522909)
  ·
    refine ⟨89401947646664498477446091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238405193724438662606522909 89401947646664498477446091)
    ·
      refine ⟨134102921469996747716169137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89401947646664498477446091 134102921469996747716169137)
      ·
        refine ⟨100577191102497560787126853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134102921469996747716169137 100577191102497560787126853)
        ·
          refine ⟨18858223331718292647586285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100577191102497560787126853 18858223331718292647586285)
          ·
            refine ⟨7071833749394359742844857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18858223331718292647586285 7071833749394359742844857)
            ·
              refine ⟨5303875312045769807133643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071833749394359742844857 5303875312045769807133643)
              ·
                refine ⟨7955812968068654710700465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303875312045769807133643 7955812968068654710700465)
                ·
                  refine ⟨5966859726051491033025349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955812968068654710700465 5966859726051491033025349)
                  ·
                    refine ⟨1118786198634654568692253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966859726051491033025349 1118786198634654568692253)
                    ·
                      rfl

theorem cell23_6536485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_6536485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536485 prefixEnd_6536485 := by exact prefixLift 6536485
  have htrace : WordTrace (prefixWord ++ tailWord_6536485) baseStart_6536485 baseEnd_6536485 := by
    simpa [prefixWord, tailWord_6536485, baseEnd_6536485] using wordTrace_append hprefix tailTrace_6536485
  have hstable : (prefixWord ++ tailWord_6536485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536485).length < 2 ^ (prefixWord ++ tailWord_6536485).sum := by decide
  have hdescent : baseEnd_6536485 < baseStart_6536485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536531 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 3, 4, 2]
def baseStart_6536531 : Nat := 118140960795 + 6536531 * 2 ^ 59
def prefixEnd_6536531 : Nat := 4983230072969 + 3 ^ 40 * 6536531 * 2
def baseEnd_6536531 : Nat := 3356382216014070526101547

theorem tailTrace_6536531 : CollatzResearch.WordTrace tailWord_6536531 prefixEnd_6536531 3356382216014070526101547 := by
  unfold tailWord_6536531
  simp only [CollatzResearch.WordTrace]
  refine ⟨238406871482272012462697447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158937914321514674975131631 238406871482272012462697447)
  ·
    refine ⟨357610307223408018694046171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238406871482272012462697447 357610307223408018694046171)
    ·
      refine ⟨536415460835112028041069257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357610307223408018694046171 536415460835112028041069257)
      ·
        refine ⟨402311595626334021030801943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536415460835112028041069257 402311595626334021030801943)
        ·
          refine ⟨603467393439501031546202915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402311595626334021030801943 603467393439501031546202915)
          ·
            refine ⟨905201090159251547319304373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603467393439501031546202915 905201090159251547319304373)
            ·
              refine ⟨84862602202429832561184785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 905201090159251547319304373 84862602202429832561184785)
              ·
                refine ⟨63646951651822374420888589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84862602202429832561184785 63646951651822374420888589)
                ·
                  refine ⟨23867606869433390407833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63646951651822374420888589 23867606869433390407833221)
                  ·
                    refine ⟨4475176288018760701468729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23867606869433390407833221 4475176288018760701468729)
                    ·
                      refine ⟨3356382216014070526101547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475176288018760701468729 3356382216014070526101547)
                      ·
                        rfl

theorem cell23_6536531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4, 2].length) (baseStart_6536531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536531 prefixEnd_6536531 := by exact prefixLift 6536531
  have htrace : WordTrace (prefixWord ++ tailWord_6536531) baseStart_6536531 baseEnd_6536531 := by
    simpa [prefixWord, tailWord_6536531, baseEnd_6536531] using wordTrace_append hprefix tailTrace_6536531
  have hstable : (prefixWord ++ tailWord_6536531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536531).length < 2 ^ (prefixWord ++ tailWord_6536531).sum := by decide
  have hdescent : baseEnd_6536531 < baseStart_6536531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536548 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_6536548 : Nat := 118140960795 + 6536548 * 2 ^ 59
def prefixEnd_6536548 : Nat := 4983230072969 + 3 ^ 40 * 6536548 * 2
def baseEnd_6536548 : Nat := 3356390945185196959588969

theorem tailTrace_6536548 : CollatzResearch.WordTrace tailWord_6536548 prefixEnd_6536548 3356390945185196959588969 := by
  unfold tailWord_6536548
  simp only [CollatzResearch.WordTrace]
  refine ⟨119203745761605212183033149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158938327682140282910710865 119203745761605212183033149)
  ·
    refine ⟨44701404660601954568637431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119203745761605212183033149 44701404660601954568637431)
    ·
      refine ⟨67052106990902931852956147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44701404660601954568637431 67052106990902931852956147)
      ·
        refine ⟨100578160486354397779434221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67052106990902931852956147 100578160486354397779434221)
        ·
          refine ⟨37716810182382899167287833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100578160486354397779434221 37716810182382899167287833)
          ·
            refine ⟨28287607636787174375465875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37716810182382899167287833 28287607636787174375465875)
            ·
              refine ⟨42431411455180761563198813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28287607636787174375465875 42431411455180761563198813)
              ·
                refine ⟨15911779295692785586199555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42431411455180761563198813 15911779295692785586199555)
                ·
                  refine ⟨23867668943539178379299333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15911779295692785586199555 23867668943539178379299333)
                  ·
                    refine ⟨4475187926913595946118625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23867668943539178379299333 4475187926913595946118625)
                    ·
                      refine ⟨3356390945185196959588969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475187926913595946118625 3356390945185196959588969)
                      ·
                        rfl

theorem cell23_6536548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_6536548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536548 prefixEnd_6536548 := by exact prefixLift 6536548
  have htrace : WordTrace (prefixWord ++ tailWord_6536548) baseStart_6536548 baseEnd_6536548 := by
    simpa [prefixWord, tailWord_6536548, baseEnd_6536548] using wordTrace_append hprefix tailTrace_6536548
  have hstable : (prefixWord ++ tailWord_6536548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536548).length < 2 ^ (prefixWord ++ tailWord_6536548).sum := by decide
  have hdescent : baseEnd_6536548 < baseStart_6536548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536581 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_6536581 : Nat := 118140960795 + 6536581 * 2 ^ 59
def prefixEnd_6536581 : Nat := 4983230072969 + 3 ^ 40 * 6536581 * 2
def baseEnd_6536581 : Nat := 3356407890046795330476317

theorem tailTrace_6536581 : CollatzResearch.WordTrace tailWord_6536581 prefixEnd_6536581 3356407890046795330476317 := by
  unfold tailWord_6536581
  simp only [CollatzResearch.WordTrace]
  refine ⟨238408695132090871002017597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158939130088060580668011731 238408695132090871002017597)
  ·
    refine ⟨89403260674534076625756599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238408695132090871002017597 89403260674534076625756599)
    ·
      refine ⟨134104891011801114938634899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89403260674534076625756599 134104891011801114938634899)
      ·
        refine ⟨201157336517701672407952349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134104891011801114938634899 201157336517701672407952349)
        ·
          refine ⟨75434001194138127152982131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201157336517701672407952349 75434001194138127152982131)
          ·
            refine ⟨113151001791207190729473197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75434001194138127152982131 113151001791207190729473197)
            ·
              refine ⟨42431625671702696523552449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113151001791207190729473197 42431625671702696523552449)
              ·
                refine ⟨31823719253777022392664337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42431625671702696523552449 31823719253777022392664337)
                ·
                  refine ⟨23867789440332766794498253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31823719253777022392664337 23867789440332766794498253)
                  ·
                    refine ⟨8950421040124787547936845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23867789440332766794498253 8950421040124787547936845)
                    ·
                      refine ⟨3356407890046795330476317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950421040124787547936845 3356407890046795330476317)
                      ·
                        rfl

theorem cell23_6536581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_6536581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536581 prefixEnd_6536581 := by exact prefixLift 6536581
  have htrace : WordTrace (prefixWord ++ tailWord_6536581) baseStart_6536581 baseEnd_6536581 := by
    simpa [prefixWord, tailWord_6536581, baseEnd_6536581] using wordTrace_append hprefix tailTrace_6536581
  have hstable : (prefixWord ++ tailWord_6536581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536581).length < 2 ^ (prefixWord ++ tailWord_6536581).sum := by decide
  have hdescent : baseEnd_6536581 < baseStart_6536581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536675 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6536675 : Nat := 118140960795 + 6536675 * 2 ^ 59
def prefixEnd_6536675 : Nat := 4983230072969 + 3 ^ 40 * 6536675 * 2
def baseEnd_6536675 : Nat := 3356456157228317962700885

theorem tailTrace_6536675 : CollatzResearch.WordTrace tailWord_6536675 prefixEnd_6536675 3356456157228317962700885 := by
  unfold tailWord_6536675
  simp only [CollatzResearch.WordTrace]
  refine ⟨238412123593750325055939479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158941415729166883370626319 238412123593750325055939479)
  ·
    refine ⟨357618185390625487583909219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238412123593750325055939479 357618185390625487583909219)
    ·
      refine ⟨536427278085938231375863829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357618185390625487583909219 536427278085938231375863829)
      ·
        refine ⟨25145028660278354595743617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 536427278085938231375863829 25145028660278354595743617)
        ·
          refine ⟨18858771495208765946807713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25145028660278354595743617 18858771495208765946807713)
          ·
            refine ⟨14144078621406574460105785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18858771495208765946807713 14144078621406574460105785)
            ·
              refine ⟨10608058966054930845079339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14144078621406574460105785 10608058966054930845079339)
              ·
                refine ⟨15912088449082396267619009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608058966054930845079339 15912088449082396267619009)
                ·
                  refine ⟨11934066336811797200714257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15912088449082396267619009 11934066336811797200714257)
                  ·
                    refine ⟨8950549752608847900535693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11934066336811797200714257 8950549752608847900535693)
                    ·
                      refine ⟨3356456157228317962700885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950549752608847900535693 3356456157228317962700885)
                      ·
                        rfl

theorem cell23_6536675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6536675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536675 prefixEnd_6536675 := by exact prefixLift 6536675
  have htrace : WordTrace (prefixWord ++ tailWord_6536675) baseStart_6536675 baseEnd_6536675 := by
    simpa [prefixWord, tailWord_6536675, baseEnd_6536675] using wordTrace_append hprefix tailTrace_6536675
  have hstable : (prefixWord ++ tailWord_6536675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536675).length < 2 ^ (prefixWord ++ tailWord_6536675).sum := by decide
  have hdescent : baseEnd_6536675 < baseStart_6536675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536738 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6536738 : Nat := 118140960795 + 6536738 * 2 ^ 59
def prefixEnd_6536738 : Nat := 4983230072969 + 3 ^ 40 * 6536738 * 2
def baseEnd_6536738 : Nat := 1118829502169850405404365

theorem tailTrace_6536738 : CollatzResearch.WordTrace tailWord_6536738 prefixEnd_6536738 1118829502169850405404365 := by
  unfold tailWord_6536738
  simp only [CollatzResearch.WordTrace]
  refine ⟨59603605348130521703870717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158942947595014724543655245 59603605348130521703870717)
  ·
    refine ⟨22351352005548945638951519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59603605348130521703870717 22351352005548945638951519)
    ·
      refine ⟨33527028008323418458427279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351352005548945638951519 33527028008323418458427279)
      ·
        refine ⟨50290542012485127687640919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33527028008323418458427279 50290542012485127687640919)
        ·
          refine ⟨75435813018727691531461379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50290542012485127687640919 75435813018727691531461379)
          ·
            refine ⟨113153719528091537297192069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75435813018727691531461379 113153719528091537297192069)
            ·
              refine ⟨21216322411517163243223513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113153719528091537297192069 21216322411517163243223513)
              ·
                refine ⟨15912241808637872432417635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21216322411517163243223513 15912241808637872432417635)
                ·
                  refine ⟨23868362712956808648626453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15912241808637872432417635 23868362712956808648626453)
                  ·
                    refine ⟨1118829502169850405404365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23868362712956808648626453 1118829502169850405404365)
                    ·
                      rfl

theorem cell23_6536738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6536738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536738 prefixEnd_6536738 := by exact prefixLift 6536738
  have htrace : WordTrace (prefixWord ++ tailWord_6536738) baseStart_6536738 baseEnd_6536738 := by
    simpa [prefixWord, tailWord_6536738, baseEnd_6536738] using wordTrace_append hprefix tailTrace_6536738
  have hstable : (prefixWord ++ tailWord_6536738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536738).length < 2 ^ (prefixWord ++ tailWord_6536738).sum := by decide
  have hdescent : baseEnd_6536738 < baseStart_6536738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536739 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 1, 1, 3]
def baseStart_6536739 : Nat := 118140960795 + 6536739 * 2 ^ 59
def prefixEnd_6536739 : Nat := 4983230072969 + 3 ^ 40 * 6536739 * 2
def baseEnd_6536739 : Nat := 3356489019990205712300591

theorem tailTrace_6536739 : CollatzResearch.WordTrace tailWord_6536739 prefixEnd_6536739 3356489019990205712300591 := by
  unfold tailWord_6536739
  simp only [CollatzResearch.WordTrace]
  refine ⟨238414457865518463986269271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158942971910345642657512847 238414457865518463986269271)
  ·
    refine ⟨357621686798277695979403907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238414457865518463986269271 357621686798277695979403907)
    ·
      refine ⟨536432530197416543969105861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357621686798277695979403907 536432530197416543969105861)
      ·
        refine ⟨100581099412015601994207349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 536432530197416543969105861 100581099412015601994207349)
        ·
          refine ⟨9429478069876462686956939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100581099412015601994207349 9429478069876462686956939)
          ·
            refine ⟨14144217104814694030435409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429478069876462686956939 14144217104814694030435409)
            ·
              refine ⟨10608162828611020522826557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14144217104814694030435409 10608162828611020522826557)
              ·
                refine ⟨3978061060729132696059959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10608162828611020522826557 3978061060729132696059959)
                ·
                  refine ⟨5967091591093699044089939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978061060729132696059959 5967091591093699044089939)
                  ·
                    refine ⟨8950637386640548566134909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967091591093699044089939 8950637386640548566134909)
                    ·
                      refine ⟨3356489019990205712300591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950637386640548566134909 3356489019990205712300591)
                      ·
                        rfl

theorem cell23_6536739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_6536739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536739 prefixEnd_6536739 := by exact prefixLift 6536739
  have htrace : WordTrace (prefixWord ++ tailWord_6536739) baseStart_6536739 baseEnd_6536739 := by
    simpa [prefixWord, tailWord_6536739, baseEnd_6536739] using wordTrace_append hprefix tailTrace_6536739
  have hstable : (prefixWord ++ tailWord_6536739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536739).length < 2 ^ (prefixWord ++ tailWord_6536739).sum := by decide
  have hdescent : baseEnd_6536739 < baseStart_6536739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536741 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6536741 : Nat := 118140960795 + 6536741 * 2 ^ 59
def prefixEnd_6536741 : Nat := 4983230072969 + 3 ^ 40 * 6536741 * 2
def baseEnd_6536741 : Nat := 3356490046951514704475581

theorem tailTrace_6536741 : CollatzResearch.WordTrace tailWord_6536741 prefixEnd_6536741 3356490046951514704475581 := by
  unfold tailWord_6536741
  simp only [CollatzResearch.WordTrace]
  refine ⟨238414530811511218327842077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158943020541007478885228051 238414530811511218327842077)
  ·
    refine ⟨89405449054316706872940779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238414530811511218327842077 89405449054316706872940779)
    ·
      refine ⟨134108173581475060309411169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89405449054316706872940779 134108173581475060309411169)
      ·
        refine ⟨100581130186106295232058377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134108173581475060309411169 100581130186106295232058377)
        ·
          refine ⟨75435847639579721424043783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100581130186106295232058377 75435847639579721424043783)
          ·
            refine ⟨113153771459369582136065675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75435847639579721424043783 113153771459369582136065675)
            ·
              refine ⟨169730657189054373204098513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113153771459369582136065675 169730657189054373204098513)
              ·
                refine ⟨127297992891790779903073885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169730657189054373204098513 127297992891790779903073885)
                ·
                  refine ⟨47736747334421542463652707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127297992891790779903073885 47736747334421542463652707)
                  ·
                    refine ⟨71605121001632313695479061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47736747334421542463652707 71605121001632313695479061)
                    ·
                      refine ⟨3356490046951514704475581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71605121001632313695479061 3356490046951514704475581)
                      ·
                        rfl

theorem cell23_6536741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6536741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536741 prefixEnd_6536741 := by exact prefixLift 6536741
  have htrace : WordTrace (prefixWord ++ tailWord_6536741) baseStart_6536741 baseEnd_6536741 := by
    simpa [prefixWord, tailWord_6536741, baseEnd_6536741] using wordTrace_append hprefix tailTrace_6536741
  have hstable : (prefixWord ++ tailWord_6536741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536741).length < 2 ^ (prefixWord ++ tailWord_6536741).sum := by decide
  have hdescent : baseEnd_6536741 < baseStart_6536741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536755 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 2, 4]
def baseStart_6536755 : Nat := 118140960795 + 6536755 * 2 ^ 59
def prefixEnd_6536755 : Nat := 4983230072969 + 3 ^ 40 * 6536755 * 2
def baseEnd_6536755 : Nat := 1118832411893559216566839

theorem tailTrace_6536755 : CollatzResearch.WordTrace tailWord_6536755 prefixEnd_6536755 1118832411893559216566839 := by
  unfold tailWord_6536755
  simp only [CollatzResearch.WordTrace]
  refine ⟨238415041433460498718851719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158943360955640332479234479 238415041433460498718851719)
  ·
    refine ⟨357622562150190748078277579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238415041433460498718851719 357622562150190748078277579)
    ·
      refine ⟨536433843225286122117416369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357622562150190748078277579 536433843225286122117416369)
      ·
        refine ⟨402325382418964591588062277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536433843225286122117416369 402325382418964591588062277)
        ·
          refine ⟨75436009203555860922761677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 402325382418964591588062277 75436009203555860922761677)
          ·
            refine ⟨28288503451333447846035629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75436009203555860922761677 28288503451333447846035629)
            ·
              refine ⟨10608188794250042942263361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28288503451333447846035629 10608188794250042942263361)
              ·
                refine ⟨7956141595687532206697521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10608188794250042942263361 7956141595687532206697521)
                ·
                  refine ⟨5967106196765649155023141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956141595687532206697521 5967106196765649155023141)
                  ·
                    refine ⟨1118832411893559216566839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5967106196765649155023141 1118832411893559216566839)
                    ·
                      rfl

theorem cell23_6536755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 4].length) (baseStart_6536755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536755 prefixEnd_6536755 := by exact prefixLift 6536755
  have htrace : WordTrace (prefixWord ++ tailWord_6536755) baseStart_6536755 baseEnd_6536755 := by
    simpa [prefixWord, tailWord_6536755, baseEnd_6536755] using wordTrace_append hprefix tailTrace_6536755
  have hstable : (prefixWord ++ tailWord_6536755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536755).length < 2 ^ (prefixWord ++ tailWord_6536755).sum := by decide
  have hdescent : baseEnd_6536755 < baseStart_6536755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536762 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_6536762 : Nat := 118140960795 + 6536762 * 2 ^ 59
def prefixEnd_6536762 : Nat := 4983230072969 + 3 ^ 40 * 6536762 * 2
def baseEnd_6536762 : Nat := 3356500830045259122312985

theorem tailTrace_6536762 : CollatzResearch.WordTrace tailWord_6536762 prefixEnd_6536762 3356500830045259122312985 := by
  unfold tailWord_6536762
  simp only [CollatzResearch.WordTrace]
  refine ⟨59603824186108784728589135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158943531162956759276237693 59603824186108784728589135)
  ·
    refine ⟨89405736279163177092883703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59603824186108784728589135 89405736279163177092883703)
    ·
      refine ⟨134108604418744765639325555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89405736279163177092883703 134108604418744765639325555)
      ·
        refine ⟨201162906628117148458988333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134108604418744765639325555 201162906628117148458988333)
        ·
          refine ⟨75436089985543930672120625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201162906628117148458988333 75436089985543930672120625)
          ·
            refine ⟨56577067489157948004090469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75436089985543930672120625 56577067489157948004090469)
            ·
              refine ⟨10608200154217115250766963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56577067489157948004090469 10608200154217115250766963)
              ·
                refine ⟨15912300231325672876150445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608200154217115250766963 15912300231325672876150445)
                ·
                  refine ⟨5967112586747127328556417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15912300231325672876150445 5967112586747127328556417)
                  ·
                    refine ⟨4475334440060345496417313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967112586747127328556417 4475334440060345496417313)
                    ·
                      refine ⟨3356500830045259122312985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475334440060345496417313 3356500830045259122312985)
                      ·
                        rfl

theorem cell23_6536762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_6536762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536762 prefixEnd_6536762 := by exact prefixLift 6536762
  have htrace : WordTrace (prefixWord ++ tailWord_6536762) baseStart_6536762 baseEnd_6536762 := by
    simpa [prefixWord, tailWord_6536762, baseEnd_6536762] using wordTrace_append hprefix tailTrace_6536762
  have hstable : (prefixWord ++ tailWord_6536762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536762).length < 2 ^ (prefixWord ++ tailWord_6536762).sum := by decide
  have hdescent : baseEnd_6536762 < baseStart_6536762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536765 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6536765 : Nat := 118140960795 + 6536765 * 2 ^ 59
def prefixEnd_6536765 : Nat := 4983230072969 + 3 ^ 40 * 6536765 * 2
def baseEnd_6536765 : Nat := 3356502370487222610575471

theorem tailTrace_6536765 : CollatzResearch.WordTrace tailWord_6536765 prefixEnd_6536765 3356502370487222610575471 := by
  unfold tailWord_6536765
  simp only [CollatzResearch.WordTrace]
  refine ⟨238415406163424270426715749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158943604108949513617810499 238415406163424270426715749)
  ·
    refine ⟨44702888655642050705009203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238415406163424270426715749 44702888655642050705009203)
    ·
      refine ⟨67054332983463076057513805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44702888655642050705009203 67054332983463076057513805)
      ·
        refine ⟨25145374868798653521567677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67054332983463076057513805 25145374868798653521567677)
        ·
          refine ⟨9429515575799495070587879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25145374868798653521567677 9429515575799495070587879)
          ·
            refine ⟨14144273363699242605881819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429515575799495070587879 14144273363699242605881819)
            ·
              refine ⟨21216410045548863908822729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144273363699242605881819 21216410045548863908822729)
              ·
                refine ⟨15912307534161647931617047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21216410045548863908822729 15912307534161647931617047)
                ·
                  refine ⟨23868461301242471897425571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15912307534161647931617047 23868461301242471897425571)
                  ·
                    refine ⟨35802691951863707846138357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23868461301242471897425571 35802691951863707846138357)
                    ·
                      refine ⟨3356502370487222610575471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35802691951863707846138357 3356502370487222610575471)
                      ·
                        rfl

theorem cell23_6536765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6536765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536765 prefixEnd_6536765 := by exact prefixLift 6536765
  have htrace : WordTrace (prefixWord ++ tailWord_6536765) baseStart_6536765 baseEnd_6536765 := by
    simpa [prefixWord, tailWord_6536765, baseEnd_6536765] using wordTrace_append hprefix tailTrace_6536765
  have hstable : (prefixWord ++ tailWord_6536765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536765).length < 2 ^ (prefixWord ++ tailWord_6536765).sum := by decide
  have hdescent : baseEnd_6536765 < baseStart_6536765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536790 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6536790 : Nat := 118140960795 + 6536790 * 2 ^ 59
def prefixEnd_6536790 : Nat := 4983230072969 + 3 ^ 40 * 6536790 * 2
def baseEnd_6536790 : Nat := 3356515207503585012762857

theorem tailTrace_6536790 : CollatzResearch.WordTrace tailWord_6536790 prefixEnd_6536790 3356515207503585012762857 := by
  unfold tailWord_6536790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901019874270856231023489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158944211992222466464250549 14901019874270856231023489)
  ·
    refine ⟨11175764905703142173267617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14901019874270856231023489 11175764905703142173267617)
    ·
      refine ⟨8381823679277356629950713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11175764905703142173267617 8381823679277356629950713)
      ·
        refine ⟨6286367759458017472463035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8381823679277356629950713 6286367759458017472463035)
        ·
          refine ⟨9429551639187026208694553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286367759458017472463035 9429551639187026208694553)
          ·
            refine ⟨7072163729390269656520915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9429551639187026208694553 7072163729390269656520915)
            ·
              refine ⟨10608245594085404484781373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072163729390269656520915 10608245594085404484781373)
              ·
                refine ⟨3978092097782026681793015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10608245594085404484781373 3978092097782026681793015)
                ·
                  refine ⟨5967138146673040022689523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978092097782026681793015 5967138146673040022689523)
                  ·
                    refine ⟨8950707220009560034034285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967138146673040022689523 8950707220009560034034285)
                    ·
                      refine ⟨3356515207503585012762857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950707220009560034034285 3356515207503585012762857)
                      ·
                        rfl

theorem cell23_6536790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6536790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536790 prefixEnd_6536790 := by exact prefixLift 6536790
  have htrace : WordTrace (prefixWord ++ tailWord_6536790) baseStart_6536790 baseEnd_6536790 := by
    simpa [prefixWord, tailWord_6536790, baseEnd_6536790] using wordTrace_append hprefix tailTrace_6536790
  have hstable : (prefixWord ++ tailWord_6536790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536790).length < 2 ^ (prefixWord ++ tailWord_6536790).sum := by decide
  have hdescent : baseEnd_6536790 < baseStart_6536790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536796 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6536796 : Nat := 118140960795 + 6536796 * 2 ^ 59
def prefixEnd_6536796 : Nat := 4983230072969 + 3 ^ 40 * 6536796 * 2
def baseEnd_6536796 : Nat := 3356518288387511989287829

theorem tailTrace_6536796 : CollatzResearch.WordTrace tailWord_6536796 prefixEnd_6536796 3356518288387511989287829 := by
  unfold tailWord_6536796
  simp only [CollatzResearch.WordTrace]
  refine ⟨119208268413155981360547121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158944357884207975147396161 119208268413155981360547121)
  ·
    refine ⟨89406201309866986020410341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119208268413155981360547121 89406201309866986020410341)
    ·
      refine ⟨16763662745600059878826939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89406201309866986020410341 16763662745600059878826939)
      ·
        refine ⟨25145494118400089818240409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16763662745600059878826939 25145494118400089818240409)
        ·
          refine ⟨18859120588800067363680307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25145494118400089818240409 18859120588800067363680307)
          ·
            refine ⟨28288680883200101045520461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859120588800067363680307 28288680883200101045520461)
            ·
              refine ⟨10608255331200037892070173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28288680883200101045520461 10608255331200037892070173)
              ·
                refine ⟨3978095749200014209526315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10608255331200037892070173 3978095749200014209526315)
                ·
                  refine ⟨5967143623800021314289473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978095749200014209526315 5967143623800021314289473)
                  ·
                    refine ⟨4475357717850015985717105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967143623800021314289473 4475357717850015985717105)
                    ·
                      refine ⟨3356518288387511989287829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475357717850015985717105 3356518288387511989287829)
                      ·
                        rfl

theorem cell23_6536796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6536796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536796 prefixEnd_6536796 := by exact prefixLift 6536796
  have htrace : WordTrace (prefixWord ++ tailWord_6536796) baseStart_6536796 baseEnd_6536796 := by
    simpa [prefixWord, tailWord_6536796, baseEnd_6536796] using wordTrace_append hprefix tailTrace_6536796
  have hstable : (prefixWord ++ tailWord_6536796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536796).length < 2 ^ (prefixWord ++ tailWord_6536796).sum := by decide
  have hdescent : baseEnd_6536796 < baseStart_6536796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536813 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6536813 : Nat := 118140960795 + 6536813 * 2 ^ 59
def prefixEnd_6536813 : Nat := 4983230072969 + 3 ^ 40 * 6536813 * 2
def baseEnd_6536813 : Nat := 3356527017558638422775251

theorem tailTrace_6536813 : CollatzResearch.WordTrace tailWord_6536813 prefixEnd_6536813 3356527017558638422775251 := by
  unfold tailWord_6536813
  simp only [CollatzResearch.WordTrace]
  refine ⟨238417156867250374624463093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158944771244833583082975395 238417156867250374624463093)
  ·
    refine ⟨22351608456304722621043415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238417156867250374624463093 22351608456304722621043415)
    ·
      refine ⟨33527412684457083931565123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351608456304722621043415 33527412684457083931565123)
      ·
        refine ⟨50291119026685625897347685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33527412684457083931565123 50291119026685625897347685)
        ·
          refine ⟨9429584817503554855752691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50291119026685625897347685 9429584817503554855752691)
          ·
            refine ⟨14144377226255332283629037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429584817503554855752691 14144377226255332283629037)
            ·
              refine ⟨5304141459845749606360889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14144377226255332283629037 5304141459845749606360889)
              ·
                refine ⟨3978106094884312204770667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304141459845749606360889 3978106094884312204770667)
                ·
                  refine ⟨5967159142326468307156001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978106094884312204770667 5967159142326468307156001)
                  ·
                    refine ⟨4475369356744851230367001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967159142326468307156001 4475369356744851230367001)
                    ·
                      refine ⟨3356527017558638422775251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475369356744851230367001 3356527017558638422775251)
                      ·
                        rfl

theorem cell23_6536813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6536813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536813 prefixEnd_6536813 := by exact prefixLift 6536813
  have htrace : WordTrace (prefixWord ++ tailWord_6536813) baseStart_6536813 baseEnd_6536813 := by
    simpa [prefixWord, tailWord_6536813, baseEnd_6536813] using wordTrace_append hprefix tailTrace_6536813
  have hstable : (prefixWord ++ tailWord_6536813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536813).length < 2 ^ (prefixWord ++ tailWord_6536813).sum := by decide
  have hdescent : baseEnd_6536813 < baseStart_6536813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536829 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_6536829 : Nat := 118140960795 + 6536829 * 2 ^ 59
def prefixEnd_6536829 : Nat := 4983230072969 + 3 ^ 40 * 6536829 * 2
def baseEnd_6536829 : Nat := 3356535233249110360175177

theorem tailTrace_6536829 : CollatzResearch.WordTrace tailWord_6536829 prefixEnd_6536829 3356535233249110360175177 := by
  unfold tailWord_6536829
  simp only [CollatzResearch.WordTrace]
  refine ⟨238417740435192409357045541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158945160290128272904697027 238417740435192409357045541)
  ·
    refine ⟨44703326331598576754446039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238417740435192409357045541 44703326331598576754446039)
    ·
      refine ⟨67054989497397865131669059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44703326331598576754446039 67054989497397865131669059)
      ·
        refine ⟨100582484246096797697503589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67054989497397865131669059 100582484246096797697503589)
        ·
          refine ⟨18859215796143149568281923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100582484246096797697503589 18859215796143149568281923)
          ·
            refine ⟨28288823694214724352422885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859215796143149568281923 28288823694214724352422885)
            ·
              refine ⟨5304154442665260816079291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28288823694214724352422885 5304154442665260816079291)
              ·
                refine ⟨7956231663997891224118937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5304154442665260816079291 7956231663997891224118937)
                ·
                  refine ⟨5967173747998418418089203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7956231663997891224118937 5967173747998418418089203)
                  ·
                    refine ⟨8950760621997627627133805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967173747998418418089203 8950760621997627627133805)
                    ·
                      refine ⟨3356535233249110360175177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950760621997627627133805 3356535233249110360175177)
                      ·
                        rfl

theorem cell23_6536829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_6536829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536829 prefixEnd_6536829 := by exact prefixLift 6536829
  have htrace : WordTrace (prefixWord ++ tailWord_6536829) baseStart_6536829 baseEnd_6536829 := by
    simpa [prefixWord, tailWord_6536829, baseEnd_6536829] using wordTrace_append hprefix tailTrace_6536829
  have hstable : (prefixWord ++ tailWord_6536829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536829).length < 2 ^ (prefixWord ++ tailWord_6536829).sum := by decide
  have hdescent : baseEnd_6536829 < baseStart_6536829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536835 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 1, 4, 2]
def baseStart_6536835 : Nat := 118140960795 + 6536835 * 2 ^ 59
def prefixEnd_6536835 : Nat := 4983230072969 + 3 ^ 40 * 6536835 * 2
def baseEnd_6536835 : Nat := 3356538314133037336700149

theorem tailTrace_6536835 : CollatzResearch.WordTrace tailWord_6536835 prefixEnd_6536835 3356538314133037336700149 := by
  unfold tailWord_6536835
  simp only [CollatzResearch.WordTrace]
  refine ⟨238417959273170672381763959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158945306182113781587842639 238417959273170672381763959)
  ·
    refine ⟨357626938909756008572645939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238417959273170672381763959 357626938909756008572645939)
    ·
      refine ⟨536440408364634012858968909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357626938909756008572645939 536440408364634012858968909)
      ·
        refine ⟨201165153136737754822113341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 536440408364634012858968909 201165153136737754822113341)
        ·
          refine ⟨75436932426276658058292503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201165153136737754822113341 75436932426276658058292503)
          ·
            refine ⟨113155398639414987087438755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75436932426276658058292503 113155398639414987087438755)
            ·
              refine ⟨169733097959122480631158133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113155398639414987087438755 169733097959122480631158133)
              ·
                refine ⟨15912477933667732559171075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169733097959122480631158133 15912477933667732559171075)
                ·
                  refine ⟨23868716900501598838756613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15912477933667732559171075 23868716900501598838756613)
                  ·
                    refine ⟨4475384418844049782266865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23868716900501598838756613 4475384418844049782266865)
                    ·
                      refine ⟨3356538314133037336700149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475384418844049782266865 3356538314133037336700149)
                      ·
                        rfl

theorem cell23_6536835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_6536835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536835 prefixEnd_6536835 := by exact prefixLift 6536835
  have htrace : WordTrace (prefixWord ++ tailWord_6536835) baseStart_6536835 baseEnd_6536835 := by
    simpa [prefixWord, tailWord_6536835, baseEnd_6536835] using wordTrace_append hprefix tailTrace_6536835
  have hstable : (prefixWord ++ tailWord_6536835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536835).length < 2 ^ (prefixWord ++ tailWord_6536835).sum := by decide
  have hdescent : baseEnd_6536835 < baseStart_6536835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536839 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_6536839 : Nat := 118140960795 + 6536839 * 2 ^ 59
def prefixEnd_6536839 : Nat := 4983230072969 + 3 ^ 40 * 6536839 * 2
def baseEnd_6536839 : Nat := 3356540368055655321050131

theorem tailTrace_6536839 : CollatzResearch.WordTrace tailWord_6536839 prefixEnd_6536839 3356540368055655321050131 := by
  unfold tailWord_6536839
  simp only [CollatzResearch.WordTrace]
  refine ⟨238418105165156181064909571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158945403443437454043273047 238418105165156181064909571)
  ·
    refine ⟨357627157747734271597364357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238418105165156181064909571 357627157747734271597364357)
    ·
      refine ⟨67055092077700175924505817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357627157747734271597364357 67055092077700175924505817)
      ·
        refine ⟨50291319058275131943379363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67055092077700175924505817 50291319058275131943379363)
        ·
          refine ⟨75436978587412697915069045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50291319058275131943379363 75436978587412697915069045)
          ·
            refine ⟨7072216742569940429537723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75436978587412697915069045 7072216742569940429537723)
            ·
              refine ⟨10608325113854910644306585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072216742569940429537723 10608325113854910644306585)
              ·
                refine ⟨7956243835391182983229939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10608325113854910644306585 7956243835391182983229939)
                ·
                  refine ⟨11934365753086774474844909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7956243835391182983229939 11934365753086774474844909)
                  ·
                    refine ⟨4475387157407540428066841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11934365753086774474844909 4475387157407540428066841)
                    ·
                      refine ⟨3356540368055655321050131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475387157407540428066841 3356540368055655321050131)
                      ·
                        rfl

theorem cell23_6536839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_6536839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536839 prefixEnd_6536839 := by exact prefixLift 6536839
  have htrace : WordTrace (prefixWord ++ tailWord_6536839) baseStart_6536839 baseEnd_6536839 := by
    simpa [prefixWord, tailWord_6536839, baseEnd_6536839] using wordTrace_append hprefix tailTrace_6536839
  have hstable : (prefixWord ++ tailWord_6536839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536839).length < 2 ^ (prefixWord ++ tailWord_6536839).sum := by decide
  have hdescent : baseEnd_6536839 < baseStart_6536839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536886 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6536886 : Nat := 118140960795 + 6536886 * 2 ^ 59
def prefixEnd_6536886 : Nat := 4983230072969 + 3 ^ 40 * 6536886 * 2
def baseEnd_6536886 : Nat := 3356564501646416637162415

theorem tailTrace_6536886 : CollatzResearch.WordTrace tailWord_6536886 prefixEnd_6536886 3356564501646416637162415 := by
  unfold tailWord_6536886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901238712249119255741907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158946546263990605394580341 14901238712249119255741907)
  ·
    refine ⟨22351858068373678883612861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14901238712249119255741907 22351858068373678883612861)
    ·
      refine ⟨8381946775640129581354823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22351858068373678883612861 8381946775640129581354823)
      ·
        refine ⟨12572920163460194372032235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381946775640129581354823 12572920163460194372032235)
        ·
          refine ⟨18859380245190291558048353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572920163460194372032235 18859380245190291558048353)
          ·
            refine ⟨14144535183892718668536265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18859380245190291558048353 14144535183892718668536265)
            ·
              refine ⟨10608401387919539001402199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14144535183892718668536265 10608401387919539001402199)
              ·
                refine ⟨15912602081879308502103299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10608401387919539001402199 15912602081879308502103299)
                ·
                  refine ⟨23868903122818962753154949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15912602081879308502103299 23868903122818962753154949)
                  ·
                    refine ⟨4475419335528555516216553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23868903122818962753154949 4475419335528555516216553)
                    ·
                      refine ⟨3356564501646416637162415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475419335528555516216553 3356564501646416637162415)
                      ·
                        rfl

theorem cell23_6536886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6536886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536886 prefixEnd_6536886 := by exact prefixLift 6536886
  have htrace : WordTrace (prefixWord ++ tailWord_6536886) baseStart_6536886 baseEnd_6536886 := by
    simpa [prefixWord, tailWord_6536886, baseEnd_6536886] using wordTrace_append hprefix tailTrace_6536886
  have hstable : (prefixWord ++ tailWord_6536886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536886).length < 2 ^ (prefixWord ++ tailWord_6536886).sum := by decide
  have hdescent : baseEnd_6536886 < baseStart_6536886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536888 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_6536888 : Nat := 118140960795 + 6536888 * 2 ^ 59
def prefixEnd_6536888 : Nat := 4983230072969 + 3 ^ 40 * 6536888 * 2
def baseEnd_6536888 : Nat := 1118855176202575209779135

theorem tailTrace_6536888 : CollatzResearch.WordTrace tailWord_6536888 prefixEnd_6536888 1118855176202575209779135 := by
  unfold tailWord_6536888
  simp only [CollatzResearch.WordTrace]
  refine ⟨119209946170989331216721659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158946594894652441622295545 119209946170989331216721659)
  ·
    refine ⟨178814919256483996825082489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119209946170989331216721659 178814919256483996825082489)
    ·
      refine ⟨134111189442362997618811867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178814919256483996825082489 134111189442362997618811867)
      ·
        refine ⟨201166784163544496428217801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134111189442362997618811867 201166784163544496428217801)
        ·
          refine ⟨150875088122658372321163351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201166784163544496428217801 150875088122658372321163351)
          ·
            refine ⟨226312632183987558481745027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150875088122658372321163351 226312632183987558481745027)
            ·
              refine ⟨339468948275981337722617541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226312632183987558481745027 339468948275981337722617541)
              ·
                refine ⟨63650427801746500822990789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339468948275981337722617541 63650427801746500822990789)
                ·
                  refine ⟨11934455212827468904310773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63650427801746500822990789 11934455212827468904310773)
                  ·
                    refine ⟨1118855176202575209779135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11934455212827468904310773 1118855176202575209779135)
                    ·
                      rfl

theorem cell23_6536888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_6536888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536888 prefixEnd_6536888 := by exact prefixLift 6536888
  have htrace : WordTrace (prefixWord ++ tailWord_6536888) baseStart_6536888 baseEnd_6536888 := by
    simpa [prefixWord, tailWord_6536888, baseEnd_6536888] using wordTrace_append hprefix tailTrace_6536888
  have hstable : (prefixWord ++ tailWord_6536888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536888).length < 2 ^ (prefixWord ++ tailWord_6536888).sum := by decide
  have hdescent : baseEnd_6536888 < baseStart_6536888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536895 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 5, 2]
def baseStart_6536895 : Nat := 118140960795 + 6536895 * 2 ^ 59
def prefixEnd_6536895 : Nat := 4983230072969 + 3 ^ 40 * 6536895 * 2
def baseEnd_6536895 : Nat := 3356569122972307101949873

theorem tailTrace_6536895 : CollatzResearch.WordTrace tailWord_6536895 prefixEnd_6536895 3356569122972307101949873 := by
  unfold tailWord_6536895
  simp only [CollatzResearch.WordTrace]
  refine ⟨238420147652953302628948139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158946765101968868419298759 238420147652953302628948139)
  ·
    refine ⟨357630221479429953943422209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238420147652953302628948139 357630221479429953943422209)
    ·
      refine ⟨268222666109572465457566657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357630221479429953943422209 268222666109572465457566657)
      ·
        refine ⟨201166999582179349093174993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268222666109572465457566657 201166999582179349093174993)
        ·
          refine ⟨150875249686634511819881245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201166999582179349093174993 150875249686634511819881245)
          ·
            refine ⟨56578218632487941932455467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150875249686634511819881245 56578218632487941932455467)
            ·
              refine ⟨84867327948731912898683201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56578218632487941932455467 84867327948731912898683201)
              ·
                refine ⟨63650495961548934674012401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84867327948731912898683201 63650495961548934674012401)
                ·
                  refine ⟨47737871971161701005509301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63650495961548934674012401 47737871971161701005509301)
                  ·
                    refine ⟨4475425497296409469266497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47737871971161701005509301 4475425497296409469266497)
                    ·
                      refine ⟨3356569122972307101949873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475425497296409469266497 3356569122972307101949873)
                      ·
                        rfl

theorem cell23_6536895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_6536895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536895 prefixEnd_6536895 := by exact prefixLift 6536895
  have htrace : WordTrace (prefixWord ++ tailWord_6536895) baseStart_6536895 baseEnd_6536895 := by
    simpa [prefixWord, tailWord_6536895, baseEnd_6536895] using wordTrace_append hprefix tailTrace_6536895
  have hstable : (prefixWord ++ tailWord_6536895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536895).length < 2 ^ (prefixWord ++ tailWord_6536895).sum := by decide
  have hdescent : baseEnd_6536895 < baseStart_6536895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536909 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 5]
def baseStart_6536909 : Nat := 118140960795 + 6536909 * 2 ^ 59
def prefixEnd_6536909 : Nat := 4983230072969 + 3 ^ 40 * 6536909 * 2
def baseEnd_6536909 : Nat := 372952923522385560797201

theorem tailTrace_6536909 : CollatzResearch.WordTrace tailWord_6536909 prefixEnd_6536909 372952923522385560797201 := by
  unfold tailWord_6536909
  simp only [CollatzResearch.WordTrace]
  refine ⟨238420658274902583019957781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158947105516601722013305187 238420658274902583019957781)
  ·
    refine ⟨11175968356636058579060521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238420658274902583019957781 11175968356636058579060521)
    ·
      refine ⟨8381976267477043934295391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11175968356636058579060521 8381976267477043934295391)
      ·
        refine ⟨12572964401215565901443087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381976267477043934295391 12572964401215565901443087)
        ·
          refine ⟨18859446601823348852164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572964401215565901443087 18859446601823348852164631)
          ·
            refine ⟨28289169902735023278246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859446601823348852164631 28289169902735023278246947)
            ·
              refine ⟨42433754854102534917370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28289169902735023278246947 42433754854102534917370421)
              ·
                refine ⟨3978164517572112648503477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42433754854102534917370421 3978164517572112648503477)
                ·
                  refine ⟨372952923522385560797201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978164517572112648503477 372952923522385560797201)
                  ·
                    rfl

theorem cell23_6536909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_6536909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536909 prefixEnd_6536909 := by exact prefixLift 6536909
  have htrace : WordTrace (prefixWord ++ tailWord_6536909) baseStart_6536909 baseEnd_6536909 := by
    simpa [prefixWord, tailWord_6536909, baseEnd_6536909] using wordTrace_append hprefix tailTrace_6536909
  have hstable : (prefixWord ++ tailWord_6536909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536909).length < 2 ^ (prefixWord ++ tailWord_6536909).sum := by decide
  have hdescent : baseEnd_6536909 < baseStart_6536909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536928 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6536928 : Nat := 118140960795 + 6536928 * 2 ^ 59
def prefixEnd_6536928 : Nat := 4983230072969 + 3 ^ 40 * 6536928 * 2
def baseEnd_6536928 : Nat := 3356586067833905472837221

theorem tailTrace_6536928 : CollatzResearch.WordTrace tailWord_6536928 prefixEnd_6536928 3356586067833905472837221 := by
  unfold tailWord_6536928
  simp only [CollatzResearch.WordTrace]
  refine ⟨119210675630916874632449719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158947567507889166176599625 119210675630916874632449719)
  ·
    refine ⟨178816013446375311948674579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119210675630916874632449719 178816013446375311948674579)
    ·
      refine ⟨268224020169562967923011869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178816013446375311948674579 268224020169562967923011869)
      ·
        refine ⟨100584007563586112971129451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268224020169562967923011869 100584007563586112971129451)
        ·
          refine ⟨150876011345379169456694177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100584007563586112971129451 150876011345379169456694177)
          ·
            refine ⟨113157008509034377092520633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150876011345379169456694177 113157008509034377092520633)
            ·
              refine ⟨84867756381775782819390475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113157008509034377092520633 84867756381775782819390475)
              ·
                refine ⟨127301634572663674229085713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84867756381775782819390475 127301634572663674229085713)
                ·
                  refine ⟨95476225929497755671814285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127301634572663674229085713 95476225929497755671814285)
                  ·
                    refine ⟨35803584723561658376930357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95476225929497755671814285 35803584723561658376930357)
                    ·
                      refine ⟨3356586067833905472837221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35803584723561658376930357 3356586067833905472837221)
                      ·
                        rfl

theorem cell23_6536928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6536928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536928 prefixEnd_6536928 := by exact prefixLift 6536928
  have htrace : WordTrace (prefixWord ++ tailWord_6536928) baseStart_6536928 baseEnd_6536928 := by
    simpa [prefixWord, tailWord_6536928, baseEnd_6536928] using wordTrace_append hprefix tailTrace_6536928
  have hstable : (prefixWord ++ tailWord_6536928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536928).length < 2 ^ (prefixWord ++ tailWord_6536928).sum := by decide
  have hdescent : baseEnd_6536928 < baseStart_6536928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536942 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_6536942 : Nat := 118140960795 + 6536942 * 2 ^ 59
def prefixEnd_6536942 : Nat := 4983230072969 + 3 ^ 40 * 6536942 * 2
def baseEnd_6536942 : Nat := 3356593256563068418062157

theorem tailTrace_6536942 : CollatzResearch.WordTrace tailWord_6536942 prefixEnd_6536942 3356593256563068418062157 := by
  unfold tailWord_6536942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29802732735472878706988635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158947907922522019770606053 29802732735472878706988635)
  ·
    refine ⟨44704099103209318060482953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29802732735472878706988635 44704099103209318060482953)
    ·
      refine ⟨33528074327406988545362215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44704099103209318060482953 33528074327406988545362215)
      ·
        refine ⟨50292111491110482818043323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33528074327406988545362215 50292111491110482818043323)
        ·
          refine ⟨75438167236665724227064985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50292111491110482818043323 75438167236665724227064985)
          ·
            refine ⟨56578625427499293170298739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75438167236665724227064985 56578625427499293170298739)
            ·
              refine ⟨84867938141248939755448109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56578625427499293170298739 84867938141248939755448109)
              ·
                refine ⟨31825476802968352408293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84867938141248939755448109 31825476802968352408293041)
                ·
                  refine ⟨23869107602226264306219781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31825476802968352408293041 23869107602226264306219781)
                  ·
                    refine ⟨4475457675417424557416209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23869107602226264306219781 4475457675417424557416209)
                    ·
                      refine ⟨3356593256563068418062157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475457675417424557416209 3356593256563068418062157)
                      ·
                        rfl

theorem cell23_6536942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_6536942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536942 prefixEnd_6536942 := by exact prefixLift 6536942
  have htrace : WordTrace (prefixWord ++ tailWord_6536942) baseStart_6536942 baseEnd_6536942 := by
    simpa [prefixWord, tailWord_6536942, baseEnd_6536942] using wordTrace_append hprefix tailTrace_6536942
  have hstable : (prefixWord ++ tailWord_6536942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536942).length < 2 ^ (prefixWord ++ tailWord_6536942).sum := by decide
  have hdescent : baseEnd_6536942 < baseStart_6536942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536945 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_6536945 : Nat := 118140960795 + 6536945 * 2 ^ 59
def prefixEnd_6536945 : Nat := 4983230072969 + 3 ^ 40 * 6536945 * 2
def baseEnd_6536945 : Nat := 3356594797005031906324643

theorem tailTrace_6536945 : CollatzResearch.WordTrace tailWord_6536945 prefixEnd_6536945 3356594797005031906324643 := by
  unfold tailWord_6536945
  simp only [CollatzResearch.WordTrace]
  refine ⟨238421971302772161168268289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158947980868514774112178859 238421971302772161168268289)
  ·
    refine ⟨178816478477079120876201217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238421971302772161168268289 178816478477079120876201217)
    ·
      refine ⟨134112358857809340657150913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178816478477079120876201217 134112358857809340657150913)
      ·
        refine ⟨100584269143357005492863185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134112358857809340657150913 100584269143357005492863185)
        ·
          refine ⟨75438201857517754119647389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100584269143357005492863185 75438201857517754119647389)
          ·
            refine ⟨28289325696569157794867771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75438201857517754119647389 28289325696569157794867771)
            ·
              refine ⟨42433988544853736692301657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28289325696569157794867771 42433988544853736692301657)
              ·
                refine ⟨31825491408640302519226243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42433988544853736692301657 31825491408640302519226243)
                ·
                  refine ⟨47738237112960453778839365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31825491408640302519226243 47738237112960453778839365)
                  ·
                    refine ⟨8950919458680085083532381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47738237112960453778839365 8950919458680085083532381)
                    ·
                      refine ⟨3356594797005031906324643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950919458680085083532381 3356594797005031906324643)
                      ·
                        rfl

theorem cell23_6536945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_6536945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536945 prefixEnd_6536945 := by exact prefixLift 6536945
  have htrace : WordTrace (prefixWord ++ tailWord_6536945) baseStart_6536945 baseEnd_6536945 := by
    simpa [prefixWord, tailWord_6536945, baseEnd_6536945] using wordTrace_append hprefix tailTrace_6536945
  have hstable : (prefixWord ++ tailWord_6536945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536945).length < 2 ^ (prefixWord ++ tailWord_6536945).sum := by decide
  have hdescent : baseEnd_6536945 < baseStart_6536945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536962 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_6536962 : Nat := 118140960795 + 6536962 * 2 ^ 59
def prefixEnd_6536962 : Nat := 4983230072969 + 3 ^ 40 * 6536962 * 2
def baseEnd_6536962 : Nat := 3356603526176158339812065

theorem tailTrace_6536962 : CollatzResearch.WordTrace tailWord_6536962 prefixEnd_6536962 3356603526176158339812065 := by
  unfold tailWord_6536962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59605647835927643267909285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158948394229140382047758093 59605647835927643267909285)
  ·
    refine ⟨11176058969236433112732991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59605647835927643267909285 11176058969236433112732991)
    ·
      refine ⟨16764088453854649669099487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11176058969236433112732991 16764088453854649669099487)
      ·
        refine ⟨25146132680781974503649231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16764088453854649669099487 25146132680781974503649231)
        ·
          refine ⟨37719199021172961755473847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25146132680781974503649231 37719199021172961755473847)
          ·
            refine ⟨56578798531759442633210771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37719199021172961755473847 56578798531759442633210771)
            ·
              refine ⟨84868197797639163949816157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56578798531759442633210771 84868197797639163949816157)
              ·
                refine ⟨31825574174114686481181059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84868197797639163949816157 31825574174114686481181059)
                ·
                  refine ⟨47738361261172029721771589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31825574174114686481181059 47738361261172029721771589)
                  ·
                    refine ⟨8950942736469755572832173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47738361261172029721771589 8950942736469755572832173)
                    ·
                      refine ⟨3356603526176158339812065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8950942736469755572832173 3356603526176158339812065)
                      ·
                        rfl

theorem cell23_6536962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_6536962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536962 prefixEnd_6536962 := by exact prefixLift 6536962
  have htrace : WordTrace (prefixWord ++ tailWord_6536962) baseStart_6536962 baseEnd_6536962 := by
    simpa [prefixWord, tailWord_6536962, baseEnd_6536962] using wordTrace_append hprefix tailTrace_6536962
  have hstable : (prefixWord ++ tailWord_6536962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536962).length < 2 ^ (prefixWord ++ tailWord_6536962).sum := by decide
  have hdescent : baseEnd_6536962 < baseStart_6536962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536973 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6536973 : Nat := 118140960795 + 6536973 * 2 ^ 59
def prefixEnd_6536973 : Nat := 4983230072969 + 3 ^ 40 * 6536973 * 2
def baseEnd_6536973 : Nat := 1118869724821119265591505

theorem tailTrace_6536973 : CollatzResearch.WordTrace tailWord_6536973 prefixEnd_6536973 1118869724821119265591505 := by
  unfold tailWord_6536973
  simp only [CollatzResearch.WordTrace]
  refine ⟨238422992546670721950287573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158948661697780481300191715 238422992546670721950287573)
  ·
    refine ⟨5588038887812595045709865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 238422992546670721950287573 5588038887812595045709865)
    ·
      refine ⟨4191029165859446284282399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5588038887812595045709865 4191029165859446284282399)
      ·
        refine ⟨6286543748789169426423599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191029165859446284282399 6286543748789169426423599)
        ·
          refine ⟨9429815623183754139635399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286543748789169426423599 9429815623183754139635399)
          ·
            refine ⟨14144723434775631209453099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429815623183754139635399 14144723434775631209453099)
            ·
              refine ⟨21217085152163446814179649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144723434775631209453099 21217085152163446814179649)
              ·
                refine ⟨15912813864122585110634737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21217085152163446814179649 15912813864122585110634737)
                ·
                  refine ⟨11934610398091938832976053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15912813864122585110634737 11934610398091938832976053)
                  ·
                    refine ⟨1118869724821119265591505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11934610398091938832976053 1118869724821119265591505)
                    ·
                      rfl

theorem cell23_6536973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6536973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536973 prefixEnd_6536973 := by exact prefixLift 6536973
  have htrace : WordTrace (prefixWord ++ tailWord_6536973) baseStart_6536973 baseEnd_6536973 := by
    simpa [prefixWord, tailWord_6536973, baseEnd_6536973] using wordTrace_append hprefix tailTrace_6536973
  have hstable : (prefixWord ++ tailWord_6536973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536973).length < 2 ^ (prefixWord ++ tailWord_6536973).sum := by decide
  have hdescent : baseEnd_6536973 < baseStart_6536973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6536986 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_6536986 : Nat := 118140960795 + 6536986 * 2 ^ 59
def prefixEnd_6536986 : Nat := 4983230072969 + 3 ^ 40 * 6536986 * 2
def baseEnd_6536986 : Nat := 1118871949903955415303985

theorem tailTrace_6536986 : CollatzResearch.WordTrace tailWord_6536986 prefixEnd_6536986 1118871949903955415303985 := by
  unfold tailWord_6536986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59605866673905906292627703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158948977797082416780340541 59605866673905906292627703)
  ·
    refine ⟨89408800010858859438941555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59605866673905906292627703 89408800010858859438941555)
    ·
      refine ⟨134113200016288289158412333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89408800010858859438941555 134113200016288289158412333)
      ·
        refine ⟨50292450006108108434404625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134113200016288289158412333 50292450006108108434404625)
        ·
          refine ⟨37719337504581081325803469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50292450006108108434404625 37719337504581081325803469)
          ·
            refine ⟨14144751564217905497176301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37719337504581081325803469 14144751564217905497176301)
            ·
              refine ⟨5304281836581714561441113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14144751564217905497176301 5304281836581714561441113)
              ·
                refine ⟨3978211377436285921080835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304281836581714561441113 3978211377436285921080835)
                ·
                  refine ⟨5967317066154428881621253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978211377436285921080835 5967317066154428881621253)
                  ·
                    refine ⟨1118871949903955415303985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5967317066154428881621253 1118871949903955415303985)
                    ·
                      rfl

theorem cell23_6536986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_6536986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6536986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6536986 prefixEnd_6536986 := by exact prefixLift 6536986
  have htrace : WordTrace (prefixWord ++ tailWord_6536986) baseStart_6536986 baseEnd_6536986 := by
    simpa [prefixWord, tailWord_6536986, baseEnd_6536986] using wordTrace_append hprefix tailTrace_6536986
  have hstable : (prefixWord ++ tailWord_6536986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6536986).length < 2 ^ (prefixWord ++ tailWord_6536986).sum := by decide
  have hdescent : baseEnd_6536986 < baseStart_6536986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6536986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537049 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 3, 2, 2]
def baseStart_6537049 : Nat := 118140960795 + 6537049 * 2 ^ 59
def prefixEnd_6537049 : Nat := 4983230072969 + 3 ^ 40 * 6537049 * 2
def baseEnd_6537049 : Nat := 3356648198993099499424165

theorem tailTrace_6537049 : CollatzResearch.WordTrace tailWord_6537049 prefixEnd_6537049 3356648198993099499424165 := by
  unfold tailWord_6537049
  simp only [CollatzResearch.WordTrace]
  refine ⟨238425764494395386930054201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158950509662930257953369467 238425764494395386930054201)
  ·
    refine ⟨178819323370796540197540651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238425764494395386930054201 178819323370796540197540651)
    ·
      refine ⟨268228985056194810296310977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178819323370796540197540651 268228985056194810296310977)
      ·
        refine ⟨201171738792146107722233233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268228985056194810296310977 201171738792146107722233233)
        ·
          refine ⟨150878804094109580791674925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201171738792146107722233233 150878804094109580791674925)
          ·
            refine ⟨56579551535291092796878097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150878804094109580791674925 56579551535291092796878097)
            ·
              refine ⟨42434663651468319597658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56579551535291092796878097 42434663651468319597658573)
              ·
                refine ⟨15912998869300619849121965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42434663651468319597658573 15912998869300619849121965)
                ·
                  refine ⟨5967374575987732443420737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15912998869300619849121965 5967374575987732443420737)
                  ·
                    refine ⟨4475530931990799332565553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5967374575987732443420737 4475530931990799332565553)
                    ·
                      refine ⟨3356648198993099499424165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4475530931990799332565553 3356648198993099499424165)
                      ·
                        rfl

theorem cell23_6537049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_6537049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537049 prefixEnd_6537049 := by exact prefixLift 6537049
  have htrace : WordTrace (prefixWord ++ tailWord_6537049) baseStart_6537049 baseEnd_6537049 := by
    simpa [prefixWord, tailWord_6537049, baseEnd_6537049] using wordTrace_append hprefix tailTrace_6537049
  have hstable : (prefixWord ++ tailWord_6537049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537049).length < 2 ^ (prefixWord ++ tailWord_6537049).sum := by decide
  have hdescent : baseEnd_6537049 < baseStart_6537049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537055 : List Nat := [1, 1, 2, 3, 1, 4, 3, 8]
def baseStart_6537055 : Nat := 118140960795 + 6537055 * 2 ^ 59
def prefixEnd_6537055 : Nat := 4983230072969 + 3 ^ 40 * 6537055 * 2
def baseEnd_6537055 : Nat := 124320417773223202812931

theorem tailTrace_6537055 : CollatzResearch.WordTrace tailWord_6537055 prefixEnd_6537055 124320417773223202812931 := by
  unfold tailWord_6537055
  simp only [CollatzResearch.WordTrace]
  refine ⟨238425983332373649954772619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158950655554915766636515079 238425983332373649954772619)
  ·
    refine ⟨357638974998560474932158929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238425983332373649954772619 357638974998560474932158929)
    ·
      refine ⟨268229231248920356199119197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357638974998560474932158929 268229231248920356199119197)
      ·
        refine ⟨100585961718345133574669699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268229231248920356199119197 100585961718345133574669699)
        ·
          refine ⟨150878942577517700362004549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100585961718345133574669699 150878942577517700362004549)
          ·
            refine ⟨28289801733284568817875853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150878942577517700362004549 28289801733284568817875853)
            ·
              refine ⟨10608675649981713306703445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28289801733284568817875853 10608675649981713306703445)
              ·
                refine ⟨124320417773223202812931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10608675649981713306703445 124320417773223202812931)
                ·
                  rfl

theorem cell23_6537055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 8].length) (baseStart_6537055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537055 prefixEnd_6537055 := by exact prefixLift 6537055
  have htrace : WordTrace (prefixWord ++ tailWord_6537055) baseStart_6537055 baseEnd_6537055 := by
    simpa [prefixWord, tailWord_6537055, baseEnd_6537055] using wordTrace_append hprefix tailTrace_6537055
  have hstable : (prefixWord ++ tailWord_6537055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537055).length < 2 ^ (prefixWord ++ tailWord_6537055).sum := by decide
  have hdescent : baseEnd_6537055 < baseStart_6537055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6537082 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_6537082 : Nat := 118140960795 + 6537082 * 2 ^ 59
def prefixEnd_6537082 : Nat := 4983230072969 + 3 ^ 40 * 6537082 * 2
def baseEnd_6537082 : Nat := 3356665143854697870311513

theorem tailTrace_6537082 : CollatzResearch.WordTrace tailWord_6537082 prefixEnd_6537082 3356665143854697870311513 := by
  unfold tailWord_6537082
  simp only [CollatzResearch.WordTrace]
  refine ⟨59606742025818958391501375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158951312068850555710670333 59606742025818958391501375)
  ·
    refine ⟨89410113038728437587252063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59606742025818958391501375 89410113038728437587252063)
    ·
      refine ⟨134115169558092656380878095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89410113038728437587252063 134115169558092656380878095)
      ·
        refine ⟨201172754337138984571317143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134115169558092656380878095 201172754337138984571317143)
        ·
          refine ⟨301759131505708476856975715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201172754337138984571317143 301759131505708476856975715)
          ·
            refine ⟨452638697258562715285463573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301759131505708476856975715 452638697258562715285463573)
            ·
              refine ⟨21217438933995127279006105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 452638697258562715285463573 21217438933995127279006105)
              ·
                refine ⟨15913079200496345459254579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21217438933995127279006105 15913079200496345459254579)
                ·
                  refine ⟨23869618800744518188881869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15913079200496345459254579 23869618800744518188881869)
                  ·
                    refine ⟨8951107050279194320830701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23869618800744518188881869 8951107050279194320830701)
                    ·
                      refine ⟨3356665143854697870311513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8951107050279194320830701 3356665143854697870311513)
                      ·
                        rfl

theorem cell23_6537082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_6537082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6537082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6537082 prefixEnd_6537082 := by exact prefixLift 6537082
  have htrace : WordTrace (prefixWord ++ tailWord_6537082) baseStart_6537082 baseEnd_6537082 := by
    simpa [prefixWord, tailWord_6537082, baseEnd_6537082] using wordTrace_append hprefix tailTrace_6537082
  have hstable : (prefixWord ++ tailWord_6537082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6537082).length < 2 ^ (prefixWord ++ tailWord_6537082).sum := by decide
  have hdescent : baseEnd_6537082 < baseStart_6537082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6537082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
