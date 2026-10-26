import V185TrunkScan23Chunk0792

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4690169 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4690169 : Nat := 118140960795 + 4690169 * 2 ^ 59
def prefixEnd_4690169 : Nat := 4983230072969 + 3 ^ 40 * 4690169 * 2
def baseEnd_4690169 : Nat := 2408311047817365425917811

theorem tailTrace_4690169 : CollatzResearch.WordTrace tailWord_4690169 prefixEnd_4690169 2408311047817365425917811 := by
  unfold tailWord_4690169
  simp only [CollatzResearch.WordTrace]
  refine ⟨171064516945326204938081561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114043011296884136625387707 171064516945326204938081561)
  ·
    refine ⟨128298387708994653703561171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171064516945326204938081561 128298387708994653703561171)
    ·
      refine ⟨192447581563491980555341757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128298387708994653703561171 192447581563491980555341757)
      ·
        refine ⟨72167843086309492708253159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192447581563491980555341757 72167843086309492708253159)
        ·
          refine ⟨108251764629464239062379739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72167843086309492708253159 108251764629464239062379739)
          ·
            refine ⟨162377646944196358593569609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108251764629464239062379739 162377646944196358593569609)
            ·
              refine ⟨121783235208147268945177207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162377646944196358593569609 121783235208147268945177207)
              ·
                refine ⟨182674852812220903417765811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121783235208147268945177207 182674852812220903417765811)
                ·
                  refine ⟨274012279218331355126648717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182674852812220903417765811 274012279218331355126648717)
                  ·
                    refine ⟨102754604706874258172493269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274012279218331355126648717 102754604706874258172493269)
                    ·
                      refine ⟨2408311047817365425917811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102754604706874258172493269 2408311047817365425917811)
                      ·
                        rfl

theorem cell23_4690169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4690169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690169 prefixEnd_4690169 := by exact prefixLift 4690169
  have htrace : WordTrace (prefixWord ++ tailWord_4690169) baseStart_4690169 baseEnd_4690169 := by
    simpa [prefixWord, tailWord_4690169, baseEnd_4690169] using wordTrace_append hprefix tailTrace_4690169
  have hstable : (prefixWord ++ tailWord_4690169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690169).length < 2 ^ (prefixWord ++ tailWord_4690169).sum := by decide
  have hdescent : baseEnd_4690169 < baseStart_4690169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690173 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_4690173 : Nat := 118140960795 + 4690173 * 2 ^ 59
def prefixEnd_4690173 : Nat := 4983230072969 + 3 ^ 40 * 4690173 * 2
def baseEnd_4690173 : Nat := 2408313101739983410267793

theorem tailTrace_4690173 : CollatzResearch.WordTrace tailWord_4690173 prefixEnd_4690173 2408313101739983410267793 := by
  unfold tailWord_4690173
  simp only [CollatzResearch.WordTrace]
  refine ⟨171064662837311713621227173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114043108558207809080818115 171064662837311713621227173)
  ·
    refine ⟨32074624281995946303980095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171064662837311713621227173 32074624281995946303980095)
    ·
      refine ⟨48111936422993919455970143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32074624281995946303980095 48111936422993919455970143)
      ·
        refine ⟨72167904634490879183955215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48111936422993919455970143 72167904634490879183955215)
        ·
          refine ⟨108251856951736318775932823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72167904634490879183955215 108251856951736318775932823)
          ·
            refine ⟨162377785427604478163899235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108251856951736318775932823 162377785427604478163899235)
            ·
              refine ⟨243566678141406717245848853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162377785427604478163899235 243566678141406717245848853)
              ·
                refine ⟨11417188037878439870899165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243566678141406717245848853 11417188037878439870899165)
                ·
                  refine ⟨4281445514204414951587187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11417188037878439870899165 4281445514204414951587187)
                  ·
                    refine ⟨6422168271306622427380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281445514204414951587187 6422168271306622427380781)
                    ·
                      refine ⟨2408313101739983410267793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422168271306622427380781 2408313101739983410267793)
                      ·
                        rfl

theorem cell23_4690173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_4690173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690173 prefixEnd_4690173 := by exact prefixLift 4690173
  have htrace : WordTrace (prefixWord ++ tailWord_4690173) baseStart_4690173 baseEnd_4690173 := by
    simpa [prefixWord, tailWord_4690173, baseEnd_4690173] using wordTrace_append hprefix tailTrace_4690173
  have hstable : (prefixWord ++ tailWord_4690173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690173).length < 2 ^ (prefixWord ++ tailWord_4690173).sum := by decide
  have hdescent : baseEnd_4690173 < baseStart_4690173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690207 : List Nat := [1, 1, 2, 4, 3, 2, 1, 4, 1, 1, 3]
def baseStart_4690207 : Nat := 118140960795 + 4690207 * 2 ^ 59
def prefixEnd_4690207 : Nat := 4983230072969 + 3 ^ 40 * 4690207 * 2
def baseEnd_4690207 : Nat := 2408330560082236277242637

theorem tailTrace_4690207 : CollatzResearch.WordTrace tailWord_4690207 prefixEnd_4690207 2408330560082236277242637 := by
  unfold tailWord_4690207
  simp only [CollatzResearch.WordTrace]
  refine ⟨171065902919188537427964875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114043935279459024951976583 171065902919188537427964875)
  ·
    refine ⟨256598854378782806141947313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171065902919188537427964875 256598854378782806141947313)
    ·
      refine ⟨192449140784087104606460485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256598854378782806141947313 192449140784087104606460485)
      ·
        refine ⟨36084213897016332113711341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192449140784087104606460485 36084213897016332113711341)
        ·
          refine ⟨13531580211381124542641753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36084213897016332113711341 13531580211381124542641753)
          ·
            refine ⟨10148685158535843406981315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13531580211381124542641753 10148685158535843406981315)
            ·
              refine ⟨15223027737803765110471973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10148685158535843406981315 15223027737803765110471973)
              ·
                refine ⟨2854317700838205958213495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15223027737803765110471973 2854317700838205958213495)
                ·
                  refine ⟨4281476551257308937320243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854317700838205958213495 4281476551257308937320243)
                  ·
                    refine ⟨6422214826885963405980365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4281476551257308937320243 6422214826885963405980365)
                    ·
                      refine ⟨2408330560082236277242637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422214826885963405980365 2408330560082236277242637)
                      ·
                        rfl

theorem cell23_4690207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_4690207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690207 prefixEnd_4690207 := by exact prefixLift 4690207
  have htrace : WordTrace (prefixWord ++ tailWord_4690207) baseStart_4690207 baseEnd_4690207 := by
    simpa [prefixWord, tailWord_4690207, baseEnd_4690207] using wordTrace_append hprefix tailTrace_4690207
  have hstable : (prefixWord ++ tailWord_4690207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690207).length < 2 ^ (prefixWord ++ tailWord_4690207).sum := by decide
  have hdescent : baseEnd_4690207 < baseStart_4690207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690223 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 2, 4]
def baseStart_4690223 : Nat := 118140960795 + 4690223 * 2 ^ 59
def prefixEnd_4690223 : Nat := 4983230072969 + 3 ^ 40 * 4690223 * 2
def baseEnd_4690223 : Nat := 802779591924236071547521

theorem tailTrace_4690223 : CollatzResearch.WordTrace tailWord_4690223 prefixEnd_4690223 802779591924236071547521 := by
  unfold tailWord_4690223
  simp only [CollatzResearch.WordTrace]
  refine ⟨171066486487130572160547323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114044324324753714773698215 171066486487130572160547323)
  ·
    refine ⟨256599729730695858240820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171066486487130572160547323 256599729730695858240820985)
    ·
      refine ⟨192449797298021893680615739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256599729730695858240820985 192449797298021893680615739)
      ·
        refine ⟨288674695947032840520923609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192449797298021893680615739 288674695947032840520923609)
        ·
          refine ⟨216506021960274630390692707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288674695947032840520923609 216506021960274630390692707)
          ·
            refine ⟨324759032940411945586039061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216506021960274630390692707 324759032940411945586039061)
            ·
              refine ⟨15223079669081809949345581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324759032940411945586039061 15223079669081809949345581)
              ·
                refine ⟨5708654875905678731004593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15223079669081809949345581 5708654875905678731004593)
                ·
                  refine ⟨4281491156929259048253445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5708654875905678731004593 4281491156929259048253445)
                  ·
                    refine ⟨802779591924236071547521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4281491156929259048253445 802779591924236071547521)
                    ·
                      rfl

theorem cell23_4690223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_4690223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690223 prefixEnd_4690223 := by exact prefixLift 4690223
  have htrace : WordTrace (prefixWord ++ tailWord_4690223) baseStart_4690223 baseEnd_4690223 := by
    simpa [prefixWord, tailWord_4690223, baseEnd_4690223] using wordTrace_append hprefix tailTrace_4690223
  have hstable : (prefixWord ++ tailWord_4690223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690223).length < 2 ^ (prefixWord ++ tailWord_4690223).sum := by decide
  have hdescent : baseEnd_4690223 < baseStart_4690223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690244 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4690244 : Nat := 118140960795 + 4690244 * 2 ^ 59
def prefixEnd_4690244 : Nat := 4983230072969 + 3 ^ 40 * 4690244 * 2
def baseEnd_4690244 : Nat := 802783186288817544159989

theorem tailTrace_4690244 : CollatzResearch.WordTrace tailWord_4690244 prefixEnd_4690244 802783186288817544159989 := by
  unfold tailWord_4690244
  simp only [CollatzResearch.WordTrace]
  refine ⟨85533626210027246373530893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114044834946702995164707857 85533626210027246373530893)
  ·
    refine ⟨32075109828760217390074085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85533626210027246373530893 32075109828760217390074085)
    ·
      refine ⟨6014083092892540760638891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32075109828760217390074085 6014083092892540760638891)
      ·
        refine ⟨9021124639338811140958337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014083092892540760638891 9021124639338811140958337)
        ·
          refine ⟨6765843479504108355718753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9021124639338811140958337 6765843479504108355718753)
          ·
            refine ⟨5074382609628081266789065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6765843479504108355718753 5074382609628081266789065)
            ·
              refine ⟨3805786957221060950091799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5074382609628081266789065 3805786957221060950091799)
              ·
                refine ⟨5708680435831591425137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805786957221060950091799 5708680435831591425137699)
                ·
                  refine ⟨8563020653747387137706549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708680435831591425137699 8563020653747387137706549)
                  ·
                    refine ⟨802783186288817544159989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8563020653747387137706549 802783186288817544159989)
                    ·
                      rfl

theorem cell23_4690244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4690244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690244 prefixEnd_4690244 := by exact prefixLift 4690244
  have htrace : WordTrace (prefixWord ++ tailWord_4690244) baseStart_4690244 baseEnd_4690244 := by
    simpa [prefixWord, tailWord_4690244, baseEnd_4690244] using wordTrace_append hprefix tailTrace_4690244
  have hstable : (prefixWord ++ tailWord_4690244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690244).length < 2 ^ (prefixWord ++ tailWord_4690244).sum := by decide
  have hdescent : baseEnd_4690244 < baseStart_4690244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690280 : List Nat := [2, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4690280 : Nat := 118140960795 + 4690280 * 2 ^ 59
def prefixEnd_4690280 : Nat := 4983230072969 + 3 ^ 40 * 4690280 * 2
def baseEnd_4690280 : Nat := 2408368044170014491629801

theorem tailTrace_4690280 : CollatzResearch.WordTrace tailWord_4690280 prefixEnd_4690280 2408368044170014491629801 := by
  unfold tailWord_4690280
  simp only [CollatzResearch.WordTrace]
  refine ⟨85534282723962035447686147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114045710298616047263581529 85534282723962035447686147)
  ·
    refine ⟨128301424085943053171529221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85534282723962035447686147 128301424085943053171529221)
    ·
      refine ⟨24056517016114322469661729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128301424085943053171529221 24056517016114322469661729)
      ·
        refine ⟨18042387762085741852246297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24056517016114322469661729 18042387762085741852246297)
        ·
          refine ⟨13531790821564306389184723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18042387762085741852246297 13531790821564306389184723)
          ·
            refine ⟨20297686232346459583777085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13531790821564306389184723 20297686232346459583777085)
            ·
              refine ⟨7611632337129922343916407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20297686232346459583777085 7611632337129922343916407)
              ·
                refine ⟨11417448505694883515874611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611632337129922343916407 11417448505694883515874611)
                ·
                  refine ⟨17126172758542325273811917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11417448505694883515874611 17126172758542325273811917)
                  ·
                    refine ⟨6422314784453371977679469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17126172758542325273811917 6422314784453371977679469)
                    ·
                      refine ⟨2408368044170014491629801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422314784453371977679469 2408368044170014491629801)
                      ·
                        rfl

theorem cell23_4690280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4690280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690280 prefixEnd_4690280 := by exact prefixLift 4690280
  have htrace : WordTrace (prefixWord ++ tailWord_4690280) baseStart_4690280 baseEnd_4690280 := by
    simpa [prefixWord, tailWord_4690280, baseEnd_4690280] using wordTrace_append hprefix tailTrace_4690280
  have hstable : (prefixWord ++ tailWord_4690280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690280).length < 2 ^ (prefixWord ++ tailWord_4690280).sum := by decide
  have hdescent : baseEnd_4690280 < baseStart_4690280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690293 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4690293 : Nat := 118140960795 + 4690293 * 2 ^ 59
def prefixEnd_4690293 : Nat := 4983230072969 + 3 ^ 40 * 4690293 * 2
def baseEnd_4690293 : Nat := 2408374719418522940767241

theorem tailTrace_4690293 : CollatzResearch.WordTrace tailWord_4690293 prefixEnd_4690293 2408374719418522940767241 := by
  unfold tailWord_4690293
  simp only [CollatzResearch.WordTrace]
  refine ⟨171069039596876974115595533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114046026397917982743730355 171069039596876974115595533)
  ·
    refine ⟨64150889848828865293348325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171069039596876974115595533 64150889848828865293348325)
    ·
      refine ⟨12028291846655412242502811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64150889848828865293348325 12028291846655412242502811)
      ·
        refine ⟨18042437769983118363754217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028291846655412242502811 18042437769983118363754217)
        ·
          refine ⟨13531828327487338772815663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18042437769983118363754217 13531828327487338772815663)
          ·
            refine ⟨20297742491231008159223495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13531828327487338772815663 20297742491231008159223495)
            ·
              refine ⟨30446613736846512238835243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20297742491231008159223495 30446613736846512238835243)
              ·
                refine ⟨45669920605269768358252865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30446613736846512238835243 45669920605269768358252865)
                ·
                  refine ⟨34252440453952326268689649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45669920605269768358252865 34252440453952326268689649)
                  ·
                    refine ⟨25689330340464244701517237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34252440453952326268689649 25689330340464244701517237)
                    ·
                      refine ⟨2408374719418522940767241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25689330340464244701517237 2408374719418522940767241)
                      ·
                        rfl

theorem cell23_4690293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4690293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690293 prefixEnd_4690293 := by exact prefixLift 4690293
  have htrace : WordTrace (prefixWord ++ tailWord_4690293) baseStart_4690293 baseEnd_4690293 := by
    simpa [prefixWord, tailWord_4690293, baseEnd_4690293] using wordTrace_append hprefix tailTrace_4690293
  have hstable : (prefixWord ++ tailWord_4690293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690293).length < 2 ^ (prefixWord ++ tailWord_4690293).sum := by decide
  have hdescent : baseEnd_4690293 < baseStart_4690293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690390 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4690390 : Nat := 118140960795 + 4690390 * 2 ^ 59
def prefixEnd_4690390 : Nat := 4983230072969 + 3 ^ 40 * 4690390 * 2
def baseEnd_4690390 : Nat := 802808175680669687084765

theorem tailTrace_4690390 : CollatzResearch.WordTrace tailWord_4690390 prefixEnd_4690390 802808175680669687084765 := by
  unfold tailWord_4690390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692036092345347480117289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114048384985017039787917749 10692036092345347480117289)
  ·
    refine ⟨8019027069259010610087967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10692036092345347480117289 8019027069259010610087967)
    ·
      refine ⟨12028540603888515915131951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8019027069259010610087967 12028540603888515915131951)
      ·
        refine ⟨18042810905832773872697927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028540603888515915131951 18042810905832773872697927)
        ·
          refine ⟨27064216358749160809046891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18042810905832773872697927 27064216358749160809046891)
          ·
            refine ⟨40596324538123741213570337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064216358749160809046891 40596324538123741213570337)
            ·
              refine ⟨30447243403592805910177753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40596324538123741213570337 30447243403592805910177753)
              ·
                refine ⟨22835432552694604432633315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30447243403592805910177753 22835432552694604432633315)
                ·
                  refine ⟨34253148829041906648949973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22835432552694604432633315 34253148829041906648949973)
                  ·
                    refine ⟨802808175680669687084765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34253148829041906648949973 802808175680669687084765)
                    ·
                      rfl

theorem cell23_4690390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4690390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690390 prefixEnd_4690390 := by exact prefixLift 4690390
  have htrace : WordTrace (prefixWord ++ tailWord_4690390) baseStart_4690390 baseEnd_4690390 := by
    simpa [prefixWord, tailWord_4690390, baseEnd_4690390] using wordTrace_append hprefix tailTrace_4690390
  have hstable : (prefixWord ++ tailWord_4690390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690390).length < 2 ^ (prefixWord ++ tailWord_4690390).sum := by decide
  have hdescent : baseEnd_4690390 < baseStart_4690390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690393 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 4]
def baseStart_4690393 : Nat := 118140960795 + 4690393 * 2 ^ 59
def prefixEnd_4690393 : Nat := 4983230072969 + 3 ^ 40 * 4690393 * 2
def baseEnd_4690393 : Nat := 2408426067483972549516781

theorem tailTrace_4690393 : CollatzResearch.WordTrace tailWord_4690393 prefixEnd_4690393 2408426067483972549516781 := by
  unfold tailWord_4690393
  simp only [CollatzResearch.WordTrace]
  refine ⟨171072686896514691194235833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114048457931009794129490555 171072686896514691194235833)
  ·
    refine ⟨128304515172386018395676875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171072686896514691194235833 128304515172386018395676875)
    ·
      refine ⟨192456772758579027593515313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128304515172386018395676875 192456772758579027593515313)
      ·
        refine ⟨144342579568934270695136485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192456772758579027593515313 144342579568934270695136485)
        ·
          refine ⟨27064233669175175755338091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144342579568934270695136485 27064233669175175755338091)
          ·
            refine ⟨40596350503762763633007137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064233669175175755338091 40596350503762763633007137)
            ·
              refine ⟨30447262877822072724755353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40596350503762763633007137 30447262877822072724755353)
              ·
                refine ⟨22835447158366554543566515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30447262877822072724755353 22835447158366554543566515)
                ·
                  refine ⟨34253170737549831815349773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22835447158366554543566515 34253170737549831815349773)
                  ·
                    refine ⟨12844939026581186930756165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34253170737549831815349773 12844939026581186930756165)
                    ·
                      refine ⟨2408426067483972549516781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12844939026581186930756165 2408426067483972549516781)
                      ·
                        rfl

theorem cell23_4690393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_4690393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690393 prefixEnd_4690393 := by exact prefixLift 4690393
  have htrace : WordTrace (prefixWord ++ tailWord_4690393) baseStart_4690393 baseEnd_4690393 := by
    simpa [prefixWord, tailWord_4690393, baseEnd_4690393] using wordTrace_append hprefix tailTrace_4690393
  have hstable : (prefixWord ++ tailWord_4690393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690393).length < 2 ^ (prefixWord ++ tailWord_4690393).sum := by decide
  have hdescent : baseEnd_4690393 < baseStart_4690393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690410 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_4690410 : Nat := 118140960795 + 4690410 * 2 ^ 59
def prefixEnd_4690410 : Nat := 4983230072969 + 3 ^ 40 * 4690410 * 2
def baseEnd_4690410 : Nat := 2408434796655098983004203

theorem tailTrace_4690410 : CollatzResearch.WordTrace tailWord_4690410 prefixEnd_4690410 2408434796655098983004203 := by
  unfold tailWord_4690410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42768326734363275774401171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114048871291635402065069789 42768326734363275774401171)
  ·
    refine ⟨64152490101544913661601757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42768326734363275774401171 64152490101544913661601757)
    ·
      refine ⟨24057183788079342623100659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64152490101544913661601757 24057183788079342623100659)
      ·
        refine ⟨36085775682119013934650989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24057183788079342623100659 36085775682119013934650989)
        ·
          refine ⟨13532165880794630225494121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36085775682119013934650989 13532165880794630225494121)
          ·
            refine ⟨10149124410595972669120591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13532165880794630225494121 10149124410595972669120591)
            ·
              refine ⟨15223686615893959003680887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10149124410595972669120591 15223686615893959003680887)
              ·
                refine ⟨22835529923840938505521331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15223686615893959003680887 22835529923840938505521331)
                ·
                  refine ⟨34253294885761407758281997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22835529923840938505521331 34253294885761407758281997)
                  ·
                    refine ⟨12844985582160527909355749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34253294885761407758281997 12844985582160527909355749)
                    ·
                      refine ⟨2408434796655098983004203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12844985582160527909355749 2408434796655098983004203)
                      ·
                        rfl

theorem cell23_4690410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_4690410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690410 prefixEnd_4690410 := by exact prefixLift 4690410
  have htrace : WordTrace (prefixWord ++ tailWord_4690410) baseStart_4690410 baseEnd_4690410 := by
    simpa [prefixWord, tailWord_4690410, baseEnd_4690410] using wordTrace_append hprefix tailTrace_4690410
  have hstable : (prefixWord ++ tailWord_4690410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690410).length < 2 ^ (prefixWord ++ tailWord_4690410).sum := by decide
  have hdescent : baseEnd_4690410 < baseStart_4690410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690437 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_4690437 : Nat := 118140960795 + 4690437 * 2 ^ 59
def prefixEnd_4690437 : Nat := 4983230072969 + 3 ^ 40 * 4690437 * 2
def baseEnd_4690437 : Nat := 802816220210923459122193

theorem tailTrace_4690437 : CollatzResearch.WordTrace tailWord_4690437 prefixEnd_4690437 802816220210923459122193 := by
  unfold tailWord_4690437
  simp only [CollatzResearch.WordTrace]
  refine ⟨171074291708355286708837565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114049527805570191139225043 171074291708355286708837565)
  ·
    refine ⟨64152859390633232515814087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171074291708355286708837565 64152859390633232515814087)
    ·
      refine ⟨96229289085949848773721131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64152859390633232515814087 96229289085949848773721131)
      ·
        refine ⟨144343933628924773160581697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96229289085949848773721131 144343933628924773160581697)
        ·
          refine ⟨108257950221693579870436273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144343933628924773160581697 108257950221693579870436273)
          ·
            refine ⟨81193462666270184902827205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108257950221693579870436273 81193462666270184902827205)
            ·
              refine ⟨15223774249925659669280101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81193462666270184902827205 15223774249925659669280101)
              ·
                refine ⟨2854457671861061187990019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15223774249925659669280101 2854457671861061187990019)
                ·
                  refine ⟨4281686507791591781985029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854457671861061187990019 4281686507791591781985029)
                  ·
                    refine ⟨802816220210923459122193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4281686507791591781985029 802816220210923459122193)
                    ·
                      rfl

theorem cell23_4690437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_4690437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690437 prefixEnd_4690437 := by exact prefixLift 4690437
  have htrace : WordTrace (prefixWord ++ tailWord_4690437) baseStart_4690437 baseEnd_4690437 := by
    simpa [prefixWord, tailWord_4690437, baseEnd_4690437] using wordTrace_append hprefix tailTrace_4690437
  have hstable : (prefixWord ++ tailWord_4690437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690437).length < 2 ^ (prefixWord ++ tailWord_4690437).sum := by decide
  have hdescent : baseEnd_4690437 < baseStart_4690437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690453 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4690453 : Nat := 118140960795 + 4690453 * 2 ^ 59
def prefixEnd_4690453 : Nat := 4983230072969 + 3 ^ 40 * 4690453 * 2
def baseEnd_4690453 : Nat := 2408456876323242314766505

theorem tailTrace_4690453 : CollatzResearch.WordTrace tailWord_4690453 prefixEnd_4690453 2408456876323242314766505 := by
  unfold tailWord_4690453
  simp only [CollatzResearch.WordTrace]
  refine ⟨171074875276297321441420013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114049916850864880960946675 171074875276297321441420013)
  ·
    refine ⟨64153078228611495540532505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171074875276297321441420013 64153078228611495540532505)
    ·
      refine ⟨48114808671458621655399379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64153078228611495540532505 48114808671458621655399379)
      ·
        refine ⟨72172213007187932483099069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48114808671458621655399379 72172213007187932483099069)
        ·
          refine ⟨27064579877695474681162151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72172213007187932483099069 27064579877695474681162151)
          ·
            refine ⟨40596869816543212021743227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064579877695474681162151 40596869816543212021743227)
            ·
              refine ⟨60895304724814818032614841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40596869816543212021743227 60895304724814818032614841)
              ·
                refine ⟨45671478543611113524461131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60895304724814818032614841 45671478543611113524461131)
                ·
                  refine ⟨68507217815416670286691697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45671478543611113524461131 68507217815416670286691697)
                  ·
                    refine ⟨51380413361562502715018773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68507217815416670286691697 51380413361562502715018773)
                    ·
                      refine ⟨2408456876323242314766505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51380413361562502715018773 2408456876323242314766505)
                      ·
                        rfl

theorem cell23_4690453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4690453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690453 prefixEnd_4690453 := by exact prefixLift 4690453
  have htrace : WordTrace (prefixWord ++ tailWord_4690453) baseStart_4690453 baseEnd_4690453 := by
    simpa [prefixWord, tailWord_4690453, baseEnd_4690453] using wordTrace_append hprefix tailTrace_4690453
  have hstable : (prefixWord ++ tailWord_4690453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690453).length < 2 ^ (prefixWord ++ tailWord_4690453).sum := by decide
  have hdescent : baseEnd_4690453 < baseStart_4690453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690480 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_4690480 : Nat := 118140960795 + 4690480 * 2 ^ 59
def prefixEnd_4690480 : Nat := 4983230072969 + 3 ^ 40 * 4690480 * 2
def baseEnd_4690480 : Nat := 802823580100304569709627

theorem tailTrace_4690480 : CollatzResearch.WordTrace tailWord_4690480 prefixEnd_4690480 802823580100304569709627 := by
  unfold tailWord_4690480
  simp only [CollatzResearch.WordTrace]
  refine ⟨85537930023599752526326447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114050573364799670035101929 85537930023599752526326447)
  ·
    refine ⟨128306895035399628789489671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85537930023599752526326447 128306895035399628789489671)
    ·
      refine ⟨192460342553099443184234507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128306895035399628789489671 192460342553099443184234507)
      ·
        refine ⟨288690513829649164776351761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192460342553099443184234507 288690513829649164776351761)
        ·
          refine ⟨216517885372236873582263821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288690513829649164776351761 216517885372236873582263821)
          ·
            refine ⟨81194207014588827593348933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216517885372236873582263821 81194207014588827593348933)
            ·
              refine ⟨15223913815235405173752925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81194207014588827593348933 15223913815235405173752925)
              ·
                refine ⟨5708967680713276940157347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15223913815235405173752925 5708967680713276940157347)
                ·
                  refine ⟨8563451521069915410236021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708967680713276940157347 8563451521069915410236021)
                  ·
                    refine ⟨802823580100304569709627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8563451521069915410236021 802823580100304569709627)
                    ·
                      rfl

theorem cell23_4690480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_4690480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690480 prefixEnd_4690480 := by exact prefixLift 4690480
  have htrace : WordTrace (prefixWord ++ tailWord_4690480) baseStart_4690480 baseEnd_4690480 := by
    simpa [prefixWord, tailWord_4690480, baseEnd_4690480] using wordTrace_append hprefix tailTrace_4690480
  have hstable : (prefixWord ++ tailWord_4690480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690480).length < 2 ^ (prefixWord ++ tailWord_4690480).sum := by decide
  have hdescent : baseEnd_4690480 < baseStart_4690480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690487 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_4690487 : Nat := 118140960795 + 4690487 * 2 ^ 59
def prefixEnd_4690487 : Nat := 4983230072969 + 3 ^ 40 * 4690487 * 2
def baseEnd_4690487 : Nat := 2408474334665495181741349

theorem tailTrace_4690487 : CollatzResearch.WordTrace tailWord_4690487 prefixEnd_4690487 2408474334665495181741349 := by
  unfold tailWord_4690487
  simp only [CollatzResearch.WordTrace]
  refine ⟨171076115358174145248157715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114050743572116096832105143 171076115358174145248157715)
  ·
    refine ⟨256614173037261217872236573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171076115358174145248157715 256614173037261217872236573)
    ·
      refine ⟨96230314888972956702088715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256614173037261217872236573 96230314888972956702088715)
      ·
        refine ⟨144345472333459435053133073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96230314888972956702088715 144345472333459435053133073)
        ·
          refine ⟨108259104250094576289849805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144345472333459435053133073 108259104250094576289849805)
          ·
            refine ⟨40597164093785466108693677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108259104250094576289849805 40597164093785466108693677)
            ·
              refine ⟨15223936535169549790760129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40597164093785466108693677 15223936535169549790760129)
              ·
                refine ⟨11417952401377162343070097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15223936535169549790760129 11417952401377162343070097)
                ·
                  refine ⟨8563464301032871757302573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11417952401377162343070097 8563464301032871757302573)
                  ·
                    refine ⟨3211299112887326908988465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8563464301032871757302573 3211299112887326908988465)
                    ·
                      refine ⟨2408474334665495181741349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211299112887326908988465 2408474334665495181741349)
                      ·
                        rfl

theorem cell23_4690487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_4690487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690487 prefixEnd_4690487 := by exact prefixLift 4690487
  have htrace : WordTrace (prefixWord ++ tailWord_4690487) baseStart_4690487 baseEnd_4690487 := by
    simpa [prefixWord, tailWord_4690487, baseEnd_4690487] using wordTrace_append hprefix tailTrace_4690487
  have hstable : (prefixWord ++ tailWord_4690487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690487).length < 2 ^ (prefixWord ++ tailWord_4690487).sum := by decide
  have hdescent : baseEnd_4690487 < baseStart_4690487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690517 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4690517 : Nat := 118140960795 + 4690517 * 2 ^ 59
def prefixEnd_4690517 : Nat := 4983230072969 + 3 ^ 40 * 4690517 * 2
def baseEnd_4690517 : Nat := 2408489739085130064366211

theorem tailTrace_4690517 : CollatzResearch.WordTrace tailWord_4690517 prefixEnd_4690517 2408489739085130064366211 := by
  unfold tailWord_4690517
  simp only [CollatzResearch.WordTrace]
  refine ⟨171077209548065460371749805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114051473032043640247833203 171077209548065460371749805)
  ·
    refine ⟨64153953580524547639406177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171077209548065460371749805 64153953580524547639406177)
    ·
      refine ⟨48115465185393410729554633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64153953580524547639406177 48115465185393410729554633)
      ·
        refine ⟨36086598889045058047165975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48115465185393410729554633 36086598889045058047165975)
        ·
          refine ⟨54129898333567587070748963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36086598889045058047165975 54129898333567587070748963)
          ·
            refine ⟨81194847500351380606123445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54129898333567587070748963 81194847500351380606123445)
            ·
              refine ⟨7612016953157941931824073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81194847500351380606123445 7612016953157941931824073)
              ·
                refine ⟨5709012714868456448868055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7612016953157941931824073 5709012714868456448868055)
                ·
                  refine ⟨8563519072302684673302083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5709012714868456448868055 8563519072302684673302083)
                  ·
                    refine ⟨12845278608454027009953125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8563519072302684673302083 12845278608454027009953125)
                    ·
                      refine ⟨2408489739085130064366211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12845278608454027009953125 2408489739085130064366211)
                      ·
                        rfl

theorem cell23_4690517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4690517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690517 prefixEnd_4690517 := by exact prefixLift 4690517
  have htrace : WordTrace (prefixWord ++ tailWord_4690517) baseStart_4690517 baseEnd_4690517 := by
    simpa [prefixWord, tailWord_4690517, baseEnd_4690517] using wordTrace_append hprefix tailTrace_4690517
  have hstable : (prefixWord ++ tailWord_4690517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690517).length < 2 ^ (prefixWord ++ tailWord_4690517).sum := by decide
  have hdescent : baseEnd_4690517 < baseStart_4690517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690544 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_4690544 : Nat := 118140960795 + 4690544 * 2 ^ 59
def prefixEnd_4690544 : Nat := 4983230072969 + 3 ^ 40 * 4690544 * 2
def baseEnd_4690544 : Nat := 802834534354267152909529

theorem tailTrace_4690544 : CollatzResearch.WordTrace tailWord_4690544 prefixEnd_4690544 802834534354267152909529 := by
  unfold tailWord_4690544
  simp only [CollatzResearch.WordTrace]
  refine ⟨85539097159483821991491343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114052129545978429321988457 85539097159483821991491343)
  ·
    refine ⟨128308645739225732987237015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85539097159483821991491343 128308645739225732987237015)
    ·
      refine ⟨192462968608838599480855523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128308645739225732987237015 192462968608838599480855523)
      ·
        refine ⟨288694452913257899221283285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192462968608838599480855523 288694452913257899221283285)
        ·
          refine ⟨6766276240154482012998827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 288694452913257899221283285 6766276240154482012998827)
          ·
            refine ⟨10149414360231723019498241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6766276240154482012998827 10149414360231723019498241)
            ·
              refine ⟨7612060770173792264623681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10149414360231723019498241 7612060770173792264623681)
              ·
                refine ⟨5709045577630344198467761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7612060770173792264623681 5709045577630344198467761)
                ·
                  refine ⟨4281784183222758148850821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5709045577630344198467761 4281784183222758148850821)
                  ·
                    refine ⟨802834534354267152909529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4281784183222758148850821 802834534354267152909529)
                    ·
                      rfl

theorem cell23_4690544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_4690544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690544 prefixEnd_4690544 := by exact prefixLift 4690544
  have htrace : WordTrace (prefixWord ++ tailWord_4690544) baseStart_4690544 baseEnd_4690544 := by
    simpa [prefixWord, tailWord_4690544, baseEnd_4690544] using wordTrace_append hprefix tailTrace_4690544
  have hstable : (prefixWord ++ tailWord_4690544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690544).length < 2 ^ (prefixWord ++ tailWord_4690544).sum := by decide
  have hdescent : baseEnd_4690544 < baseStart_4690544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690557 : List Nat := [1, 4, 1, 1, 5, 2, 1, 8]
def baseStart_4690557 : Nat := 118140960795 + 4690557 * 2 ^ 59
def prefixEnd_4690557 : Nat := 4983230072969 + 3 ^ 40 * 4690557 * 2
def baseEnd_4690557 : Nat := 89204084381900366958001

theorem tailTrace_4690557 : CollatzResearch.WordTrace tailWord_4690557 prefixEnd_4690557 89204084381900366958001 := by
  unfold tailWord_4690557
  simp only [CollatzResearch.WordTrace]
  refine ⟨171078668467920547203205925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114052445645280364802137283 171078668467920547203205925)
  ·
    refine ⟨32077250337735102600601111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171078668467920547203205925 32077250337735102600601111)
    ·
      refine ⟨48115875506602653900901667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32077250337735102600601111 48115875506602653900901667)
      ·
        refine ⟨72173813259903980851352501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48115875506602653900901667 72173813259903980851352501)
        ·
          refine ⟨6766294993115998204814297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72173813259903980851352501 6766294993115998204814297)
          ·
            refine ⟨5074721244836998653610723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766294993115998204814297 5074721244836998653610723)
            ·
              refine ⟨7612081867255497980416085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074721244836998653610723 7612081867255497980416085)
              ·
                refine ⟨89204084381900366958001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7612081867255497980416085 89204084381900366958001)
                ·
                  rfl

theorem cell23_4690557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 8].length) (baseStart_4690557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690557 prefixEnd_4690557 := by exact prefixLift 4690557
  have htrace : WordTrace (prefixWord ++ tailWord_4690557) baseStart_4690557 baseEnd_4690557 := by
    simpa [prefixWord, tailWord_4690557, baseEnd_4690557] using wordTrace_append hprefix tailTrace_4690557
  have hstable : (prefixWord ++ tailWord_4690557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690557).length < 2 ^ (prefixWord ++ tailWord_4690557).sum := by decide
  have hdescent : baseEnd_4690557 < baseStart_4690557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690567 : List Nat := [1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_4690567 : Nat := 118140960795 + 4690567 * 2 ^ 59
def prefixEnd_4690567 : Nat := 4983230072969 + 3 ^ 40 * 4690567 * 2
def baseEnd_4690567 : Nat := 2408515413117854868740981

theorem tailTrace_4690567 : CollatzResearch.WordTrace tailWord_4690567 prefixEnd_4690567 2408515413117854868740981 := by
  unfold tailWord_4690567
  simp only [CollatzResearch.WordTrace]
  refine ⟨171079033197884318911069955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114052688798589545940713303 171079033197884318911069955)
  ·
    refine ⟨256618549796826478366604933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171079033197884318911069955 256618549796826478366604933)
    ·
      refine ⟨48115978086904964693738425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256618549796826478366604933 48115978086904964693738425)
      ·
        refine ⟨36086983565178723520303819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48115978086904964693738425 36086983565178723520303819)
        ·
          refine ⟨54130475347768085280455729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36086983565178723520303819 54130475347768085280455729)
          ·
            refine ⟨40597856510826063960341797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54130475347768085280455729 40597856510826063960341797)
            ·
              refine ⟨7612098095779886992564087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40597856510826063960341797 7612098095779886992564087)
              ·
                refine ⟨11418147143669830488846131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612098095779886992564087 11418147143669830488846131)
                ·
                  refine ⟨17127220715504745733269197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418147143669830488846131 17127220715504745733269197)
                  ·
                    refine ⟨6422707768314279649975949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17127220715504745733269197 6422707768314279649975949)
                    ·
                      refine ⟨2408515413117854868740981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422707768314279649975949 2408515413117854868740981)
                      ·
                        rfl

theorem cell23_4690567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_4690567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690567 prefixEnd_4690567 := by exact prefixLift 4690567
  have htrace : WordTrace (prefixWord ++ tailWord_4690567) baseStart_4690567 baseEnd_4690567 := by
    simpa [prefixWord, tailWord_4690567, baseEnd_4690567] using wordTrace_append hprefix tailTrace_4690567
  have hstable : (prefixWord ++ tailWord_4690567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690567).length < 2 ^ (prefixWord ++ tailWord_4690567).sum := by decide
  have hdescent : baseEnd_4690567 < baseStart_4690567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_4690610 : Nat := 118140960795 + 4690610 * 2 ^ 59
def prefixEnd_4690610 : Nat := 4983230072969 + 3 ^ 40 * 4690610 * 2
def baseEnd_4690610 : Nat := 2408537492785998200503283

theorem tailTrace_4690610 : CollatzResearch.WordTrace tailWord_4690610 prefixEnd_4690610 2408537492785998200503283 := by
  unfold tailWord_4690610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42770150384182134313721321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114053734357819024836590189 42770150384182134313721321)
  ·
    refine ⟨32077612788136600735290991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42770150384182134313721321 32077612788136600735290991)
    ·
      refine ⟨48116419182204901102936487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32077612788136600735290991 48116419182204901102936487)
      ·
        refine ⟨72174628773307351654404731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48116419182204901102936487 72174628773307351654404731)
        ·
          refine ⟨108261943159961027481607097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72174628773307351654404731 108261943159961027481607097)
          ·
            refine ⟨81196457369970770611205323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108261943159961027481607097 81196457369970770611205323)
            ·
              refine ⟨121794686054956155916807985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81196457369970770611205323 121794686054956155916807985)
              ·
                refine ⟨91346014541217116937605989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121794686054956155916807985 91346014541217116937605989)
                ·
                  refine ⟨17127377726478209425801123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91346014541217116937605989 17127377726478209425801123)
                  ·
                    refine ⟨25691066589717314138701685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17127377726478209425801123 25691066589717314138701685)
                    ·
                      refine ⟨2408537492785998200503283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25691066589717314138701685 2408537492785998200503283)
                      ·
                        rfl

theorem cell23_4690610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_4690610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690610 prefixEnd_4690610 := by exact prefixLift 4690610
  have htrace : WordTrace (prefixWord ++ tailWord_4690610) baseStart_4690610 baseEnd_4690610 := by
    simpa [prefixWord, tailWord_4690610, baseEnd_4690610] using wordTrace_append hprefix tailTrace_4690610
  have hstable : (prefixWord ++ tailWord_4690610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690610).length < 2 ^ (prefixWord ++ tailWord_4690610).sum := by decide
  have hdescent : baseEnd_4690610 < baseStart_4690610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690624 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2]
def baseStart_4690624 : Nat := 118140960795 + 4690624 * 2 ^ 59
def prefixEnd_4690624 : Nat := 4983230072969 + 3 ^ 40 * 4690624 * 2
def baseEnd_4690624 : Nat := 2408544681515161145728219

theorem tailTrace_4690624 : CollatzResearch.WordTrace tailWord_4690624 prefixEnd_4690624 2408544681515161145728219 := by
  unfold tailWord_4690624
  simp only [CollatzResearch.WordTrace]
  refine ⟨85540556079338908822947463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114054074772451878430596617 85540556079338908822947463)
  ·
    refine ⟨128310834119008363234421195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85540556079338908822947463 128310834119008363234421195)
    ·
      refine ⟨192466251178512544851631793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128310834119008363234421195 192466251178512544851631793)
      ·
        refine ⟨144349688383884408638723845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192466251178512544851631793 144349688383884408638723845)
        ·
          refine ⟨27065566571978326619760721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144349688383884408638723845 27065566571978326619760721)
          ·
            refine ⟨20299174928983744964820541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27065566571978326619760721 20299174928983744964820541)
            ·
              refine ⟨7612190598368904361807703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20299174928983744964820541 7612190598368904361807703)
              ·
                refine ⟨11418285897553356542711555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612190598368904361807703 11418285897553356542711555)
                ·
                  refine ⟨17127428846330034814067333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418285897553356542711555 17127428846330034814067333)
                  ·
                    refine ⟨3211392908686881527637625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17127428846330034814067333 3211392908686881527637625)
                    ·
                      refine ⟨2408544681515161145728219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211392908686881527637625 2408544681515161145728219)
                      ·
                        rfl

theorem cell23_4690624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_4690624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690624 prefixEnd_4690624 := by exact prefixLift 4690624
  have htrace : WordTrace (prefixWord ++ tailWord_4690624) baseStart_4690624 baseEnd_4690624 := by
    simpa [prefixWord, tailWord_4690624, baseEnd_4690624] using wordTrace_append hprefix tailTrace_4690624
  have hstable : (prefixWord ++ tailWord_4690624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690624).length < 2 ^ (prefixWord ++ tailWord_4690624).sum := by decide
  have hdescent : baseEnd_4690624 < baseStart_4690624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690644 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4690644 : Nat := 118140960795 + 4690644 * 2 ^ 59
def prefixEnd_4690644 : Nat := 4983230072969 + 3 ^ 40 * 4690644 * 2
def baseEnd_4690644 : Nat := 2408554951128251067478127

theorem tailTrace_4690644 : CollatzResearch.WordTrace tailWord_4690644 prefixEnd_4690644 2408554951128251067478127 := by
  unfold tailWord_4690644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85540920809302680530811493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114054561079070240707748657 85540920809302680530811493)
  ·
    refine ⟨16038922651744252599527155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85540920809302680530811493 16038922651744252599527155)
    ·
      refine ⟨24058383977616378899290733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16038922651744252599527155 24058383977616378899290733)
      ·
        refine ⟨9021893991606142087234025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24058383977616378899290733 9021893991606142087234025)
        ·
          refine ⟨6766420493704606565425519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9021893991606142087234025 6766420493704606565425519)
          ·
            refine ⟨10149630740556909848138279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6766420493704606565425519 10149630740556909848138279)
            ·
              refine ⟨15224446110835364772207419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10149630740556909848138279 15224446110835364772207419)
              ·
                refine ⟨22836669166253047158311129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15224446110835364772207419 22836669166253047158311129)
                ·
                  refine ⟨17127501874689785368733347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22836669166253047158311129 17127501874689785368733347)
                  ·
                    refine ⟨25691252812034678053100021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17127501874689785368733347 25691252812034678053100021)
                    ·
                      refine ⟨2408554951128251067478127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25691252812034678053100021 2408554951128251067478127)
                      ·
                        rfl

theorem cell23_4690644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4690644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690644 prefixEnd_4690644 := by exact prefixLift 4690644
  have htrace : WordTrace (prefixWord ++ tailWord_4690644) baseStart_4690644 baseEnd_4690644 := by
    simpa [prefixWord, tailWord_4690644, baseEnd_4690644] using wordTrace_append hprefix tailTrace_4690644
  have hstable : (prefixWord ++ tailWord_4690644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690644).length < 2 ^ (prefixWord ++ tailWord_4690644).sum := by decide
  have hdescent : baseEnd_4690644 < baseStart_4690644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690664 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 7]
def baseStart_4690664 : Nat := 118140960795 + 4690664 * 2 ^ 59
def prefixEnd_4690664 : Nat := 4983230072969 + 3 ^ 40 * 4690664 * 2
def baseEnd_4690664 : Nat := 267618357860148998803115

theorem tailTrace_4690664 : CollatzResearch.WordTrace tailWord_4690664 prefixEnd_4690664 267618357860148998803115 := by
  unfold tailWord_4690664
  simp only [CollatzResearch.WordTrace]
  refine ⟨85541285539266452238675523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114055047385688602984900697 85541285539266452238675523)
  ·
    refine ⟨128311928308899678358013285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85541285539266452238675523 128311928308899678358013285)
    ·
      refine ⟨24058486557918689692127491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128311928308899678358013285 24058486557918689692127491)
      ·
        refine ⟨36087729836878034538191237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24058486557918689692127491 36087729836878034538191237)
        ·
          refine ⟨6766449344414631475910857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36087729836878034538191237 6766449344414631475910857)
          ·
            refine ⟨5074837008310973606933143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766449344414631475910857 5074837008310973606933143)
            ·
              refine ⟨7612255512466460410399715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074837008310973606933143 7612255512466460410399715)
              ·
                refine ⟨11418383268699690615599573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612255512466460410399715 11418383268699690615599573)
                ·
                  refine ⟨267618357860148998803115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11418383268699690615599573 267618357860148998803115)
                  ·
                    rfl

theorem cell23_4690664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_4690664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690664 prefixEnd_4690664 := by exact prefixLift 4690664
  have htrace : WordTrace (prefixWord ++ tailWord_4690664) baseStart_4690664 baseEnd_4690664 := by
    simpa [prefixWord, tailWord_4690664, baseEnd_4690664] using wordTrace_append hprefix tailTrace_4690664
  have hstable : (prefixWord ++ tailWord_4690664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690664).length < 2 ^ (prefixWord ++ tailWord_4690664).sum := by decide
  have hdescent : baseEnd_4690664 < baseStart_4690664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690667 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 5, 2]
def baseStart_4690667 : Nat := 118140960795 + 4690667 * 2 ^ 59
def prefixEnd_4690667 : Nat := 4983230072969 + 3 ^ 40 * 4690667 * 2
def baseEnd_4690667 : Nat := 2408566761183304477490521

theorem tailTrace_4690667 : CollatzResearch.WordTrace tailWord_4690667 prefixEnd_4690667 2408566761183304477490521 := by
  unfold tailWord_4690667
  simp only [CollatzResearch.WordTrace]
  refine ⟨171082680497522035989710255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114055120331681357326473503 171082680497522035989710255)
  ·
    refine ⟨256624020746283053984565383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171082680497522035989710255 256624020746283053984565383)
    ·
      refine ⟨384936031119424580976848075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256624020746283053984565383 384936031119424580976848075)
      ·
        refine ⟨577404046679136871465272113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384936031119424580976848075 577404046679136871465272113)
        ·
          refine ⟨433053035009352653598954085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577404046679136871465272113 433053035009352653598954085)
          ·
            refine ⟨81197444064253622549803891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 433053035009352653598954085 81197444064253622549803891)
            ·
              refine ⟨121796166096380433824705837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81197444064253622549803891 121796166096380433824705837)
              ·
                refine ⟨45673562286142662684264689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121796166096380433824705837 45673562286142662684264689)
                ·
                  refine ⟨34255171714606997013198517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45673562286142662684264689 34255171714606997013198517)
                  ·
                    refine ⟨3211422348244405969987361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34255171714606997013198517 3211422348244405969987361)
                    ·
                      refine ⟨2408566761183304477490521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211422348244405969987361 2408566761183304477490521)
                      ·
                        rfl

theorem cell23_4690667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 5, 2].length) (baseStart_4690667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690667 prefixEnd_4690667 := by exact prefixLift 4690667
  have htrace : WordTrace (prefixWord ++ tailWord_4690667) baseStart_4690667 baseEnd_4690667 := by
    simpa [prefixWord, tailWord_4690667, baseEnd_4690667] using wordTrace_append hprefix tailTrace_4690667
  have hstable : (prefixWord ++ tailWord_4690667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690667).length < 2 ^ (prefixWord ++ tailWord_4690667).sum := by decide
  have hdescent : baseEnd_4690667 < baseStart_4690667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690697 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 4]
def baseStart_4690697 : Nat := 118140960795 + 4690697 * 2 ^ 59
def prefixEnd_4690697 : Nat := 4983230072969 + 3 ^ 40 * 4690697 * 2
def baseEnd_4690697 : Nat := 2408582165602939360115383

theorem tailTrace_4690697 : CollatzResearch.WordTrace tailWord_4690697 prefixEnd_4690697 2408582165602939360115383 := by
  unfold tailWord_4690697
  simp only [CollatzResearch.WordTrace]
  refine ⟨171083774687413351113302345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114055849791608900742201563 171083774687413351113302345)
  ·
    refine ⟨128312831015560013334976759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171083774687413351113302345 128312831015560013334976759)
    ·
      refine ⟨192469246523340020002465139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128312831015560013334976759 192469246523340020002465139)
      ·
        refine ⟨288703869785010030003697709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192469246523340020002465139 288703869785010030003697709)
        ·
          refine ⟨108263951169378761251386641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288703869785010030003697709 108263951169378761251386641)
          ·
            refine ⟨81197963377034070938539981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108263951169378761251386641 81197963377034070938539981)
            ·
              refine ⟨30449236266387776601952493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81197963377034070938539981 30449236266387776601952493)
              ·
                refine ⟨11418463599895416225732185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30449236266387776601952493 11418463599895416225732185)
                ·
                  refine ⟨8563847699921562169299139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11418463599895416225732185 8563847699921562169299139)
                  ·
                    refine ⟨12845771549882343253948709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8563847699921562169299139 12845771549882343253948709)
                    ·
                      refine ⟨2408582165602939360115383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12845771549882343253948709 2408582165602939360115383)
                      ·
                        rfl

theorem cell23_4690697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_4690697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690697 prefixEnd_4690697 := by exact prefixLift 4690697
  have htrace : WordTrace (prefixWord ++ tailWord_4690697) baseStart_4690697 baseEnd_4690697 := by
    simpa [prefixWord, tailWord_4690697, baseEnd_4690697] using wordTrace_append hprefix tailTrace_4690697
  have hstable : (prefixWord ++ tailWord_4690697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690697).length < 2 ^ (prefixWord ++ tailWord_4690697).sum := by decide
  have hdescent : baseEnd_4690697 < baseStart_4690697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690714 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2]
def baseStart_4690714 : Nat := 118140960795 + 4690714 * 2 ^ 59
def prefixEnd_4690714 : Nat := 4983230072969 + 3 ^ 40 * 4690714 * 2
def baseEnd_4690714 : Nat := 2408590894774065793602805

theorem tailTrace_4690714 : CollatzResearch.WordTrace tailWord_4690714 prefixEnd_4690714 2408590894774065793602805 := by
  unfold tailWord_4690714
  simp only [CollatzResearch.WordTrace]
  refine ⟨42771098682087940754167799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114056263152234508677780797 42771098682087940754167799)
  ·
    refine ⟨64156648023131911131251699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42771098682087940754167799 64156648023131911131251699)
    ·
      refine ⟨96234972034697866696877549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64156648023131911131251699 96234972034697866696877549)
      ·
        refine ⟨36088114513011700011329081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96234972034697866696877549 36088114513011700011329081)
        ·
          refine ⟨27066085884758775008496811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36088114513011700011329081 27066085884758775008496811)
          ·
            refine ⟨40599128827138162512745217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27066085884758775008496811 40599128827138162512745217)
            ·
              refine ⟨30449346620353621884558913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40599128827138162512745217 30449346620353621884558913)
              ·
                refine ⟨22837009965265216413419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30449346620353621884558913 22837009965265216413419185)
                ·
                  refine ⟨17127757473948912310064389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22837009965265216413419185 17127757473948912310064389)
                  ·
                    refine ⟨3211454526365421058137073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17127757473948912310064389 3211454526365421058137073)
                    ·
                      refine ⟨2408590894774065793602805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211454526365421058137073 2408590894774065793602805)
                      ·
                        rfl

theorem cell23_4690714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_4690714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690714 prefixEnd_4690714 := by exact prefixLift 4690714
  have htrace : WordTrace (prefixWord ++ tailWord_4690714) baseStart_4690714 baseEnd_4690714 := by
    simpa [prefixWord, tailWord_4690714, baseEnd_4690714] using wordTrace_append hprefix tailTrace_4690714
  have hstable : (prefixWord ++ tailWord_4690714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690714).length < 2 ^ (prefixWord ++ tailWord_4690714).sum := by decide
  have hdescent : baseEnd_4690714 < baseStart_4690714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690737 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 6]
def baseStart_4690737 : Nat := 118140960795 + 4690737 * 2 ^ 59
def prefixEnd_4690737 : Nat := 4983230072969 + 3 ^ 40 * 4690737 * 2
def baseEnd_4690737 : Nat := 267622522758791022623911

theorem tailTrace_4690737 : CollatzResearch.WordTrace tailWord_4690737 prefixEnd_4690737 267622522758791022623911 := by
  unfold tailWord_4690737
  simp only [CollatzResearch.WordTrace]
  refine ⟨171085233607268437944758465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114056822404845625296505643 171085233607268437944758465)
  ·
    refine ⟨128313925205451328458568849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171085233607268437944758465 128313925205451328458568849)
    ·
      refine ⟨96235443904088496343926637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128313925205451328458568849 96235443904088496343926637)
      ·
        refine ⟨36088291464033186128972489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96235443904088496343926637 36088291464033186128972489)
        ·
          refine ⟨27066218598024889596729367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36088291464033186128972489 27066218598024889596729367)
          ·
            refine ⟨40599327897037334395094051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27066218598024889596729367 40599327897037334395094051)
            ·
              refine ⟨60898991845556001592641077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40599327897037334395094051 60898991845556001592641077)
              ·
                refine ⟨5709280485520875149310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60898991845556001592641077 5709280485520875149310101)
                ·
                  refine ⟨267622522758791022623911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5709280485520875149310101 267622522758791022623911)
                  ·
                    rfl

theorem cell23_4690737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_4690737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690737 prefixEnd_4690737 := by exact prefixLift 4690737
  have htrace : WordTrace (prefixWord ++ tailWord_4690737) baseStart_4690737 baseEnd_4690737 := by
    simpa [prefixWord, tailWord_4690737, baseEnd_4690737] using wordTrace_append hprefix tailTrace_4690737
  have hstable : (prefixWord ++ tailWord_4690737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690737).length < 2 ^ (prefixWord ++ tailWord_4690737).sum := by decide
  have hdescent : baseEnd_4690737 < baseStart_4690737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690751 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 3]
def baseStart_4690751 : Nat := 118140960795 + 4690751 * 2 ^ 59
def prefixEnd_4690751 : Nat := 4983230072969 + 3 ^ 40 * 4690751 * 2
def baseEnd_4690751 : Nat := 2408609893558282148840135

theorem tailTrace_4690751 : CollatzResearch.WordTrace tailWord_4690751 prefixEnd_4690751 2408609893558282148840135 := by
  unfold tailWord_4690751
  simp only [CollatzResearch.WordTrace]
  refine ⟨171085744229217718335768107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114057162819478478890512071 171085744229217718335768107)
  ·
    refine ⟨256628616343826577503652161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171085744229217718335768107 256628616343826577503652161)
    ·
      refine ⟨192471462257869933127739121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256628616343826577503652161 192471462257869933127739121)
      ·
        refine ⟨144353596693402449845804341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192471462257869933127739121 144353596693402449845804341)
        ·
          refine ⟨13533149690006479673044157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144353596693402449845804341 13533149690006479673044157)
          ·
            refine ⟨5074931133752429877391559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13533149690006479673044157 5074931133752429877391559)
            ·
              refine ⟨7612396700628644816087339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074931133752429877391559 7612396700628644816087339)
              ·
                refine ⟨11418595050942967224131009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612396700628644816087339 11418595050942967224131009)
                ·
                  refine ⟨8563946288207225418098257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11418595050942967224131009 8563946288207225418098257)
                  ·
                    refine ⟨6422959716155419063573693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8563946288207225418098257 6422959716155419063573693)
                    ·
                      refine ⟨2408609893558282148840135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6422959716155419063573693 2408609893558282148840135)
                      ·
                        rfl

theorem cell23_4690751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_4690751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690751 prefixEnd_4690751 := by exact prefixLift 4690751
  have htrace : WordTrace (prefixWord ++ tailWord_4690751) baseStart_4690751 baseEnd_4690751 := by
    simpa [prefixWord, tailWord_4690751, baseEnd_4690751] using wordTrace_append hprefix tailTrace_4690751
  have hstable : (prefixWord ++ tailWord_4690751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690751).length < 2 ^ (prefixWord ++ tailWord_4690751).sum := by decide
  have hdescent : baseEnd_4690751 < baseStart_4690751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690807 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_4690807 : Nat := 118140960795 + 4690807 * 2 ^ 59
def prefixEnd_4690807 : Nat := 4983230072969 + 3 ^ 40 * 4690807 * 2
def baseEnd_4690807 : Nat := 2408638648474933929739877

theorem tailTrace_4690807 : CollatzResearch.WordTrace tailWord_4690807 prefixEnd_4690807 2408638648474933929739877 := by
  unfold tailWord_4690807
  simp only [CollatzResearch.WordTrace]
  refine ⟨171087786717014839899806675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114058524478009893266537783 171087786717014839899806675)
  ·
    refine ⟨256631680075522259849710013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171087786717014839899806675 256631680075522259849710013)
    ·
      refine ⟨96236880028320847443641255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256631680075522259849710013 96236880028320847443641255)
      ·
        refine ⟨144355320042481271165461883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96236880028320847443641255 144355320042481271165461883)
        ·
          refine ⟨216532980063721906748192825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144355320042481271165461883 216532980063721906748192825)
          ·
            refine ⟨162399735047791430061144619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216532980063721906748192825 162399735047791430061144619)
            ·
              refine ⟨243599602571687145091716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162399735047791430061144619 243599602571687145091716929)
              ·
                refine ⟨182699701928765358818787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243599602571687145091716929 182699701928765358818787697)
                ·
                  refine ⟨137024776446574019114090773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182699701928765358818787697 137024776446574019114090773)
                  ·
                    refine ⟨6423036395933157145973005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137024776446574019114090773 6423036395933157145973005)
                    ·
                      refine ⟨2408638648474933929739877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423036395933157145973005 2408638648474933929739877)
                      ·
                        rfl

theorem cell23_4690807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_4690807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690807 prefixEnd_4690807 := by exact prefixLift 4690807
  have htrace : WordTrace (prefixWord ++ tailWord_4690807) baseStart_4690807 baseEnd_4690807 := by
    simpa [prefixWord, tailWord_4690807, baseEnd_4690807] using wordTrace_append hprefix tailTrace_4690807
  have hstable : (prefixWord ++ tailWord_4690807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690807).length < 2 ^ (prefixWord ++ tailWord_4690807).sum := by decide
  have hdescent : baseEnd_4690807 < baseStart_4690807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690824 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4690824 : Nat := 118140960795 + 4690824 * 2 ^ 59
def prefixEnd_4690824 : Nat := 4983230072969 + 3 ^ 40 * 4690824 * 2
def baseEnd_4690824 : Nat := 2408647377646060363227299

theorem tailTrace_4690824 : CollatzResearch.WordTrace tailWord_4690824 prefixEnd_4690824 2408647377646060363227299 := by
  unfold tailWord_4690824
  simp only [CollatzResearch.WordTrace]
  refine ⟨85544203378976625901587763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114058937838635501202117017 85544203378976625901587763)
  ·
    refine ⟨128316305068464938852381645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85544203378976625901587763 128316305068464938852381645)
    ·
      refine ⟨48118614400674352069643117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128316305068464938852381645 48118614400674352069643117)
      ·
        refine ⟨18044480400252882026116169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48118614400674352069643117 18044480400252882026116169)
        ·
          refine ⟨13533360300189661519587127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18044480400252882026116169 13533360300189661519587127)
          ·
            refine ⟨20300040450284492279380691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13533360300189661519587127 20300040450284492279380691)
            ·
              refine ⟨30450060675426738419071037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300040450284492279380691 30450060675426738419071037)
              ·
                refine ⟨11418772753285026907151639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30450060675426738419071037 11418772753285026907151639)
                ·
                  refine ⟨17128159129927540360727459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418772753285026907151639 17128159129927540360727459)
                  ·
                    refine ⟨25692238694891310541091189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17128159129927540360727459 25692238694891310541091189)
                    ·
                      refine ⟨2408647377646060363227299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25692238694891310541091189 2408647377646060363227299)
                      ·
                        rfl

theorem cell23_4690824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4690824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690824 prefixEnd_4690824 := by exact prefixLift 4690824
  have htrace : WordTrace (prefixWord ++ tailWord_4690824) baseStart_4690824 baseEnd_4690824 := by
    simpa [prefixWord, tailWord_4690824, baseEnd_4690824] using wordTrace_append hprefix tailTrace_4690824
  have hstable : (prefixWord ++ tailWord_4690824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690824).length < 2 ^ (prefixWord ++ tailWord_4690824).sum := by decide
  have hdescent : baseEnd_4690824 < baseStart_4690824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690855 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4690855 : Nat := 118140960795 + 4690855 * 2 ^ 59
def prefixEnd_4690855 : Nat := 4983230072969 + 3 ^ 40 * 4690855 * 2
def baseEnd_4690855 : Nat := 2408663295546349741939657

theorem tailTrace_4690855 : CollatzResearch.WordTrace tailWord_4690855 prefixEnd_4690855 2408663295546349741939657 := by
  unfold tailWord_4690855
  simp only [CollatzResearch.WordTrace]
  refine ⟨171089537420840944097554019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114059691613893962731702679 171089537420840944097554019)
  ·
    refine ⟨256634306131261416146331029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171089537420840944097554019 256634306131261416146331029)
    ·
      refine ⟨12029733099902878881859267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256634306131261416146331029 12029733099902878881859267)
      ·
        refine ⟨18044599649854318322788901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12029733099902878881859267 18044599649854318322788901)
        ·
          refine ⟨3383362434347684685522919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18044599649854318322788901 3383362434347684685522919)
          ·
            refine ⟨5075043651521527028284379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383362434347684685522919 5075043651521527028284379)
            ·
              refine ⟨7612565477282290542426569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075043651521527028284379 7612565477282290542426569)
              ·
                refine ⟨5709424107961717906819927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7612565477282290542426569 5709424107961717906819927)
                ·
                  refine ⟨8564136161942576860229891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5709424107961717906819927 8564136161942576860229891)
                  ·
                    refine ⟨12846204242913865290344837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8564136161942576860229891 12846204242913865290344837)
                    ·
                      refine ⟨2408663295546349741939657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12846204242913865290344837 2408663295546349741939657)
                      ·
                        rfl

theorem cell23_4690855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4690855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690855 prefixEnd_4690855 := by exact prefixLift 4690855
  have htrace : WordTrace (prefixWord ++ tailWord_4690855) baseStart_4690855 baseEnd_4690855 := by
    simpa [prefixWord, tailWord_4690855, baseEnd_4690855] using wordTrace_append hprefix tailTrace_4690855
  have hstable : (prefixWord ++ tailWord_4690855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690855).length < 2 ^ (prefixWord ++ tailWord_4690855).sum := by decide
  have hdescent : baseEnd_4690855 < baseStart_4690855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690867 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_4690867 : Nat := 118140960795 + 4690867 * 2 ^ 59
def prefixEnd_4690867 : Nat := 4983230072969 + 3 ^ 40 * 4690867 * 2
def baseEnd_4690867 : Nat := 2408669457314203694989601

theorem tailTrace_4690867 : CollatzResearch.WordTrace tailWord_4690867 prefixEnd_4690867 2408669457314203694989601 := by
  unfold tailWord_4690867
  simp only [CollatzResearch.WordTrace]
  refine ⟨171089975096797470146990855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114059983397864980097993903 171089975096797470146990855)
  ·
    refine ⟨256634962645196205220486283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171089975096797470146990855 256634962645196205220486283)
    ·
      refine ⟨384952443967794307830729425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256634962645196205220486283 384952443967794307830729425)
      ·
        refine ⟨288714332975845730873047069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384952443967794307830729425 288714332975845730873047069)
        ·
          refine ⟨108267874865942149077392651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288714332975845730873047069 108267874865942149077392651)
          ·
            refine ⟨162401812298913223616088977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108267874865942149077392651 162401812298913223616088977)
            ·
              refine ⟨121801359224184917712066733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162401812298913223616088977 121801359224184917712066733)
              ·
                refine ⟨45675509709069344142025025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121801359224184917712066733 45675509709069344142025025)
                ·
                  refine ⟨34256632281802008106518769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45675509709069344142025025 34256632281802008106518769)
                  ·
                    refine ⟨25692474211351506079889077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34256632281802008106518769 25692474211351506079889077)
                    ·
                      refine ⟨2408669457314203694989601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25692474211351506079889077 2408669457314203694989601)
                      ·
                        rfl

theorem cell23_4690867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_4690867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690867 prefixEnd_4690867 := by exact prefixLift 4690867
  have htrace : WordTrace (prefixWord ++ tailWord_4690867) baseStart_4690867 baseEnd_4690867 := by
    simpa [prefixWord, tailWord_4690867, baseEnd_4690867] using wordTrace_append hprefix tailTrace_4690867
  have hstable : (prefixWord ++ tailWord_4690867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690867).length < 2 ^ (prefixWord ++ tailWord_4690867).sum := by decide
  have hdescent : baseEnd_4690867 < baseStart_4690867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690868 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4690868 : Nat := 118140960795 + 4690868 * 2 ^ 59
def prefixEnd_4690868 : Nat := 4983230072969 + 3 ^ 40 * 4690868 * 2
def baseEnd_4690868 : Nat := 2408669970794858191077097

theorem tailTrace_4690868 : CollatzResearch.WordTrace tailWord_4690868 prefixEnd_4690868 2408669970794858191077097 := by
  unfold tailWord_4690868
  simp only [CollatzResearch.WordTrace]
  refine ⟨85545005784896923658888629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114060007713195898211851505 85545005784896923658888629)
  ·
    refine ⟨8019844292334086593020809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85545005784896923658888629 8019844292334086593020809)
    ·
      refine ⟨6014883219250564944765607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019844292334086593020809 6014883219250564944765607)
      ·
        refine ⟨9022324828875847417148411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014883219250564944765607 9022324828875847417148411)
        ·
          refine ⟨13533487243313771125722617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022324828875847417148411 13533487243313771125722617)
          ·
            refine ⟨10150115432485328344291963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13533487243313771125722617 10150115432485328344291963)
            ·
              refine ⟨15225173148727992516437945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10150115432485328344291963 15225173148727992516437945)
              ·
                refine ⟨11418879861545994387328459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15225173148727992516437945 11418879861545994387328459)
                ·
                  refine ⟨17128319792318991580992689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11418879861545994387328459 17128319792318991580992689)
                  ·
                    refine ⟨12846239844239243685744517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17128319792318991580992689 12846239844239243685744517)
                    ·
                      refine ⟨2408669970794858191077097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12846239844239243685744517 2408669970794858191077097)
                      ·
                        rfl

theorem cell23_4690868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4690868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690868 prefixEnd_4690868 := by exact prefixLift 4690868
  have htrace : WordTrace (prefixWord ++ tailWord_4690868) baseStart_4690868 baseEnd_4690868 := by
    simpa [prefixWord, tailWord_4690868, baseEnd_4690868] using wordTrace_append hprefix tailTrace_4690868
  have hstable : (prefixWord ++ tailWord_4690868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690868).length < 2 ^ (prefixWord ++ tailWord_4690868).sum := by decide
  have hdescent : baseEnd_4690868 < baseStart_4690868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690894 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4690894 : Nat := 118140960795 + 4690894 * 2 ^ 59
def prefixEnd_4690894 : Nat := 4983230072969 + 3 ^ 40 * 4690894 * 2
def baseEnd_4690894 : Nat := 2408683321291875089351977

theorem tailTrace_4690894 : CollatzResearch.WordTrace tailWord_4690894 prefixEnd_4690894 2408683321291875089351977 := by
  unfold tailWord_4690894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386369983462456719777967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114060639911799769172149157 21386369983462456719777967)
  ·
    refine ⟨32079554975193685079666951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386369983462456719777967 32079554975193685079666951)
    ·
      refine ⟨48119332462790527619500427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32079554975193685079666951 48119332462790527619500427)
      ·
        refine ⟨72178998694185791429250641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48119332462790527619500427 72178998694185791429250641)
        ·
          refine ⟨54134249020639343571937981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72178998694185791429250641 54134249020639343571937981)
          ·
            refine ⟨20300343382739753839476743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54134249020639343571937981 20300343382739753839476743)
            ·
              refine ⟨30450515074109630759215115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300343382739753839476743 30450515074109630759215115)
              ·
                refine ⟨45675772611164446138822673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30450515074109630759215115 45675772611164446138822673)
                ·
                  refine ⟨34256829458373334604117005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45675772611164446138822673 34256829458373334604117005)
                  ·
                    refine ⟨12846311046890000476543877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34256829458373334604117005 12846311046890000476543877)
                    ·
                      refine ⟨2408683321291875089351977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12846311046890000476543877 2408683321291875089351977)
                      ·
                        rfl

theorem cell23_4690894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4690894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690894 prefixEnd_4690894 := by exact prefixLift 4690894
  have htrace : WordTrace (prefixWord ++ tailWord_4690894) baseStart_4690894 baseEnd_4690894 := by
    simpa [prefixWord, tailWord_4690894, baseEnd_4690894] using wordTrace_append hprefix tailTrace_4690894
  have hstable : (prefixWord ++ tailWord_4690894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690894).length < 2 ^ (prefixWord ++ tailWord_4690894).sum := by decide
  have hdescent : baseEnd_4690894 < baseStart_4690894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690898 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4690898 : Nat := 118140960795 + 4690898 * 2 ^ 59
def prefixEnd_4690898 : Nat := 4983230072969 + 3 ^ 40 * 4690898 * 2
def baseEnd_4690898 : Nat := 2408685375214493073701959

theorem tailTrace_4690898 : CollatzResearch.WordTrace tailWord_4690898 prefixEnd_4690898 2408685375214493073701959 := by
  unfold tailWord_4690898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42772776439921290610342337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114060737173123441627579565 42772776439921290610342337)
  ·
    refine ⟨32079582329940967957756753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42772776439921290610342337 32079582329940967957756753)
    ·
      refine ⟨24059686747455725968317565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32079582329940967957756753 24059686747455725968317565)
      ·
        refine ⟨9022382530295897238119087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24059686747455725968317565 9022382530295897238119087)
        ·
          refine ⟨13533573795443845857178631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022382530295897238119087 13533573795443845857178631)
          ·
            refine ⟨20300360693165768785767947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13533573795443845857178631 20300360693165768785767947)
            ·
              refine ⟨30450541039748653178651921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300360693165768785767947 30450541039748653178651921)
              ·
                refine ⟨22837905779811489883988941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30450541039748653178651921 22837905779811489883988941)
                ·
                  refine ⟨8564214667429308706495853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22837905779811489883988941 8564214667429308706495853)
                  ·
                    refine ⟨3211580500285990764935945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8564214667429308706495853 3211580500285990764935945)
                    ·
                      refine ⟨2408685375214493073701959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211580500285990764935945 2408685375214493073701959)
                      ·
                        rfl

theorem cell23_4690898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4690898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690898 prefixEnd_4690898 := by exact prefixLift 4690898
  have htrace : WordTrace (prefixWord ++ tailWord_4690898) baseStart_4690898 baseEnd_4690898 := by
    simpa [prefixWord, tailWord_4690898, baseEnd_4690898] using wordTrace_append hprefix tailTrace_4690898
  have hstable : (prefixWord ++ tailWord_4690898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690898).length < 2 ^ (prefixWord ++ tailWord_4690898).sum := by decide
  have hdescent : baseEnd_4690898 < baseStart_4690898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690904 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_4690904 : Nat := 118140960795 + 4690904 * 2 ^ 59
def prefixEnd_4690904 : Nat := 4983230072969 + 3 ^ 40 * 4690904 * 2
def baseEnd_4690904 : Nat := 802896152032806683408977

theorem tailTrace_4690904 : CollatzResearch.WordTrace tailWord_4690904 prefixEnd_4690904 802896152032806683408977 := by
  unfold tailWord_4690904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85545662298831712733043883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114060883065108950310725177 85545662298831712733043883)
  ·
    refine ⟨128318493448247569099565825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85545662298831712733043883 128318493448247569099565825)
    ·
      refine ⟨96238870086185676824674369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128318493448247569099565825 96238870086185676824674369)
      ·
        refine ⟨72179152564639257618505777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96238870086185676824674369 72179152564639257618505777)
        ·
          refine ⟨54134364423479443213879333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72179152564639257618505777 54134364423479443213879333)
          ·
            refine ⟨10150193329402395602602375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54134364423479443213879333 10150193329402395602602375)
            ·
              refine ⟨15225289994103593403903563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10150193329402395602602375 15225289994103593403903563)
              ·
                refine ⟨22837934991155390105855345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225289994103593403903563 22837934991155390105855345)
                ·
                  refine ⟨17128451243366542579391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22837934991155390105855345 17128451243366542579391509)
                  ·
                    refine ⟨802896152032806683408977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17128451243366542579391509 802896152032806683408977)
                    ·
                      rfl

theorem cell23_4690904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_4690904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690904 prefixEnd_4690904 := by exact prefixLift 4690904
  have htrace : WordTrace (prefixWord ++ tailWord_4690904) baseStart_4690904 baseEnd_4690904 := by
    simpa [prefixWord, tailWord_4690904, baseEnd_4690904] using wordTrace_append hprefix tailTrace_4690904
  have hstable : (prefixWord ++ tailWord_4690904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690904).length < 2 ^ (prefixWord ++ tailWord_4690904).sum := by decide
  have hdescent : baseEnd_4690904 < baseStart_4690904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690945 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_4690945 : Nat := 118140960795 + 4690945 * 2 ^ 59
def prefixEnd_4690945 : Nat := 4983230072969 + 3 ^ 40 * 4690945 * 2
def baseEnd_4690945 : Nat := 2408709508805254389814243

theorem tailTrace_4690945 : CollatzResearch.WordTrace tailWord_4690945 prefixEnd_4690945 2408709508805254389814243 := by
  unfold tailWord_4690945
  simp only [CollatzResearch.WordTrace]
  refine ⟨171092819990514889468330289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114061879993676592978886859 171092819990514889468330289)
  ·
    refine ⟨128319614992886167101247717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171092819990514889468330289 128319614992886167101247717)
    ·
      refine ⟨24059927811166156331483947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128319614992886167101247717 24059927811166156331483947)
      ·
        refine ⟨36089891716749234497225921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24059927811166156331483947 36089891716749234497225921)
        ·
          refine ⟨27067418787561925872919441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36089891716749234497225921 27067418787561925872919441)
          ·
            refine ⟨20300564090671444404689581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27067418787561925872919441 20300564090671444404689581)
            ·
              refine ⟨7612711534001791651758593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20300564090671444404689581 7612711534001791651758593)
              ·
                refine ⟨5709533650501343738818945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7612711534001791651758593 5709533650501343738818945)
                ·
                  refine ⟨4282150237876007804114209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5709533650501343738818945 4282150237876007804114209)
                  ·
                    refine ⟨3211612678407005853085657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282150237876007804114209 3211612678407005853085657)
                    ·
                      refine ⟨2408709508805254389814243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211612678407005853085657 2408709508805254389814243)
                      ·
                        rfl

theorem cell23_4690945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_4690945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690945 prefixEnd_4690945 := by exact prefixLift 4690945
  have htrace : WordTrace (prefixWord ++ tailWord_4690945) baseStart_4690945 baseEnd_4690945 := by
    simpa [prefixWord, tailWord_4690945, baseEnd_4690945] using wordTrace_append hprefix tailTrace_4690945
  have hstable : (prefixWord ++ tailWord_4690945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690945).length < 2 ^ (prefixWord ++ tailWord_4690945).sum := by decide
  have hdescent : baseEnd_4690945 < baseStart_4690945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690951 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 5]
def baseStart_4690951 : Nat := 118140960795 + 4690951 * 2 ^ 59
def prefixEnd_4690951 : Nat := 4983230072969 + 3 ^ 40 * 4690951 * 2
def baseEnd_4690951 : Nat := 267634732187686818482135

theorem tailTrace_4690951 : CollatzResearch.WordTrace tailWord_4690951 prefixEnd_4690951 267634732187686818482135 := by
  unfold tailWord_4690951
  simp only [CollatzResearch.WordTrace]
  refine ⟨171093038828493152493048707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114062025885662101662032471 171093038828493152493048707)
  ·
    refine ⟨256639558242739728739573061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171093038828493152493048707 256639558242739728739573061)
    ·
      refine ⟨48119917170513699138669949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256639558242739728739573061 48119917170513699138669949)
      ·
        refine ⟨18044968938942637177001231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48119917170513699138669949 18044968938942637177001231)
        ·
          refine ⟨27067453408413955765501847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18044968938942637177001231 27067453408413955765501847)
          ·
            refine ⟨40601180112620933648252771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27067453408413955765501847 40601180112620933648252771)
            ·
              refine ⟨60901770168931400472379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40601180112620933648252771 60901770168931400472379157)
              ·
                refine ⟨2854770476668659397142773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60901770168931400472379157 2854770476668659397142773)
                ·
                  refine ⟨267634732187686818482135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854770476668659397142773 267634732187686818482135)
                  ·
                    rfl

theorem cell23_4690951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 5].length) (baseStart_4690951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690951 prefixEnd_4690951 := by exact prefixLift 4690951
  have htrace : WordTrace (prefixWord ++ tailWord_4690951) baseStart_4690951 baseEnd_4690951 := by
    simpa [prefixWord, tailWord_4690951, baseEnd_4690951] using wordTrace_append hprefix tailTrace_4690951
  have hstable : (prefixWord ++ tailWord_4690951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690951).length < 2 ^ (prefixWord ++ tailWord_4690951).sum := by decide
  have hdescent : baseEnd_4690951 < baseStart_4690951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4690998 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4690998 : Nat := 118140960795 + 4690998 * 2 ^ 59
def prefixEnd_4690998 : Nat := 4983230072969 + 3 ^ 40 * 4690998 * 2
def baseEnd_4690998 : Nat := 802912241093314227483833

theorem tailTrace_4690998 : CollatzResearch.WordTrace tailWord_4690998 prefixEnd_4690998 802912241093314227483833 := by
  unfold tailWord_4690998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693422066207679970000603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114063168706215253013339765 10693422066207679970000603)
  ·
    refine ⟨16040133099311519955000905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10693422066207679970000603 16040133099311519955000905)
    ·
      refine ⟨12030099824483639966250679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16040133099311519955000905 12030099824483639966250679)
      ·
        refine ⟨18045149736725459949376019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12030099824483639966250679 18045149736725459949376019)
        ·
          refine ⟨27067724605088189924064029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18045149736725459949376019 27067724605088189924064029)
          ·
            refine ⟨10150396726908071221524011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27067724605088189924064029 10150396726908071221524011)
            ·
              refine ⟨15225595090362106832286017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10150396726908071221524011 15225595090362106832286017)
              ·
                refine ⟨11419196317771580124214513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15225595090362106832286017 11419196317771580124214513)
                ·
                  refine ⟨8564397238328685093160885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11419196317771580124214513 8564397238328685093160885)
                  ·
                    refine ⟨802912241093314227483833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8564397238328685093160885 802912241093314227483833)
                    ·
                      rfl

theorem cell23_4690998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4690998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4690998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4690998 prefixEnd_4690998 := by exact prefixLift 4690998
  have htrace : WordTrace (prefixWord ++ tailWord_4690998) baseStart_4690998 baseEnd_4690998 := by
    simpa [prefixWord, tailWord_4690998, baseEnd_4690998] using wordTrace_append hprefix tailTrace_4690998
  have hstable : (prefixWord ++ tailWord_4690998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4690998).length < 2 ^ (prefixWord ++ tailWord_4690998).sum := by decide
  have hdescent : baseEnd_4690998 < baseStart_4690998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4690998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691001 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4691001 : Nat := 118140960795 + 4691001 * 2 ^ 59
def prefixEnd_4691001 : Nat := 4983230072969 + 3 ^ 40 * 4691001 * 2
def baseEnd_4691001 : Nat := 2408738263721906170713985

theorem tailTrace_4691001 : CollatzResearch.WordTrace tailWord_4691001 prefixEnd_4691001 2408738263721906170713985 := by
  unfold tailWord_4691001
  simp only [CollatzResearch.WordTrace]
  refine ⟨171094862478312011032368857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114063241652208007354912571 171094862478312011032368857)
  ·
    refine ⟨128321146858734008274276643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171094862478312011032368857 128321146858734008274276643)
    ·
      refine ⟨192481720288101012411414965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128321146858734008274276643 192481720288101012411414965)
      ·
        refine ⟨18045161277009469913570153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192481720288101012411414965 18045161277009469913570153)
        ·
          refine ⟨13533870957757102435177615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18045161277009469913570153 13533870957757102435177615)
          ·
            refine ⟨20300806436635653652766423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13533870957757102435177615 20300806436635653652766423)
            ·
              refine ⟨30451209654953480479149635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20300806436635653652766423 30451209654953480479149635)
              ·
                refine ⟨45676814482430220718724453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30451209654953480479149635 45676814482430220718724453)
                ·
                  refine ⟨8564402715455666384760835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45676814482430220718724453 8564402715455666384760835)
                  ·
                    refine ⟨12846604073183499577141253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8564402715455666384760835 12846604073183499577141253)
                    ·
                      refine ⟨2408738263721906170713985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12846604073183499577141253 2408738263721906170713985)
                      ·
                        rfl

theorem cell23_4691001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4691001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691001 prefixEnd_4691001 := by exact prefixLift 4691001
  have htrace : WordTrace (prefixWord ++ tailWord_4691001) baseStart_4691001 baseEnd_4691001 := by
    simpa [prefixWord, tailWord_4691001, baseEnd_4691001] using wordTrace_append hprefix tailTrace_4691001
  have hstable : (prefixWord ++ tailWord_4691001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691001).length < 2 ^ (prefixWord ++ tailWord_4691001).sum := by decide
  have hdescent : baseEnd_4691001 < baseStart_4691001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691044 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_4691044 : Nat := 118140960795 + 4691044 * 2 ^ 59
def prefixEnd_4691044 : Nat := 4983230072969 + 3 ^ 40 * 4691044 * 2
def baseEnd_4691044 : Nat := 2408760343390049502476287

theorem tailTrace_4691044 : CollatzResearch.WordTrace tailWord_4691044 prefixEnd_4691044 2408760343390049502476287 := by
  unfold tailWord_4691044
  simp only [CollatzResearch.WordTrace]
  refine ⟨85548215408578114688092093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114064287211437486250789457 85548215408578114688092093)
  ·
    refine ⟨32080580778216793008034535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85548215408578114688092093 32080580778216793008034535)
    ·
      refine ⟨48120871167325189512051803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32080580778216793008034535 48120871167325189512051803)
      ·
        refine ⟨72181306750987784268077705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48120871167325189512051803 72181306750987784268077705)
        ·
          refine ⟨54135980063240838201058279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72181306750987784268077705 54135980063240838201058279)
          ·
            refine ⟨81203970094861257301587419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54135980063240838201058279 81203970094861257301587419)
            ·
              refine ⟨121805955142291885952381129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81203970094861257301587419 121805955142291885952381129)
              ·
                refine ⟨91354466356718914464285847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121805955142291885952381129 91354466356718914464285847)
                ·
                  refine ⟨137031699535078371696428771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91354466356718914464285847 137031699535078371696428771)
                  ·
                    refine ⟨205547549302617557544643157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137031699535078371696428771 205547549302617557544643157)
                    ·
                      refine ⟨2408760343390049502476287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205547549302617557544643157 2408760343390049502476287)
                      ·
                        rfl

theorem cell23_4691044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_4691044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691044 prefixEnd_4691044 := by exact prefixLift 4691044
  have htrace : WordTrace (prefixWord ++ tailWord_4691044) baseStart_4691044 baseEnd_4691044 := by
    simpa [prefixWord, tailWord_4691044, baseEnd_4691044] using wordTrace_append hprefix tailTrace_4691044
  have hstable : (prefixWord ++ tailWord_4691044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691044).length < 2 ^ (prefixWord ++ tailWord_4691044).sum := by decide
  have hdescent : baseEnd_4691044 < baseStart_4691044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691068 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_4691068 : Nat := 118140960795 + 4691068 * 2 ^ 59
def prefixEnd_4691068 : Nat := 4983230072969 + 3 ^ 40 * 4691068 * 2
def baseEnd_4691068 : Nat := 2408772666925757408576177

theorem tailTrace_4691068 : CollatzResearch.WordTrace tailWord_4691068 prefixEnd_4691068 2408772666925757408576177 := by
  unfold tailWord_4691068
  simp only [CollatzResearch.WordTrace]
  refine ⟨85548653084534640737528929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114064870779379520983371905 85548653084534640737528929)
  ·
    refine ⟨64161489813400980553146697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85548653084534640737528929 64161489813400980553146697)
    ·
      refine ⟨48121117360050735414860023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64161489813400980553146697 48121117360050735414860023)
      ·
        refine ⟨72181676040076103122290035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48121117360050735414860023 72181676040076103122290035)
        ·
          refine ⟨108272514060114154683435053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72181676040076103122290035 108272514060114154683435053)
          ·
            refine ⟨40602192772542808006288145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108272514060114154683435053 40602192772542808006288145)
            ·
              refine ⟨30451644579407106004716109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40602192772542808006288145 30451644579407106004716109)
              ·
                refine ⟨11419366717277664751768541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30451644579407106004716109 11419366717277664751768541)
                ·
                  refine ⟨4282262518979124281913203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11419366717277664751768541 4282262518979124281913203)
                  ·
                    refine ⟨6423393778468686422869805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282262518979124281913203 6423393778468686422869805)
                    ·
                      refine ⟨2408772666925757408576177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423393778468686422869805 2408772666925757408576177)
                      ·
                        rfl

theorem cell23_4691068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_4691068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691068 prefixEnd_4691068 := by exact prefixLift 4691068
  have htrace : WordTrace (prefixWord ++ tailWord_4691068) baseStart_4691068 baseEnd_4691068 := by
    simpa [prefixWord, tailWord_4691068, baseEnd_4691068] using wordTrace_append hprefix tailTrace_4691068
  have hstable : (prefixWord ++ tailWord_4691068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691068).length < 2 ^ (prefixWord ++ tailWord_4691068).sum := by decide
  have hdescent : baseEnd_4691068 < baseStart_4691068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691091 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4]
def baseStart_4691091 : Nat := 118140960795 + 4691091 * 2 ^ 59
def prefixEnd_4691091 : Nat := 4983230072969 + 3 ^ 40 * 4691091 * 2
def baseEnd_4691091 : Nat := 2408784476980810818588571

theorem tailTrace_4691091 : CollatzResearch.WordTrace tailWord_4691091 prefixEnd_4691091 2408784476980810818588571 := by
  unfold tailWord_4691091
  simp only [CollatzResearch.WordTrace]
  refine ⟨171098145047985956403145127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114065430031990637602096751 171098145047985956403145127)
  ·
    refine ⟨256647217571978934604717691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171098145047985956403145127 256647217571978934604717691)
    ·
      refine ⟨384970826357968401907076537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256647217571978934604717691 384970826357968401907076537)
      ·
        refine ⟨288728119768476301430307403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384970826357968401907076537 288728119768476301430307403)
        ·
          refine ⟨433092179652714452145461105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288728119768476301430307403 433092179652714452145461105)
          ·
            refine ⟨324819134739535839109095829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433092179652714452145461105 324819134739535839109095829)
            ·
              refine ⟨15225896940915742458238867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324819134739535839109095829 15225896940915742458238867)
              ·
                refine ⟨22838845411373613687358301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225896940915742458238867 22838845411373613687358301)
                ·
                  refine ⟨8564567029265105132759363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22838845411373613687358301 8564567029265105132759363)
                  ·
                    refine ⟨12846850543897657699139045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8564567029265105132759363 12846850543897657699139045)
                    ·
                      refine ⟨2408784476980810818588571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12846850543897657699139045 2408784476980810818588571)
                      ·
                        rfl

theorem cell23_4691091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_4691091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691091 prefixEnd_4691091 := by exact prefixLift 4691091
  have htrace : WordTrace (prefixWord ++ tailWord_4691091) baseStart_4691091 baseEnd_4691091 := by
    simpa [prefixWord, tailWord_4691091, baseEnd_4691091] using wordTrace_append hprefix tailTrace_4691091
  have hstable : (prefixWord ++ tailWord_4691091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691091).length < 2 ^ (prefixWord ++ tailWord_4691091).sum := by decide
  have hdescent : baseEnd_4691091 < baseStart_4691091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691095 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_4691095 : Nat := 118140960795 + 4691095 * 2 ^ 59
def prefixEnd_4691095 : Nat := 4983230072969 + 3 ^ 40 * 4691095 * 2
def baseEnd_4691095 : Nat := 2408786530903428802938553

theorem tailTrace_4691095 : CollatzResearch.WordTrace tailWord_4691095 prefixEnd_4691095 2408786530903428802938553 := by
  unfold tailWord_4691095
  simp only [CollatzResearch.WordTrace]
  refine ⟨171098290939971465086290739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114065527293314310057527159 171098290939971465086290739)
  ·
    refine ⟨256647436409957197629436109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171098290939971465086290739 256647436409957197629436109)
    ·
      refine ⟨96242788653733949111038541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256647436409957197629436109 96242788653733949111038541)
      ·
        refine ⟨36091045745150230916639453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96242788653733949111038541 36091045745150230916639453)
        ·
          refine ⟨13534142154431336593739795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36091045745150230916639453 13534142154431336593739795)
          ·
            refine ⟨20301213231647004890609693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13534142154431336593739795 20301213231647004890609693)
            ·
              refine ⟨7612954961867626833978635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20301213231647004890609693 7612954961867626833978635)
              ·
                refine ⟨11419432442801440250967953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612954961867626833978635 11419432442801440250967953)
                ·
                  refine ⟨8564574332101080188225965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11419432442801440250967953 8564574332101080188225965)
                  ·
                    refine ⟨3211715374537905070584737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8564574332101080188225965 3211715374537905070584737)
                    ·
                      refine ⟨2408786530903428802938553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211715374537905070584737 2408786530903428802938553)
                      ·
                        rfl

theorem cell23_4691095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_4691095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691095 prefixEnd_4691095 := by exact prefixLift 4691095
  have htrace : WordTrace (prefixWord ++ tailWord_4691095) baseStart_4691095 baseEnd_4691095 := by
    simpa [prefixWord, tailWord_4691095, baseEnd_4691095] using wordTrace_append hprefix tailTrace_4691095
  have hstable : (prefixWord ++ tailWord_4691095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691095).length < 2 ^ (prefixWord ++ tailWord_4691095).sum := by decide
  have hdescent : baseEnd_4691095 < baseStart_4691095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691101 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4691101 : Nat := 118140960795 + 4691101 * 2 ^ 59
def prefixEnd_4691101 : Nat := 4983230072969 + 3 ^ 40 * 4691101 * 2
def baseEnd_4691101 : Nat := 802929870595785259821175

theorem tailTrace_4691101 : CollatzResearch.WordTrace tailWord_4691101 prefixEnd_4691101 802929870595785259821175 := by
  unfold tailWord_4691101
  simp only [CollatzResearch.WordTrace]
  refine ⟨171098509777949728111009157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114065673185299818740672771 171098509777949728111009157)
  ·
    refine ⟨32080970583365574020814217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171098509777949728111009157 32080970583365574020814217)
    ·
      refine ⟨24060727937524180515610663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32080970583365574020814217 24060727937524180515610663)
      ·
        refine ⟨36091091906286270773415995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24060727937524180515610663 36091091906286270773415995)
        ·
          refine ⟨54136637859429406160123993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36091091906286270773415995 54136637859429406160123993)
          ·
            refine ⟨40602478394572054620092995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54136637859429406160123993 40602478394572054620092995)
            ·
              refine ⟨60903717591858081930139493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40602478394572054620092995 60903717591858081930139493)
              ·
                refine ⟨11419447048473390361901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60903717591858081930139493 11419447048473390361901155)
                ·
                  refine ⟨17129170572710085542851733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11419447048473390361901155 17129170572710085542851733)
                  ·
                    refine ⟨802929870595785259821175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17129170572710085542851733 802929870595785259821175)
                    ·
                      rfl

theorem cell23_4691101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4691101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691101 prefixEnd_4691101 := by exact prefixLift 4691101
  have htrace : WordTrace (prefixWord ++ tailWord_4691101) baseStart_4691101 baseEnd_4691101 := by
    simpa [prefixWord, tailWord_4691101, baseEnd_4691101] using wordTrace_append hprefix tailTrace_4691101
  have hstable : (prefixWord ++ tailWord_4691101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691101).length < 2 ^ (prefixWord ++ tailWord_4691101).sum := by decide
  have hdescent : baseEnd_4691101 < baseStart_4691101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691165 : List Nat := [1, 4, 3, 2, 3, 1, 9]
def baseStart_4691165 : Nat := 118140960795 + 4691165 * 2 ^ 59
def prefixEnd_4691165 : Nat := 4983230072969 + 3 ^ 40 * 4691165 * 2
def baseEnd_4691165 : Nat := 29738549068509179371151

theorem tailTrace_4691165 : CollatzResearch.WordTrace tailWord_4691165 prefixEnd_4691165 29738549068509179371151 := by
  unfold tailWord_4691165
  simp only [CollatzResearch.WordTrace]
  refine ⟨171100844049717867041338949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114067229366478578027559299 171100844049717867041338949)
  ·
    refine ⟨32081408259322100070251053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171100844049717867041338949 32081408259322100070251053)
    ·
      refine ⟨12030528097245787526344145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32081408259322100070251053 12030528097245787526344145)
      ·
        refine ⟨9022896072934340644758109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12030528097245787526344145 9022896072934340644758109)
        ·
          refine ⟨3383586027350377741784291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9022896072934340644758109 3383586027350377741784291)
          ·
            refine ⟨5075379041025566612676437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383586027350377741784291 5075379041025566612676437)
            ·
              refine ⟨29738549068509179371151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5075379041025566612676437 29738549068509179371151)
              ·
                rfl

theorem cell23_4691165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 9].length) (baseStart_4691165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691165 prefixEnd_4691165 := by exact prefixLift 4691165
  have htrace : WordTrace (prefixWord ++ tailWord_4691165) baseStart_4691165 baseEnd_4691165 := by
    simpa [prefixWord, tailWord_4691165, baseEnd_4691165] using wordTrace_append hprefix tailTrace_4691165
  have hstable : (prefixWord ++ tailWord_4691165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691165).length < 2 ^ (prefixWord ++ tailWord_4691165).sum := by decide
  have hdescent : baseEnd_4691165 < baseStart_4691165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691245 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4691245 : Nat := 118140960795 + 4691245 * 2 ^ 59
def prefixEnd_4691245 : Nat := 4983230072969 + 3 ^ 40 * 4691245 * 2
def baseEnd_4691245 : Nat := 2408863553001603216062863

theorem tailTrace_4691245 : CollatzResearch.WordTrace tailWord_4691245 prefixEnd_4691245 2408863553001603216062863 := by
  unfold tailWord_4691245
  simp only [CollatzResearch.WordTrace]
  refine ⟨171103761889428040704251189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114069174592952027136167459 171103761889428040704251189)
  ·
    refine ⟨16040977677133878816023549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171103761889428040704251189 16040977677133878816023549)
    ·
      refine ⟨6015366628925204556008831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16040977677133878816023549 6015366628925204556008831)
      ·
        refine ⟨9023049943387806834013247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015366628925204556008831 9023049943387806834013247)
        ·
          refine ⟨13534574915081710251019871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023049943387806834013247 13534574915081710251019871)
          ·
            refine ⟨20301862372622565376529807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13534574915081710251019871 20301862372622565376529807)
            ·
              refine ⟨30452793558933848064794711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20301862372622565376529807 30452793558933848064794711)
              ·
                refine ⟨45679190338400772097192067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30452793558933848064794711 45679190338400772097192067)
                ·
                  refine ⟨68518785507601158145788101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45679190338400772097192067 68518785507601158145788101)
                  ·
                    refine ⟨12847272282675217152335269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68518785507601158145788101 12847272282675217152335269)
                    ·
                      refine ⟨2408863553001603216062863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847272282675217152335269 2408863553001603216062863)
                      ·
                        rfl

theorem cell23_4691245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4691245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691245 prefixEnd_4691245 := by exact prefixLift 4691245
  have htrace : WordTrace (prefixWord ++ tailWord_4691245) baseStart_4691245 baseEnd_4691245 := by
    simpa [prefixWord, tailWord_4691245, baseEnd_4691245] using wordTrace_append hprefix tailTrace_4691245
  have hstable : (prefixWord ++ tailWord_4691245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691245).length < 2 ^ (prefixWord ++ tailWord_4691245).sum := by decide
  have hdescent : baseEnd_4691245 < baseStart_4691245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691248 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_4691248 : Nat := 118140960795 + 4691248 * 2 ^ 59
def prefixEnd_4691248 : Nat := 4983230072969 + 3 ^ 40 * 4691248 * 2
def baseEnd_4691248 : Nat := 2408865093443566704325349

theorem tailTrace_4691248 : CollatzResearch.WordTrace tailWord_4691248 prefixEnd_4691248 2408865093443566704325349 := by
  unfold tailWord_4691248
  simp only [CollatzResearch.WordTrace]
  refine ⟨85551935654208586108305199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114069247538944781477740265 85551935654208586108305199)
  ·
    refine ⟨128327903481312879162457799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85551935654208586108305199 128327903481312879162457799)
    ·
      refine ⟨192491855221969318743686699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128327903481312879162457799 192491855221969318743686699)
      ·
        refine ⟨288737782832953978115530049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192491855221969318743686699 288737782832953978115530049)
        ·
          refine ⟨216553337124715483586647537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288737782832953978115530049 216553337124715483586647537)
          ·
            refine ⟨162415002843536612689985653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216553337124715483586647537 162415002843536612689985653)
            ·
              refine ⟨15226406516581557439686155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162415002843536612689985653 15226406516581557439686155)
              ·
                refine ⟨22839609774872336159529233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15226406516581557439686155 22839609774872336159529233)
                ·
                  refine ⟨17129707331154252119646925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22839609774872336159529233 17129707331154252119646925)
                  ·
                    refine ⟨6423640249182844544867597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17129707331154252119646925 6423640249182844544867597)
                    ·
                      refine ⟨2408865093443566704325349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423640249182844544867597 2408865093443566704325349)
                      ·
                        rfl

theorem cell23_4691248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_4691248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691248 prefixEnd_4691248 := by exact prefixLift 4691248
  have htrace : WordTrace (prefixWord ++ tailWord_4691248) baseStart_4691248 baseEnd_4691248 := by
    simpa [prefixWord, tailWord_4691248, baseEnd_4691248] using wordTrace_append hprefix tailTrace_4691248
  have hstable : (prefixWord ++ tailWord_4691248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691248).length < 2 ^ (prefixWord ++ tailWord_4691248).sum := by decide
  have hdescent : baseEnd_4691248 < baseStart_4691248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691270 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4691270 : Nat := 118140960795 + 4691270 * 2 ^ 59
def prefixEnd_4691270 : Nat := 4983230072969 + 3 ^ 40 * 4691270 * 2
def baseEnd_4691270 : Nat := 2408876390017965618250249

theorem tailTrace_4691270 : CollatzResearch.WordTrace tailWord_4691270 prefixEnd_4691270 2408876390017965618250249 := by
  unfold tailWord_4691270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347021053573045936684727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114069782476224979982607509 5347021053573045936684727)
  ·
    refine ⟨8020531580359568905027091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5347021053573045936684727 8020531580359568905027091)
    ·
      refine ⟨12030797370539353357540637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8020531580359568905027091 12030797370539353357540637)
      ·
        refine ⟨4511549013952257509077739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12030797370539353357540637 4511549013952257509077739)
        ·
          refine ⟨6767323520928386263616609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511549013952257509077739 6767323520928386263616609)
          ·
            refine ⟨5075492640696289697712457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6767323520928386263616609 5075492640696289697712457)
            ·
              refine ⟨3806619480522217273284343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075492640696289697712457 3806619480522217273284343)
              ·
                refine ⟨5709929220783325909926515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806619480522217273284343 5709929220783325909926515)
                ·
                  refine ⟨8564893831174988864889773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5709929220783325909926515 8564893831174988864889773)
                  ·
                    refine ⟨3211835186690620824333665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8564893831174988864889773 3211835186690620824333665)
                    ·
                      refine ⟨2408876390017965618250249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211835186690620824333665 2408876390017965618250249)
                      ·
                        rfl

theorem cell23_4691270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4691270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691270 prefixEnd_4691270 := by exact prefixLift 4691270
  have htrace : WordTrace (prefixWord ++ tailWord_4691270) baseStart_4691270 baseEnd_4691270 := by
    simpa [prefixWord, tailWord_4691270, baseEnd_4691270] using wordTrace_append hprefix tailTrace_4691270
  have hstable : (prefixWord ++ tailWord_4691270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691270).length < 2 ^ (prefixWord ++ tailWord_4691270).sum := by decide
  have hdescent : baseEnd_4691270 < baseStart_4691270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691288 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4691288 : Nat := 118140960795 + 4691288 * 2 ^ 59
def prefixEnd_4691288 : Nat := 4983230072969 + 3 ^ 40 * 4691288 * 2
def baseEnd_4691288 : Nat := 2408885632669746547825165

theorem tailTrace_4691288 : CollatzResearch.WordTrace tailWord_4691288 prefixEnd_4691288 2408885632669746547825165 := by
  unfold tailWord_4691288
  simp only [CollatzResearch.WordTrace]
  refine ⟨85552665114136129524033259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114070220152181506032044345 85552665114136129524033259)
  ·
    refine ⟨128328997671204194286049889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85552665114136129524033259 128328997671204194286049889)
    ·
      refine ⟨96246748253403145714537417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128328997671204194286049889 96246748253403145714537417)
      ·
        refine ⟨72185061190052359285903063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96246748253403145714537417 72185061190052359285903063)
        ·
          refine ⟨108277591785078538928854595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72185061190052359285903063 108277591785078538928854595)
          ·
            refine ⟨162416387677617808393281893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108277591785078538928854595 162416387677617808393281893)
            ·
              refine ⟨30453072689553339073740355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162416387677617808393281893 30453072689553339073740355)
              ·
                refine ⟨45679609034330008610610533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30453072689553339073740355 45679609034330008610610533)
                ·
                  refine ⟨8564926693936876614489475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45679609034330008610610533 8564926693936876614489475)
                  ·
                    refine ⟨12847390040905314921734213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8564926693936876614489475 12847390040905314921734213)
                    ·
                      refine ⟨2408885632669746547825165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847390040905314921734213 2408885632669746547825165)
                      ·
                        rfl

theorem cell23_4691288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4691288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691288 prefixEnd_4691288 := by exact prefixLift 4691288
  have htrace : WordTrace (prefixWord ++ tailWord_4691288) baseStart_4691288 baseEnd_4691288 := by
    simpa [prefixWord, tailWord_4691288, baseEnd_4691288] using wordTrace_append hprefix tailTrace_4691288
  have hstable : (prefixWord ++ tailWord_4691288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691288).length < 2 ^ (prefixWord ++ tailWord_4691288).sum := by decide
  have hdescent : baseEnd_4691288 < baseStart_4691288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691325 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_4691325 : Nat := 118140960795 + 4691325 * 2 ^ 59
def prefixEnd_4691325 : Nat := 4983230072969 + 3 ^ 40 * 4691325 * 2
def baseEnd_4691325 : Nat := 2408904631453962903062495

theorem tailTrace_4691325 : CollatzResearch.WordTrace tailWord_4691325 prefixEnd_4691325 2408904631453962903062495 := by
  unfold tailWord_4691325
  simp only [CollatzResearch.WordTrace]
  refine ⟨171106679729138214367163429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114071119819425476244775619 171106679729138214367163429)
  ·
    refine ⟨32082502449213415193843143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171106679729138214367163429 32082502449213415193843143)
    ·
      refine ⟨48123753673820122790764715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32082502449213415193843143 48123753673820122790764715)
      ·
        refine ⟨72185630510730184186147073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48123753673820122790764715 72185630510730184186147073)
        ·
          refine ⟨54139222883047638139610305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72185630510730184186147073 54139222883047638139610305)
          ·
            refine ⟨40604417162285728604707729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54139222883047638139610305 40604417162285728604707729)
            ·
              refine ⟨30453312871714296453530797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40604417162285728604707729 30453312871714296453530797)
              ·
                refine ⟨11419992326892861170074049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30453312871714296453530797 11419992326892861170074049)
                ·
                  refine ⟨8564994245169645877555537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11419992326892861170074049 8564994245169645877555537)
                  ·
                    refine ⟨6423745683877234408166653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8564994245169645877555537 6423745683877234408166653)
                    ·
                      refine ⟨2408904631453962903062495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423745683877234408166653 2408904631453962903062495)
                      ·
                        rfl

theorem cell23_4691325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_4691325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691325 prefixEnd_4691325 := by exact prefixLift 4691325
  have htrace : WordTrace (prefixWord ++ tailWord_4691325) baseStart_4691325 baseEnd_4691325 := by
    simpa [prefixWord, tailWord_4691325, baseEnd_4691325] using wordTrace_append hprefix tailTrace_4691325
  have hstable : (prefixWord ++ tailWord_4691325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691325).length < 2 ^ (prefixWord ++ tailWord_4691325).sum := by decide
  have hdescent : baseEnd_4691325 < baseStart_4691325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691362 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4691362 : Nat := 118140960795 + 4691362 * 2 ^ 59
def prefixEnd_4691362 : Nat := 4983230072969 + 3 ^ 40 * 4691362 * 2
def baseEnd_4691362 : Nat := 267658181137575473144425

theorem tailTrace_4691362 : CollatzResearch.WordTrace tailWord_4691362 prefixEnd_4691362 267658181137575473144425 := by
  unfold tailWord_4691362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42777007307501042421565085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114072019486669446457506893 42777007307501042421565085)
  ·
    refine ⟨16041377740312890908086907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42777007307501042421565085 16041377740312890908086907)
    ·
      refine ⟨24062066610469336362130361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16041377740312890908086907 24062066610469336362130361)
      ·
        refine ⟨18046549957852002271597771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24062066610469336362130361 18046549957852002271597771)
        ·
          refine ⟨27069824936778003407396657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18046549957852002271597771 27069824936778003407396657)
          ·
            refine ⟨20302368702583502555547493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27069824936778003407396657 20302368702583502555547493)
            ·
              refine ⟨3806694131734406729165155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20302368702583502555547493 3806694131734406729165155)
              ·
                refine ⟨5710041197601610093747733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806694131734406729165155 5710041197601610093747733)
                ·
                  refine ⟨267658181137575473144425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5710041197601610093747733 267658181137575473144425)
                  ·
                    rfl

theorem cell23_4691362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4691362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691362 prefixEnd_4691362 := by exact prefixLift 4691362
  have htrace : WordTrace (prefixWord ++ tailWord_4691362) baseStart_4691362 baseEnd_4691362 := by
    simpa [prefixWord, tailWord_4691362, baseEnd_4691362] using wordTrace_append hprefix tailTrace_4691362
  have hstable : (prefixWord ++ tailWord_4691362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691362).length < 2 ^ (prefixWord ++ tailWord_4691362).sum := by decide
  have hdescent : baseEnd_4691362 < baseStart_4691362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691365 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_4691365 : Nat := 118140960795 + 4691365 * 2 ^ 59
def prefixEnd_4691365 : Nat := 4983230072969 + 3 ^ 40 * 4691365 * 2
def baseEnd_4691365 : Nat := 2408925170680142746562311

theorem tailTrace_4691365 : CollatzResearch.WordTrace tailWord_4691365 prefixEnd_4691365 2408925170680142746562311 := by
  unfold tailWord_4691365
  simp only [CollatzResearch.WordTrace]
  refine ⟨171108138648993301198619549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114072092432662200799079699 171108138648993301198619549)
  ·
    refine ⟨64165551993372487949482331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171108138648993301198619549 64165551993372487949482331)
    ·
      refine ⟨96248327990058731924223497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64165551993372487949482331 96248327990058731924223497)
      ·
        refine ⟨72186245992544048943167623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96248327990058731924223497 72186245992544048943167623)
        ·
          refine ⟨108279368988816073414751435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72186245992544048943167623 108279368988816073414751435)
          ·
            refine ⟨162419053483224110122127153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108279368988816073414751435 162419053483224110122127153)
            ·
              refine ⟨121814290112418082591595365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162419053483224110122127153 121814290112418082591595365)
              ·
                refine ⟨22840179396078390485924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121814290112418082591595365 22840179396078390485924131)
                ·
                  refine ⟨34260269094117585728886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22840179396078390485924131 34260269094117585728886197)
                  ·
                    refine ⟨3211900227573523662083081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34260269094117585728886197 3211900227573523662083081)
                    ·
                      refine ⟨2408925170680142746562311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211900227573523662083081 2408925170680142746562311)
                      ·
                        rfl

theorem cell23_4691365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_4691365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691365 prefixEnd_4691365 := by exact prefixLift 4691365
  have htrace : WordTrace (prefixWord ++ tailWord_4691365) baseStart_4691365 baseEnd_4691365 := by
    simpa [prefixWord, tailWord_4691365, baseEnd_4691365] using wordTrace_append hprefix tailTrace_4691365
  have hstable : (prefixWord ++ tailWord_4691365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691365).length < 2 ^ (prefixWord ++ tailWord_4691365).sum := by decide
  have hdescent : baseEnd_4691365 < baseStart_4691365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691389 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4691389 : Nat := 118140960795 + 4691389 * 2 ^ 59
def prefixEnd_4691389 : Nat := 4983230072969 + 3 ^ 40 * 4691389 * 2
def baseEnd_4691389 : Nat := 2408937494215850652662201

theorem tailTrace_4691389 : CollatzResearch.WordTrace tailWord_4691389 prefixEnd_4691389 2408937494215850652662201 := by
  unfold tailWord_4691389
  simp only [CollatzResearch.WordTrace]
  refine ⟨171109014000906353297493221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114072676000604235531662147 171109014000906353297493221)
  ·
    refine ⟨32082940125169941243279979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171109014000906353297493221 32082940125169941243279979)
    ·
      refine ⟨48124410187754911864919969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32082940125169941243279979 48124410187754911864919969)
      ·
        refine ⟨36093307640816183898689977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48124410187754911864919969 36093307640816183898689977)
        ·
          refine ⟨27069980730612137924017483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36093307640816183898689977 27069980730612137924017483)
          ·
            refine ⟨40604971095918206886026225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27069980730612137924017483 40604971095918206886026225)
            ·
              refine ⟨30453728321938655164519669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40604971095918206886026225 30453728321938655164519669)
              ·
                refine ⟨2855037030181748921673719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30453728321938655164519669 2855037030181748921673719)
                ·
                  refine ⟨4282555545272623382510579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855037030181748921673719 4282555545272623382510579)
                  ·
                    refine ⟨6423833317908935073765869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282555545272623382510579 6423833317908935073765869)
                    ·
                      refine ⟨2408937494215850652662201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423833317908935073765869 2408937494215850652662201)
                      ·
                        rfl

theorem cell23_4691389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4691389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691389 prefixEnd_4691389 := by exact prefixLift 4691389
  have htrace : WordTrace (prefixWord ++ tailWord_4691389) baseStart_4691389 baseEnd_4691389 := by
    simpa [prefixWord, tailWord_4691389, baseEnd_4691389] using wordTrace_append hprefix tailTrace_4691389
  have hstable : (prefixWord ++ tailWord_4691389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691389).length < 2 ^ (prefixWord ++ tailWord_4691389).sum := by decide
  have hdescent : baseEnd_4691389 < baseStart_4691389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691395 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 4]
def baseStart_4691395 : Nat := 118140960795 + 4691395 * 2 ^ 59
def prefixEnd_4691395 : Nat := 4983230072969 + 3 ^ 40 * 4691395 * 2
def baseEnd_4691395 : Nat := 2408940575099777629187173

theorem tailTrace_4691395 : CollatzResearch.WordTrace tailWord_4691395 prefixEnd_4691395 2408940575099777629187173 := by
  unfold tailWord_4691395
  simp only [CollatzResearch.WordTrace]
  refine ⟨171109232838884616322211639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114072821892589744214807759 171109232838884616322211639)
  ·
    refine ⟨256663849258326924483317459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171109232838884616322211639 256663849258326924483317459)
    ·
      refine ⟨384995773887490386724976189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256663849258326924483317459 384995773887490386724976189)
      ·
        refine ⟨144373415207808895021866071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 384995773887490386724976189 144373415207808895021866071)
        ·
          refine ⟨216560122811713342532799107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144373415207808895021866071 216560122811713342532799107)
          ·
            refine ⟨324840184217570013799198661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216560122811713342532799107 324840184217570013799198661)
            ·
              refine ⟨60907534540794377587349749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324840184217570013799198661 60907534540794377587349749)
              ·
                refine ⟨5710081363199472898814039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60907534540794377587349749 5710081363199472898814039)
                ·
                  refine ⟨8565122044799209348221059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710081363199472898814039 8565122044799209348221059)
                  ·
                    refine ⟨12847683067198814022331589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8565122044799209348221059 12847683067198814022331589)
                    ·
                      refine ⟨2408940575099777629187173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847683067198814022331589 2408940575099777629187173)
                      ·
                        rfl

theorem cell23_4691395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_4691395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691395 prefixEnd_4691395 := by exact prefixLift 4691395
  have htrace : WordTrace (prefixWord ++ tailWord_4691395) baseStart_4691395 baseEnd_4691395 := by
    simpa [prefixWord, tailWord_4691395, baseEnd_4691395] using wordTrace_append hprefix tailTrace_4691395
  have hstable : (prefixWord ++ tailWord_4691395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691395).length < 2 ^ (prefixWord ++ tailWord_4691395).sum := by decide
  have hdescent : baseEnd_4691395 < baseStart_4691395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691406 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4691406 : Nat := 118140960795 + 4691406 * 2 ^ 59
def prefixEnd_4691406 : Nat := 4983230072969 + 3 ^ 40 * 4691406 * 2
def baseEnd_4691406 : Nat := 2408946223386977086149623

theorem tailTrace_4691406 : CollatzResearch.WordTrace tailWord_4691406 prefixEnd_4691406 2408946223386977086149623 := by
  unfold tailWord_4691406
  simp only [CollatzResearch.WordTrace]
  refine ⟨21388704255230595650107759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114073089361229843467241381 21388704255230595650107759)
  ·
    refine ⟨32083056382845893475161639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21388704255230595650107759 32083056382845893475161639)
    ·
      refine ⟨48124584574268840212742459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32083056382845893475161639 48124584574268840212742459)
      ·
        refine ⟨72186876861403260319113689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48124584574268840212742459 72186876861403260319113689)
        ·
          refine ⟨54140157646052445239335267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72186876861403260319113689 54140157646052445239335267)
          ·
            refine ⟨81210236469078667859002901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54140157646052445239335267 81210236469078667859002901)
            ·
              refine ⟨3806729834488062555890761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81210236469078667859002901 3806729834488062555890761)
              ·
                refine ⟨2855047375866046916918071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3806729834488062555890761 2855047375866046916918071)
                ·
                  refine ⟨4282571063799070375377107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855047375866046916918071 4282571063799070375377107)
                  ·
                    refine ⟨6423856595698605563065661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282571063799070375377107 6423856595698605563065661)
                    ·
                      refine ⟨2408946223386977086149623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423856595698605563065661 2408946223386977086149623)
                      ·
                        rfl

theorem cell23_4691406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4691406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691406 prefixEnd_4691406 := by exact prefixLift 4691406
  have htrace : WordTrace (prefixWord ++ tailWord_4691406) baseStart_4691406 baseEnd_4691406 := by
    simpa [prefixWord, tailWord_4691406, baseEnd_4691406] using wordTrace_append hprefix tailTrace_4691406
  have hstable : (prefixWord ++ tailWord_4691406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691406).length < 2 ^ (prefixWord ++ tailWord_4691406).sum := by decide
  have hdescent : baseEnd_4691406 < baseStart_4691406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691425 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_4691425 : Nat := 118140960795 + 4691425 * 2 ^ 59
def prefixEnd_4691425 : Nat := 4983230072969 + 3 ^ 40 * 4691425 * 2
def baseEnd_4691425 : Nat := 2408955979519412511812035

theorem tailTrace_4691425 : CollatzResearch.WordTrace tailWord_4691425 prefixEnd_4691425 2408955979519412511812035 := by
  unfold tailWord_4691425
  simp only [CollatzResearch.WordTrace]
  refine ⟨171110327028775931445803729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114073551352517287630535819 171110327028775931445803729)
  ·
    refine ⟨128332745271581948584352797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171110327028775931445803729 128332745271581948584352797)
    ·
      refine ⟨48124779476843230719132299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128332745271581948584352797 48124779476843230719132299)
      ·
        refine ⟨72187169215264846078698449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48124779476843230719132299 72187169215264846078698449)
        ·
          refine ⟨54140376911448634559023837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72187169215264846078698449 54140376911448634559023837)
          ·
            refine ⟨20302641341793237959633939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54140376911448634559023837 20302641341793237959633939)
            ·
              refine ⟨30453962012689856939450909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302641341793237959633939 30453962012689856939450909)
              ·
                refine ⟨11420235754758696352294091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30453962012689856939450909 11420235754758696352294091)
                ·
                  refine ⟨17130353632138044528441137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11420235754758696352294091 17130353632138044528441137)
                  ·
                    refine ⟨12847765224103533396330853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17130353632138044528441137 12847765224103533396330853)
                    ·
                      refine ⟨2408955979519412511812035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847765224103533396330853 2408955979519412511812035)
                      ·
                        rfl

theorem cell23_4691425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_4691425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691425 prefixEnd_4691425 := by exact prefixLift 4691425
  have htrace : WordTrace (prefixWord ++ tailWord_4691425) baseStart_4691425 baseEnd_4691425 := by
    simpa [prefixWord, tailWord_4691425, baseEnd_4691425] using wordTrace_append hprefix tailTrace_4691425
  have hstable : (prefixWord ++ tailWord_4691425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691425).length < 2 ^ (prefixWord ++ tailWord_4691425).sum := by decide
  have hdescent : baseEnd_4691425 < baseStart_4691425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4691428 : Nat := 118140960795 + 4691428 * 2 ^ 59
def prefixEnd_4691428 : Nat := 4983230072969 + 3 ^ 40 * 4691428 * 2
def baseEnd_4691428 : Nat := 2408957519961376000074521

theorem tailTrace_4691428 : CollatzResearch.WordTrace tailWord_4691428 prefixEnd_4691428 2408957519961376000074521 := by
  unfold tailWord_4691428
  simp only [CollatzResearch.WordTrace]
  refine ⟨85555218223882531479081469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114073624298510041972108625 85555218223882531479081469)
  ·
    refine ⟨32083206833955949304655551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85555218223882531479081469 32083206833955949304655551)
    ·
      refine ⟨48124810250933923956983327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32083206833955949304655551 48124810250933923956983327)
      ·
        refine ⟨72187215376400885935474991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48124810250933923956983327 72187215376400885935474991)
        ·
          refine ⟨108280823064601328903212487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72187215376400885935474991 108280823064601328903212487)
          ·
            refine ⟨162421234596901993354818731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108280823064601328903212487 162421234596901993354818731)
            ·
              refine ⟨243631851895352990032228097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162421234596901993354818731 243631851895352990032228097)
              ·
                refine ⟨182723888921514742524171073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243631851895352990032228097 182723888921514742524171073)
                ·
                  refine ⟨137042916691136056893128305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182723888921514742524171073 137042916691136056893128305)
                  ·
                    refine ⟨102782187518352042669846229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137042916691136056893128305 102782187518352042669846229)
                    ·
                      refine ⟨2408957519961376000074521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102782187518352042669846229 2408957519961376000074521)
                      ·
                        rfl

theorem cell23_4691428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4691428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691428 prefixEnd_4691428 := by exact prefixLift 4691428
  have htrace : WordTrace (prefixWord ++ tailWord_4691428) baseStart_4691428 baseEnd_4691428 := by
    simpa [prefixWord, tailWord_4691428, baseEnd_4691428] using wordTrace_append hprefix tailTrace_4691428
  have hstable : (prefixWord ++ tailWord_4691428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691428).length < 2 ^ (prefixWord ++ tailWord_4691428).sum := by decide
  have hdescent : baseEnd_4691428 < baseStart_4691428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691429 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4691429 : Nat := 118140960795 + 4691429 * 2 ^ 59
def prefixEnd_4691429 : Nat := 4983230072969 + 3 ^ 40 * 4691429 * 2
def baseEnd_4691429 : Nat := 2408958033442030496162017

theorem tailTrace_4691429 : CollatzResearch.WordTrace tailWord_4691429 prefixEnd_4691429 2408958033442030496162017 := by
  unfold tailWord_4691429
  simp only [CollatzResearch.WordTrace]
  refine ⟨171110472920761440128949341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114073648613840960085966227 171110472920761440128949341)
  ·
    refine ⟨64166427345285540048356003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171110472920761440128949341 64166427345285540048356003)
    ·
      refine ⟨96249641017928310072534005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64166427345285540048356003 96249641017928310072534005)
      ·
        refine ⟨9023403845430779069300063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96249641017928310072534005 9023403845430779069300063)
        ·
          refine ⟨13535105768146168603950095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023403845430779069300063 13535105768146168603950095)
          ·
            refine ⟨20302658652219252905925143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13535105768146168603950095 20302658652219252905925143)
            ·
              refine ⟨30453987978328879358887715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302658652219252905925143 30453987978328879358887715)
              ·
                refine ⟨45680981967493319038331573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30453987978328879358887715 45680981967493319038331573)
                ·
                  refine ⟨4282592059452498659843585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45680981967493319038331573 4282592059452498659843585)
                  ·
                    refine ⟨3211944044589373994882689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282592059452498659843585 3211944044589373994882689)
                    ·
                      refine ⟨2408958033442030496162017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211944044589373994882689 2408958033442030496162017)
                      ·
                        rfl

theorem cell23_4691429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4691429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691429 prefixEnd_4691429 := by exact prefixLift 4691429
  have htrace : WordTrace (prefixWord ++ tailWord_4691429) baseStart_4691429 baseEnd_4691429 := by
    simpa [prefixWord, tailWord_4691429, baseEnd_4691429] using wordTrace_append hprefix tailTrace_4691429
  have hstable : (prefixWord ++ tailWord_4691429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691429).length < 2 ^ (prefixWord ++ tailWord_4691429).sum := by decide
  have hdescent : baseEnd_4691429 < baseStart_4691429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691432 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4691432 : Nat := 118140960795 + 4691432 * 2 ^ 59
def prefixEnd_4691432 : Nat := 4983230072969 + 3 ^ 40 * 4691432 * 2
def baseEnd_4691432 : Nat := 2408959573883993984424503

theorem tailTrace_4691432 : CollatzResearch.WordTrace tailWord_4691432 prefixEnd_4691432 2408959573883993984424503 := by
  unfold tailWord_4691432
  simp only [CollatzResearch.WordTrace]
  refine ⟨85555291169875285820654275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114073721559833714427539033 85555291169875285820654275)
  ·
    refine ⟨128332936754812928730981413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85555291169875285820654275 128332936754812928730981413)
    ·
      refine ⟨24062425641527424137059015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128332936754812928730981413 24062425641527424137059015)
      ·
        refine ⟨36093638462291136205588523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24062425641527424137059015 36093638462291136205588523)
        ·
          refine ⟨54140457693436704308382785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36093638462291136205588523 54140457693436704308382785)
          ·
            refine ⟨40605343270077528231287089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54140457693436704308382785 40605343270077528231287089)
            ·
              refine ⟨30454007452558146173465317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40605343270077528231287089 30454007452558146173465317)
              ·
                refine ⟨5710126397354652407524747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30454007452558146173465317 5710126397354652407524747)
                ·
                  refine ⟨8565189596031978611287121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710126397354652407524747 8565189596031978611287121)
                  ·
                    refine ⟨6423892197023983958465341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8565189596031978611287121 6423892197023983958465341)
                    ·
                      refine ⟨2408959573883993984424503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423892197023983958465341 2408959573883993984424503)
                      ·
                        rfl

theorem cell23_4691432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4691432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691432 prefixEnd_4691432 := by exact prefixLift 4691432
  have htrace : WordTrace (prefixWord ++ tailWord_4691432) baseStart_4691432 baseEnd_4691432 := by
    simpa [prefixWord, tailWord_4691432, baseEnd_4691432] using wordTrace_append hprefix tailTrace_4691432
  have hstable : (prefixWord ++ tailWord_4691432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691432).length < 2 ^ (prefixWord ++ tailWord_4691432).sum := by decide
  have hdescent : baseEnd_4691432 < baseStart_4691432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691442 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4691442 : Nat := 118140960795 + 4691442 * 2 ^ 59
def prefixEnd_4691442 : Nat := 4983230072969 + 3 ^ 40 * 4691442 * 2
def baseEnd_4691442 : Nat := 2408964708690538945299457

theorem tailTrace_4691442 : CollatzResearch.WordTrace tailWord_4691442 prefixEnd_4691442 2408964708690538945299457 := by
  unfold tailWord_4691442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42777736767428585837293145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114073964713142895566115053 42777736767428585837293145)
  ·
    refine ⟨32083302575571439377969859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42777736767428585837293145 32083302575571439377969859)
    ·
      refine ⟨48124953863357159066954789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32083302575571439377969859 48124953863357159066954789)
      ·
        refine ⟨9023428849379467325054023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48124953863357159066954789 9023428849379467325054023)
        ·
          refine ⟨13535143274069200987581035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023428849379467325054023 13535143274069200987581035)
          ·
            refine ⟨20302714911103801481371553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13535143274069200987581035 20302714911103801481371553)
            ·
              refine ⟨15227036183327851111028665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20302714911103801481371553 15227036183327851111028665)
              ·
                refine ⟨11420277137495888333271499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15227036183327851111028665 11420277137495888333271499)
                ·
                  refine ⟨17130415706243832499907249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11420277137495888333271499 17130415706243832499907249)
                  ·
                    refine ⟨12847811779682874374930437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17130415706243832499907249 12847811779682874374930437)
                    ·
                      refine ⟨2408964708690538945299457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847811779682874374930437 2408964708690538945299457)
                      ·
                        rfl

theorem cell23_4691442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4691442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691442 prefixEnd_4691442 := by exact prefixLift 4691442
  have htrace : WordTrace (prefixWord ++ tailWord_4691442) baseStart_4691442 baseEnd_4691442 := by
    simpa [prefixWord, tailWord_4691442, baseEnd_4691442] using wordTrace_append hprefix tailTrace_4691442
  have hstable : (prefixWord ++ tailWord_4691442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691442).length < 2 ^ (prefixWord ++ tailWord_4691442).sum := by decide
  have hdescent : baseEnd_4691442 < baseStart_4691442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691446 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4691446 : Nat := 118140960795 + 4691446 * 2 ^ 59
def prefixEnd_4691446 : Nat := 4983230072969 + 3 ^ 40 * 4691446 * 2
def baseEnd_4691446 : Nat := 2408966762613156929649439

theorem tailTrace_4691446 : CollatzResearch.WordTrace tailWord_4691446 prefixEnd_4691446 2408966762613156929649439 := by
  unfold tailWord_4691446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694443310106240752019887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114074061974466568021545461 10694443310106240752019887)
  ·
    refine ⟨16041664965159361128029831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10694443310106240752019887 16041664965159361128029831)
    ·
      refine ⟨24062497447739041692044747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16041664965159361128029831 24062497447739041692044747)
      ·
        refine ⟨36093746171608562538067121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24062497447739041692044747 36093746171608562538067121)
        ·
          refine ⟨27070309628706421903550341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36093746171608562538067121 27070309628706421903550341)
          ·
            refine ⟨5075683055382454106915689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27070309628706421903550341 5075683055382454106915689)
            ·
              refine ⟨3806762291536840580186767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075683055382454106915689 3806762291536840580186767)
              ·
                refine ⟨5710143437305260870280151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806762291536840580186767 5710143437305260870280151)
                ·
                  refine ⟨8565215155957891305420227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710143437305260870280151 8565215155957891305420227)
                  ·
                    refine ⟨12847822733936836958130341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8565215155957891305420227 12847822733936836958130341)
                    ·
                      refine ⟨2408966762613156929649439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847822733936836958130341 2408966762613156929649439)
                      ·
                        rfl

theorem cell23_4691446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4691446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691446 prefixEnd_4691446 := by exact prefixLift 4691446
  have htrace : WordTrace (prefixWord ++ tailWord_4691446) baseStart_4691446 baseEnd_4691446 := by
    simpa [prefixWord, tailWord_4691446, baseEnd_4691446] using wordTrace_append hprefix tailTrace_4691446
  have hstable : (prefixWord ++ tailWord_4691446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691446).length < 2 ^ (prefixWord ++ tailWord_4691446).sum := by decide
  have hdescent : baseEnd_4691446 < baseStart_4691446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691476 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4691476 : Nat := 118140960795 + 4691476 * 2 ^ 59
def prefixEnd_4691476 : Nat := 4983230072969 + 3 ^ 40 * 4691476 * 2
def baseEnd_4691476 : Nat := 2408982167032791812274301

theorem tailTrace_4691476 : CollatzResearch.WordTrace tailWord_4691476 prefixEnd_4691476 2408982167032791812274301 := by
  unfold tailWord_4691476
  simp only [CollatzResearch.WordTrace]
  refine ⟨85556093575795583577955141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114074791434394111437273521 85556093575795583577955141)
  ·
    refine ⟨16041767545461671920866589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85556093575795583577955141 16041767545461671920866589)
    ·
      refine ⟨6015662829548126970324971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16041767545461671920866589 6015662829548126970324971)
      ·
        refine ⟨9023494244322190455487457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015662829548126970324971 9023494244322190455487457)
        ·
          refine ⟨6767620683241642841615593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9023494244322190455487457 6767620683241642841615593)
          ·
            refine ⟨5075715512431232131211695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6767620683241642841615593 5075715512431232131211695)
            ·
              refine ⟨7613573268646848196817543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075715512431232131211695 7613573268646848196817543)
              ·
                refine ⟨11420359902970272295226315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613573268646848196817543 11420359902970272295226315)
                ·
                  refine ⟨17130539854455408442839473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11420359902970272295226315 17130539854455408442839473)
                  ·
                    refine ⟨12847904890841556332129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17130539854455408442839473 12847904890841556332129605)
                    ·
                      refine ⟨2408982167032791812274301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12847904890841556332129605 2408982167032791812274301)
                      ·
                        rfl

theorem cell23_4691476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4691476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691476 prefixEnd_4691476 := by exact prefixLift 4691476
  have htrace : WordTrace (prefixWord ++ tailWord_4691476) baseStart_4691476 baseEnd_4691476 := by
    simpa [prefixWord, tailWord_4691476, baseEnd_4691476] using wordTrace_append hprefix tailTrace_4691476
  have hstable : (prefixWord ++ tailWord_4691476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691476).length < 2 ^ (prefixWord ++ tailWord_4691476).sum := by decide
  have hdescent : baseEnd_4691476 < baseStart_4691476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691486 : List Nat := [4, 3, 3, 1, 1, 1, 1, 9]
def baseStart_4691486 : Nat := 118140960795 + 4691486 * 2 ^ 59
def prefixEnd_4691486 : Nat := 4983230072969 + 3 ^ 40 * 4691486 * 2
def baseEnd_4691486 : Nat := 89221751919975436042565

theorem tailTrace_4691486 : CollatzResearch.WordTrace tailWord_4691486 prefixEnd_4691486 89221751919975436042565 := by
  unfold tailWord_4691486
  simp only [CollatzResearch.WordTrace]
  refine ⟨21389068985194367357971789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114075034587703292575849541 21389068985194367357971789)
  ·
    refine ⟨8020900869447887759239421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21389068985194367357971789 8020900869447887759239421)
    ·
      refine ⟨3007837826042957909714783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8020900869447887759239421 3007837826042957909714783)
      ·
        refine ⟨4511756739064436864572175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3007837826042957909714783 4511756739064436864572175)
        ·
          refine ⟨6767635108596655296858263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511756739064436864572175 6767635108596655296858263)
          ·
            refine ⟨10151452662894982945287395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6767635108596655296858263 10151452662894982945287395)
            ·
              refine ⟨15227178994342474417931093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10151452662894982945287395 15227178994342474417931093)
              ·
                refine ⟨89221751919975436042565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15227178994342474417931093 89221751919975436042565)
                ·
                  rfl

theorem cell23_4691486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_4691486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691486 prefixEnd_4691486 := by exact prefixLift 4691486
  have htrace : WordTrace (prefixWord ++ tailWord_4691486) baseStart_4691486 baseEnd_4691486 := by
    simpa [prefixWord, tailWord_4691486, baseEnd_4691486] using wordTrace_append hprefix tailTrace_4691486
  have hstable : (prefixWord ++ tailWord_4691486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691486).length < 2 ^ (prefixWord ++ tailWord_4691486).sum := by decide
  have hdescent : baseEnd_4691486 < baseStart_4691486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691489 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4691489 : Nat := 118140960795 + 4691489 * 2 ^ 59
def prefixEnd_4691489 : Nat := 4983230072969 + 3 ^ 40 * 4691489 * 2
def baseEnd_4691489 : Nat := 2408988842281300261411741

theorem tailTrace_4691489 : CollatzResearch.WordTrace tailWord_4691489 prefixEnd_4691489 2408988842281300261411741 := by
  unfold tailWord_4691489
  simp only [CollatzResearch.WordTrace]
  refine ⟨171112661300544070376133521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114075107533696046917422347 171112661300544070376133521)
  ·
    refine ⟨128334495975408052782100141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171112661300544070376133521 128334495975408052782100141)
    ·
      refine ⟨48125435990778019793287553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128334495975408052782100141 48125435990778019793287553)
      ·
        refine ⟨36094076993083514844965665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48125435990778019793287553 36094076993083514844965665)
        ·
          refine ⟨27070557744812636133724249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36094076993083514844965665 27070557744812636133724249)
          ·
            refine ⟨20302918308609477100293187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27070557744812636133724249 20302918308609477100293187)
            ·
              refine ⟨30454377462914215650439781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20302918308609477100293187 30454377462914215650439781)
              ·
                refine ⟨5710195774296415434457459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30454377462914215650439781 5710195774296415434457459)
                ·
                  refine ⟨8565293661444623151686189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710195774296415434457459 8565293661444623151686189)
                  ·
                    refine ⟨3211985123041733681882321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8565293661444623151686189 3211985123041733681882321)
                    ·
                      refine ⟨2408988842281300261411741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3211985123041733681882321 2408988842281300261411741)
                      ·
                        rfl

theorem cell23_4691489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4691489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691489 prefixEnd_4691489 := by exact prefixLift 4691489
  have htrace : WordTrace (prefixWord ++ tailWord_4691489) baseStart_4691489 baseEnd_4691489 := by
    simpa [prefixWord, tailWord_4691489, baseEnd_4691489] using wordTrace_append hprefix tailTrace_4691489
  have hstable : (prefixWord ++ tailWord_4691489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691489).length < 2 ^ (prefixWord ++ tailWord_4691489).sum := by decide
  have hdescent : baseEnd_4691489 < baseStart_4691489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691505 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_4691505 : Nat := 118140960795 + 4691505 * 2 ^ 59
def prefixEnd_4691505 : Nat := 4983230072969 + 3 ^ 40 * 4691505 * 2
def baseEnd_4691505 : Nat := 2408997057971772198811667

theorem tailTrace_4691505 : CollatzResearch.WordTrace tailWord_4691505 prefixEnd_4691505 2408997057971772198811667 := by
  unfold tailWord_4691505
  simp only [CollatzResearch.WordTrace]
  refine ⟨171113244868486105108715969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114075496578990736739143979 171113244868486105108715969)
  ·
    refine ⟨128334933651364578831536977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171113244868486105108715969 128334933651364578831536977)
    ·
      refine ⟨96251200238523434123652733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128334933651364578831536977 96251200238523434123652733)
      ·
        refine ⟨36094200089446287796369775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96251200238523434123652733 36094200089446287796369775)
        ·
          refine ⟨54141300134169431694554663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36094200089446287796369775 54141300134169431694554663)
          ·
            refine ⟨81211950201254147541831995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54141300134169431694554663 81211950201254147541831995)
            ·
              refine ⟨121817925301881221312747993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81211950201254147541831995 121817925301881221312747993)
              ·
                refine ⟨91363443976410915984560995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121817925301881221312747993 91363443976410915984560995)
                ·
                  refine ⟨137045165964616373976841493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91363443976410915984560995 137045165964616373976841493)
                  ·
                    refine ⟨6423992154591392530164445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137045165964616373976841493 6423992154591392530164445)
                    ·
                      refine ⟨2408997057971772198811667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6423992154591392530164445 2408997057971772198811667)
                      ·
                        rfl

theorem cell23_4691505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_4691505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691505 prefixEnd_4691505 := by exact prefixLift 4691505
  have htrace : WordTrace (prefixWord ++ tailWord_4691505) baseStart_4691505 baseEnd_4691505 := by
    simpa [prefixWord, tailWord_4691505, baseEnd_4691505] using wordTrace_append hprefix tailTrace_4691505
  have hstable : (prefixWord ++ tailWord_4691505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691505).length < 2 ^ (prefixWord ++ tailWord_4691505).sum := by decide
  have hdescent : baseEnd_4691505 < baseStart_4691505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691519 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 4, 2, 2]
def baseStart_4691519 : Nat := 118140960795 + 4691519 * 2 ^ 59
def prefixEnd_4691519 : Nat := 4983230072969 + 3 ^ 40 * 4691519 * 2
def baseEnd_4691519 : Nat := 2409004246700935144036603

theorem tailTrace_4691519 : CollatzResearch.WordTrace tailWord_4691519 prefixEnd_4691519 2409004246700935144036603 := by
  unfold tailWord_4691519
  simp only [CollatzResearch.WordTrace]
  refine ⟨171113755490435385499725611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114075836993623590333150407 171113755490435385499725611)
  ·
    refine ⟨256670633235653078249588417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171113755490435385499725611 256670633235653078249588417)
    ·
      refine ⟨192502974926739808687191313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256670633235653078249588417 192502974926739808687191313)
      ·
        refine ⟨144377231195054856515393485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192502974926739808687191313 144377231195054856515393485)
        ·
          refine ⟨54141461698145571193272557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144377231195054856515393485 54141461698145571193272557)
          ·
            refine ⟨20303048136804589197477209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54141461698145571193272557 20303048136804589197477209)
            ·
              refine ⟨15227286102603441898107907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20303048136804589197477209 15227286102603441898107907)
              ·
                refine ⟨22840929153905162847161861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15227286102603441898107907 22840929153905162847161861)
                ·
                  refine ⟨4282674216357218033842849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22840929153905162847161861 4282674216357218033842849)
                  ·
                    refine ⟨3212005662267913525382137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282674216357218033842849 3212005662267913525382137)
                    ·
                      refine ⟨2409004246700935144036603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212005662267913525382137 2409004246700935144036603)
                      ·
                        rfl

theorem cell23_4691519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_4691519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691519 prefixEnd_4691519 := by exact prefixLift 4691519
  have htrace : WordTrace (prefixWord ++ tailWord_4691519) baseStart_4691519 baseEnd_4691519 := by
    simpa [prefixWord, tailWord_4691519, baseEnd_4691519] using wordTrace_append hprefix tailTrace_4691519
  have hstable : (prefixWord ++ tailWord_4691519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691519).length < 2 ^ (prefixWord ++ tailWord_4691519).sum := by decide
  have hdescent : baseEnd_4691519 < baseStart_4691519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691535 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3]
def baseStart_4691535 : Nat := 118140960795 + 4691535 * 2 ^ 59
def prefixEnd_4691535 : Nat := 4983230072969 + 3 ^ 40 * 4691535 * 2
def baseEnd_4691535 : Nat := 2409012462391407081436529

theorem tailTrace_4691535 : CollatzResearch.WordTrace tailWord_4691535 prefixEnd_4691535 2409012462391407081436529 := by
  unfold tailWord_4691535
  simp only [CollatzResearch.WordTrace]
  refine ⟨171114339058377420232308059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114076226038918280154872039 171114339058377420232308059)
  ·
    refine ⟨256671508587566130348462089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171114339058377420232308059 256671508587566130348462089)
    ·
      refine ⟨192503631440674597761346567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256671508587566130348462089 192503631440674597761346567)
      ·
        refine ⟨288755447161011896642019851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192503631440674597761346567 288755447161011896642019851)
        ·
          refine ⟨433133170741517844963029777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288755447161011896642019851 433133170741517844963029777)
          ·
            refine ⟨324849878056138383722272333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433133170741517844963029777 324849878056138383722272333)
            ·
              refine ⟨121818704271051893895852125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324849878056138383722272333 121818704271051893895852125)
              ·
                refine ⟨45682014101644460210944547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121818704271051893895852125 45682014101644460210944547)
                ·
                  refine ⟨68523021152466690316416821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45682014101644460210944547 68523021152466690316416821)
                  ·
                    refine ⟨6424033233043752217164077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68523021152466690316416821 6424033233043752217164077)
                    ·
                      refine ⟨2409012462391407081436529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424033233043752217164077 2409012462391407081436529)
                      ·
                        rfl

theorem cell23_4691535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_4691535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691535 prefixEnd_4691535 := by exact prefixLift 4691535
  have htrace : WordTrace (prefixWord ++ tailWord_4691535) baseStart_4691535 baseEnd_4691535 := by
    simpa [prefixWord, tailWord_4691535, baseEnd_4691535] using wordTrace_append hprefix tailTrace_4691535
  have hstable : (prefixWord ++ tailWord_4691535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691535).length < 2 ^ (prefixWord ++ tailWord_4691535).sum := by decide
  have hdescent : baseEnd_4691535 < baseStart_4691535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691575 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_4691575 : Nat := 118140960795 + 4691575 * 2 ^ 59
def prefixEnd_4691575 : Nat := 4983230072969 + 3 ^ 40 * 4691575 * 2
def baseEnd_4691575 : Nat := 2409033001617586924936345

theorem tailTrace_4691575 : CollatzResearch.WordTrace tailWord_4691575 prefixEnd_4691575 2409033001617586924936345 := by
  unfold tailWord_4691575
  simp only [CollatzResearch.WordTrace]
  refine ⟨171115797978232507063764179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114077198652155004709176119 171115797978232507063764179)
  ·
    refine ⟨256673696967348760595646269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171115797978232507063764179 256673696967348760595646269)
    ·
      refine ⟨96252636362755785223367351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256673696967348760595646269 96252636362755785223367351)
      ·
        refine ⟨144378954544133677835051027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96252636362755785223367351 144378954544133677835051027)
        ·
          refine ⟨216568431816200516752576541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144378954544133677835051027 216568431816200516752576541)
          ·
            refine ⟨81213161931075193782216203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216568431816200516752576541 81213161931075193782216203)
            ·
              refine ⟨121819742896612790673324305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81213161931075193782216203 121819742896612790673324305)
              ·
                refine ⟨91364807172459593004993229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121819742896612790673324305 91364807172459593004993229)
                ·
                  refine ⟨34261802689672347376872461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91364807172459593004993229 34261802689672347376872461)
                  ·
                    refine ⟨12848176008627130266327173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34261802689672347376872461 12848176008627130266327173)
                    ·
                      refine ⟨2409033001617586924936345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12848176008627130266327173 2409033001617586924936345)
                      ·
                        rfl

theorem cell23_4691575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_4691575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691575 prefixEnd_4691575 := by exact prefixLift 4691575
  have htrace : WordTrace (prefixWord ++ tailWord_4691575) baseStart_4691575 baseEnd_4691575 := by
    simpa [prefixWord, tailWord_4691575, baseEnd_4691575] using wordTrace_append hprefix tailTrace_4691575
  have hstable : (prefixWord ++ tailWord_4691575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691575).length < 2 ^ (prefixWord ++ tailWord_4691575).sum := by decide
  have hdescent : baseEnd_4691575 < baseStart_4691575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691605 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4691605 : Nat := 118140960795 + 4691605 * 2 ^ 59
def prefixEnd_4691605 : Nat := 4983230072969 + 3 ^ 40 * 4691605 * 2
def baseEnd_4691605 : Nat := 2409048406037221807561207

theorem tailTrace_4691605 : CollatzResearch.WordTrace tailWord_4691605 prefixEnd_4691605 2409048406037221807561207 := by
  unfold tailWord_4691605
  simp only [CollatzResearch.WordTrace]
  refine ⟨171116892168123822187356269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114077928112082548124904179 171116892168123822187356269)
  ·
    refine ⟨64168834563046433320258601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171116892168123822187356269 64168834563046433320258601)
    ·
      refine ⟨48126625922284824990193951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64168834563046433320258601 48126625922284824990193951)
      ·
        refine ⟨72189938883427237485290927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48126625922284824990193951 72189938883427237485290927)
        ·
          refine ⟨108284908325140856227936391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72189938883427237485290927 108284908325140856227936391)
          ·
            refine ⟨162427362487711284341904587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108284908325140856227936391 162427362487711284341904587)
            ·
              refine ⟨243641043731566926512856881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162427362487711284341904587 243641043731566926512856881)
              ·
                refine ⟨182730782798675194884642661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243641043731566926512856881 182730782798675194884642661)
                ·
                  refine ⟨34262021774751599040870499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182730782798675194884642661 34262021774751599040870499)
                  ·
                    refine ⟨51393032662127398561305749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34262021774751599040870499 51393032662127398561305749)
                    ·
                      refine ⟨2409048406037221807561207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51393032662127398561305749 2409048406037221807561207)
                      ·
                        rfl

theorem cell23_4691605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4691605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691605 prefixEnd_4691605 := by exact prefixLift 4691605
  have htrace : WordTrace (prefixWord ++ tailWord_4691605) baseStart_4691605 baseEnd_4691605 := by
    simpa [prefixWord, tailWord_4691605, baseEnd_4691605] using wordTrace_append hprefix tailTrace_4691605
  have hstable : (prefixWord ++ tailWord_4691605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691605).length < 2 ^ (prefixWord ++ tailWord_4691605).sum := by decide
  have hdescent : baseEnd_4691605 < baseStart_4691605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691629 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_4691629 : Nat := 118140960795 + 4691629 * 2 ^ 59
def prefixEnd_4691629 : Nat := 4983230072969 + 3 ^ 40 * 4691629 * 2
def baseEnd_4691629 : Nat := 2409060729572929713661097

theorem tailTrace_4691629 : CollatzResearch.WordTrace tailWord_4691629 prefixEnd_4691629 2409060729572929713661097 := by
  unfold tailWord_4691629
  simp only [CollatzResearch.WordTrace]
  refine ⟨171117767520036874286229941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114078511680024582857486627 171117767520036874286229941)
  ·
    refine ⟨16042290705003456964334057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171117767520036874286229941 16042290705003456964334057)
    ·
      refine ⟨12031718028752592723250543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16042290705003456964334057 12031718028752592723250543)
      ·
        refine ⟨18047577043128889084875815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031718028752592723250543 18047577043128889084875815)
        ·
          refine ⟨27071365564693333627313723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047577043128889084875815 27071365564693333627313723)
          ·
            refine ⟨40607048347040000440970585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27071365564693333627313723 40607048347040000440970585)
            ·
              refine ⟨30455286260280000330727939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40607048347040000440970585 30455286260280000330727939)
              ·
                refine ⟨45682929390420000496091909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30455286260280000330727939 45682929390420000496091909)
                ·
                  refine ⟨8565549260703750093017233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45682929390420000496091909 8565549260703750093017233)
                  ·
                    refine ⟨6424161945527812569762925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8565549260703750093017233 6424161945527812569762925)
                    ·
                      refine ⟨2409060729572929713661097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424161945527812569762925 2409060729572929713661097)
                      ·
                        rfl

theorem cell23_4691629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_4691629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691629 prefixEnd_4691629 := by exact prefixLift 4691629
  have htrace : WordTrace (prefixWord ++ tailWord_4691629) baseStart_4691629 baseEnd_4691629 := by
    simpa [prefixWord, tailWord_4691629, baseEnd_4691629] using wordTrace_append hprefix tailTrace_4691629
  have hstable : (prefixWord ++ tailWord_4691629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691629).length < 2 ^ (prefixWord ++ tailWord_4691629).sum := by decide
  have hdescent : baseEnd_4691629 < baseStart_4691629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691632 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 6]
def baseStart_4691632 : Nat := 118140960795 + 4691632 * 2 ^ 59
def prefixEnd_4691632 : Nat := 4983230072969 + 3 ^ 40 * 4691632 * 2
def baseEnd_4691632 : Nat := 267673585557210355769287

theorem tailTrace_4691632 : CollatzResearch.WordTrace tailWord_4691632 prefixEnd_4691632 267673585557210355769287 := by
  unfold tailWord_4691632
  simp only [CollatzResearch.WordTrace]
  refine ⟨85558938469513002899294575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114078584626017337199059433 85558938469513002899294575)
  ·
    refine ⟨128338407704269504348941863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85558938469513002899294575 128338407704269504348941863)
    ·
      refine ⟨192507611556404256523412795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128338407704269504348941863 192507611556404256523412795)
      ·
        refine ⟨288761417334606384785119193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192507611556404256523412795 288761417334606384785119193)
        ·
          refine ⟨216571063000954788588839395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288761417334606384785119193 216571063000954788588839395)
          ·
            refine ⟨324856594501432182883259093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216571063000954788588839395 324856594501432182883259093)
            ·
              refine ⟨7613826433627316786326385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 324856594501432182883259093 7613826433627316786326385)
              ·
                refine ⟨5710369825220487589744789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7613826433627316786326385 5710369825220487589744789)
                ·
                  refine ⟨267673585557210355769287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5710369825220487589744789 267673585557210355769287)
                  ·
                    rfl

theorem cell23_4691632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_4691632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691632 prefixEnd_4691632 := by exact prefixLift 4691632
  have htrace : WordTrace (prefixWord ++ tailWord_4691632) baseStart_4691632 baseEnd_4691632 := by
    simpa [prefixWord, tailWord_4691632, baseEnd_4691632] using wordTrace_append hprefix tailTrace_4691632
  have hstable : (prefixWord ++ tailWord_4691632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691632).length < 2 ^ (prefixWord ++ tailWord_4691632).sum := by decide
  have hdescent : baseEnd_4691632 < baseStart_4691632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691635 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8]
def baseStart_4691635 : Nat := 118140960795 + 4691635 * 2 ^ 59
def prefixEnd_4691635 : Nat := 4983230072969 + 3 ^ 40 * 4691635 * 2
def baseEnd_4691635 : Nat := 2409063810456856690186069

theorem tailTrace_4691635 : CollatzResearch.WordTrace tailWord_4691635 prefixEnd_4691635 2409063810456856690186069 := by
  unfold tailWord_4691635
  simp only [CollatzResearch.WordTrace]
  refine ⟨171117986358015137310948359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114078657572010091540632239 171117986358015137310948359)
  ·
    refine ⟨256676979537022705966422539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171117986358015137310948359 256676979537022705966422539)
    ·
      refine ⟨385015469305534058949633809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256676979537022705966422539 385015469305534058949633809)
      ·
        refine ⟨288761601979150544212225357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385015469305534058949633809 288761601979150544212225357)
        ·
          refine ⟨108285600742181454079584509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288761601979150544212225357 108285600742181454079584509)
          ·
            refine ⟨40607100278318045279844191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108285600742181454079584509 40607100278318045279844191)
            ·
              refine ⟨60910650417477067919766287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40607100278318045279844191 60910650417477067919766287)
              ·
                refine ⟨91365975626215601879649431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60910650417477067919766287 91365975626215601879649431)
                ·
                  refine ⟨137048963439323402819474147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91365975626215601879649431 137048963439323402819474147)
                  ·
                    refine ⟨205573445158985104229211221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137048963439323402819474147 205573445158985104229211221)
                    ·
                      refine ⟨2409063810456856690186069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205573445158985104229211221 2409063810456856690186069)
                      ·
                        rfl

theorem cell23_4691635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_4691635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691635 prefixEnd_4691635 := by exact prefixLift 4691635
  have htrace : WordTrace (prefixWord ++ tailWord_4691635) baseStart_4691635 baseEnd_4691635 := by
    simpa [prefixWord, tailWord_4691635, baseEnd_4691635] using wordTrace_append hprefix tailTrace_4691635
  have hstable : (prefixWord ++ tailWord_4691635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691635).length < 2 ^ (prefixWord ++ tailWord_4691635).sum := by decide
  have hdescent : baseEnd_4691635 < baseStart_4691635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691652 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4691652 : Nat := 118140960795 + 4691652 * 2 ^ 59
def prefixEnd_4691652 : Nat := 4983230072969 + 3 ^ 40 * 4691652 * 2
def baseEnd_4691652 : Nat := 2409072539627983123673491

theorem tailTrace_4691652 : CollatzResearch.WordTrace tailWord_4691652 prefixEnd_4691652 2409072539627983123673491 := by
  unfold tailWord_4691652
  simp only [CollatzResearch.WordTrace]
  refine ⟨85559303199476774607158605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114079070932635699476211473 85559303199476774607158605)
  ·
    refine ⟨32084738699803790477684477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85559303199476774607158605 32084738699803790477684477)
    ·
      refine ⟨12031777012426421429131679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32084738699803790477684477 12031777012426421429131679)
      ·
        refine ⟨18047665518639632143697519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031777012426421429131679 18047665518639632143697519)
        ·
          refine ⟨27071498277959448215546279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047665518639632143697519 27071498277959448215546279)
          ·
            refine ⟨40607247416939172323319419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27071498277959448215546279 40607247416939172323319419)
            ·
              refine ⟨60910871125408758484979129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40607247416939172323319419 60910871125408758484979129)
              ·
                refine ⟨45683153344056568863734347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60910871125408758484979129 45683153344056568863734347)
                ·
                  refine ⟨68524730016084853295601521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45683153344056568863734347 68524730016084853295601521)
                  ·
                    refine ⟨51393547512063639971701141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68524730016084853295601521 51393547512063639971701141)
                    ·
                      refine ⟨2409072539627983123673491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51393547512063639971701141 2409072539627983123673491)
                      ·
                        rfl

theorem cell23_4691652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4691652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691652 prefixEnd_4691652 := by exact prefixLift 4691652
  have htrace : WordTrace (prefixWord ++ tailWord_4691652) baseStart_4691652 baseEnd_4691652 := by
    simpa [prefixWord, tailWord_4691652, baseEnd_4691652] using wordTrace_append hprefix tailTrace_4691652
  have hstable : (prefixWord ++ tailWord_4691652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691652).length < 2 ^ (prefixWord ++ tailWord_4691652).sum := by decide
  have hdescent : baseEnd_4691652 < baseStart_4691652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691693 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_4691693 : Nat := 118140960795 + 4691693 * 2 ^ 59
def prefixEnd_4691693 : Nat := 4983230072969 + 3 ^ 40 * 4691693 * 2
def baseEnd_4691693 : Nat := 2409093592334817463260803

theorem tailTrace_4691693 : CollatzResearch.WordTrace tailWord_4691693 prefixEnd_4691693 2409093592334817463260803 := by
  unfold tailWord_4691693
  simp only [CollatzResearch.WordTrace]
  refine ⟨171120101791805013216559733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114080067861203342144373155 171120101791805013216559733)
  ·
    refine ⟨16042509542981719989052475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171120101791805013216559733 16042509542981719989052475)
    ·
      refine ⟨24063764314472579983578713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16042509542981719989052475 24063764314472579983578713)
      ·
        refine ⟨18047823235854434987684035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24063764314472579983578713 18047823235854434987684035)
        ·
          refine ⟨27071734853781652481526053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047823235854434987684035 27071734853781652481526053)
          ·
            refine ⟨5075950285084059840286135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27071734853781652481526053 5075950285084059840286135)
            ·
              refine ⟨7613925427626089760429203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075950285084059840286135 7613925427626089760429203)
              ·
                refine ⟨11420888141439134640643805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613925427626089760429203 11420888141439134640643805)
                ·
                  refine ⟨4282833053039675490241427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11420888141439134640643805 4282833053039675490241427)
                  ·
                    refine ⟨6424249579559513235362141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4282833053039675490241427 6424249579559513235362141)
                    ·
                      refine ⟨2409093592334817463260803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424249579559513235362141 2409093592334817463260803)
                      ·
                        rfl

theorem cell23_4691693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_4691693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691693 prefixEnd_4691693 := by exact prefixLift 4691693
  have htrace : WordTrace (prefixWord ++ tailWord_4691693) baseStart_4691693 baseEnd_4691693 := by
    simpa [prefixWord, tailWord_4691693, baseEnd_4691693] using wordTrace_append hprefix tailTrace_4691693
  have hstable : (prefixWord ++ tailWord_4691693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691693).length < 2 ^ (prefixWord ++ tailWord_4691693).sum := by decide
  have hdescent : baseEnd_4691693 < baseStart_4691693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691700 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4691700 : Nat := 118140960795 + 4691700 * 2 ^ 59
def prefixEnd_4691700 : Nat := 4983230072969 + 3 ^ 40 * 4691700 * 2
def baseEnd_4691700 : Nat := 267677465188822103985919

theorem tailTrace_4691700 : CollatzResearch.WordTrace tailWord_4691700 prefixEnd_4691700 267677465188822103985919 := by
  unfold tailWord_4691700
  simp only [CollatzResearch.WordTrace]
  refine ⟨85560178551389826706032277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114080238068519768941376369 85560178551389826706032277)
  ·
    refine ⟨4010633369596398126845263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85560178551389826706032277 4010633369596398126845263)
    ·
      refine ⟨6015950054394597190267895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4010633369596398126845263 6015950054394597190267895)
      ·
        refine ⟨9023925081591895785401843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015950054394597190267895 9023925081591895785401843)
        ·
          refine ⟨13535887622387843678102765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023925081591895785401843 13535887622387843678102765)
          ·
            refine ⟨5075957858395441379288537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13535887622387843678102765 5075957858395441379288537)
            ·
              refine ⟨3806968393796581034466403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075957858395441379288537 3806968393796581034466403)
              ·
                refine ⟨5710452590694871551699605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806968393796581034466403 5710452590694871551699605)
                ·
                  refine ⟨267677465188822103985919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5710452590694871551699605 267677465188822103985919)
                  ·
                    rfl

theorem cell23_4691700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4691700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691700 prefixEnd_4691700 := by exact prefixLift 4691700
  have htrace : WordTrace (prefixWord ++ tailWord_4691700) baseStart_4691700 baseEnd_4691700 := by
    simpa [prefixWord, tailWord_4691700, baseEnd_4691700] using wordTrace_append hprefix tailTrace_4691700
  have hstable : (prefixWord ++ tailWord_4691700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691700).length < 2 ^ (prefixWord ++ tailWord_4691700).sum := by decide
  have hdescent : baseEnd_4691700 < baseStart_4691700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691716 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4691716 : Nat := 118140960795 + 4691716 * 2 ^ 59
def prefixEnd_4691716 : Nat := 4983230072969 + 3 ^ 40 * 4691716 * 2
def baseEnd_4691716 : Nat := 2409105402389870873273197

theorem tailTrace_4691716 : CollatzResearch.WordTrace tailWord_4691716 prefixEnd_4691716 2409105402389870873273197 := by
  unfold tailWord_4691716
  simp only [CollatzResearch.WordTrace]
  refine ⟨85560470335360844072323501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114080627113814458763098001 85560470335360844072323501)
  ·
    refine ⟨32085176375760316527121313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85560470335360844072323501 32085176375760316527121313)
    ·
      refine ⟨24063882281820237395340985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32085176375760316527121313 24063882281820237395340985)
      ·
        refine ⟨18047911711365178046505739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24063882281820237395340985 18047911711365178046505739)
        ·
          refine ⟨27071867567047767069758609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047911711365178046505739 27071867567047767069758609)
          ·
            refine ⟨20303900675285825302318957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27071867567047767069758609 20303900675285825302318957)
            ·
              refine ⟨7613962753232184488369609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20303900675285825302318957 7613962753232184488369609)
              ·
                refine ⟨5710472064924138366277207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7613962753232184488369609 5710472064924138366277207)
                ·
                  refine ⟨8565708097386207549415811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710472064924138366277207 8565708097386207549415811)
                  ·
                    refine ⟨12848562146079311324123717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8565708097386207549415811 12848562146079311324123717)
                    ·
                      refine ⟨2409105402389870873273197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12848562146079311324123717 2409105402389870873273197)
                      ·
                        rfl

theorem cell23_4691716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4691716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691716 prefixEnd_4691716 := by exact prefixLift 4691716
  have htrace : WordTrace (prefixWord ++ tailWord_4691716) baseStart_4691716 baseEnd_4691716 := by
    simpa [prefixWord, tailWord_4691716, baseEnd_4691716] using wordTrace_append hprefix tailTrace_4691716
  have hstable : (prefixWord ++ tailWord_4691716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691716).length < 2 ^ (prefixWord ++ tailWord_4691716).sum := by decide
  have hdescent : baseEnd_4691716 < baseStart_4691716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691722 : List Nat := [3, 1, 2, 2, 1, 3, 2, 9]
def baseStart_4691722 : Nat := 118140960795 + 4691722 * 2 ^ 59
def prefixEnd_4691722 : Nat := 4983230072969 + 3 ^ 40 * 4691722 * 2
def baseEnd_4691722 : Nat := 89226240121251772214747

theorem tailTrace_4691722 : CollatzResearch.WordTrace tailWord_4691722 prefixEnd_4691722 89226240121251772214747 := by
  unfold tailWord_4691722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42780289877174987792341355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114080773005799967446243613 42780289877174987792341355)
  ·
    refine ⟨64170434815762481688512033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42780289877174987792341355 64170434815762481688512033)
    ·
      refine ⟨48127826111821861266384025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64170434815762481688512033 48127826111821861266384025)
      ·
        refine ⟨36095869583866395949788019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48127826111821861266384025 36095869583866395949788019)
        ·
          refine ⟨54143804375799593924682029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36095869583866395949788019 54143804375799593924682029)
          ·
            refine ⟨20303926640924847721755761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54143804375799593924682029 20303926640924847721755761)
            ·
              refine ⟨15227944980693635791316821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20303926640924847721755761 15227944980693635791316821)
              ·
                refine ⟨89226240121251772214747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15227944980693635791316821 89226240121251772214747)
                ·
                  rfl

theorem cell23_4691722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_4691722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691722 prefixEnd_4691722 := by exact prefixLift 4691722
  have htrace : WordTrace (prefixWord ++ tailWord_4691722) baseStart_4691722 baseEnd_4691722 := by
    simpa [prefixWord, tailWord_4691722, baseEnd_4691722] using wordTrace_append hprefix tailTrace_4691722
  have hstable : (prefixWord ++ tailWord_4691722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691722).length < 2 ^ (prefixWord ++ tailWord_4691722).sum := by decide
  have hdescent : baseEnd_4691722 < baseStart_4691722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691792 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_4691792 : Nat := 118140960795 + 4691792 * 2 ^ 59
def prefixEnd_4691792 : Nat := 4983230072969 + 3 ^ 40 * 4691792 * 2
def baseEnd_4691792 : Nat := 2409144426919612575922847

theorem tailTrace_4691792 : CollatzResearch.WordTrace tailWord_4691792 prefixEnd_4691792 2409144426919612575922847 := by
  unfold tailWord_4691792
  simp only [CollatzResearch.WordTrace]
  refine ⟨85561856309223176562206815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114082475078964235416275753 85561856309223176562206815)
  ·
    refine ⟨128342784463834764843310223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85561856309223176562206815 128342784463834764843310223)
    ·
      refine ⟨192514176695752147264965335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128342784463834764843310223 192514176695752147264965335)
      ·
        refine ⟨288771265043628220897448003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192514176695752147264965335 288771265043628220897448003)
        ·
          refine ⟨433156897565442331346172005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288771265043628220897448003 433156897565442331346172005)
          ·
            refine ⟨81216918293520437127407251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 433156897565442331346172005 81216918293520437127407251)
            ·
              refine ⟨121825377440280655691110877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81216918293520437127407251 121825377440280655691110877)
              ·
                refine ⟨45684516540105245884166579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121825377440280655691110877 45684516540105245884166579)
                ·
                  refine ⟨68526774810157868826249869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45684516540105245884166579 68526774810157868826249869)
                  ·
                    refine ⟨25697540553809200809843701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68526774810157868826249869 25697540553809200809843701)
                    ·
                      refine ⟨2409144426919612575922847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25697540553809200809843701 2409144426919612575922847)
                      ·
                        rfl

theorem cell23_4691792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_4691792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691792 prefixEnd_4691792 := by exact prefixLift 4691792
  have htrace : WordTrace (prefixWord ++ tailWord_4691792) baseStart_4691792 baseEnd_4691792 := by
    simpa [prefixWord, tailWord_4691792, baseEnd_4691792] using wordTrace_append hprefix tailTrace_4691792
  have hstable : (prefixWord ++ tailWord_4691792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691792).length < 2 ^ (prefixWord ++ tailWord_4691792).sum := by decide
  have hdescent : baseEnd_4691792 < baseStart_4691792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691793 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_4691793 : Nat := 118140960795 + 4691793 * 2 ^ 59
def prefixEnd_4691793 : Nat := 4983230072969 + 3 ^ 40 * 4691793 * 2
def baseEnd_4691793 : Nat := 2409144940400267072010343

theorem tailTrace_4691793 : CollatzResearch.WordTrace tailWord_4691793 prefixEnd_4691793 2409144940400267072010343 := by
  unfold tailWord_4691793
  simp only [CollatzResearch.WordTrace]
  refine ⟨171123749091442730295200033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114082499394295153530133355 171123749091442730295200033)
  ·
    refine ⟨128342811818582047721400025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171123749091442730295200033 128342811818582047721400025)
    ·
      refine ⟨96257108863936535791050019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128342811818582047721400025 96257108863936535791050019)
      ·
        refine ⟨144385663295904803686575029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96257108863936535791050019 144385663295904803686575029)
        ·
          refine ⟨13536155933991075345616409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144385663295904803686575029 13536155933991075345616409)
          ·
            refine ⟨10152116950493306509212307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13536155933991075345616409 10152116950493306509212307)
            ·
              refine ⟨15228175425739959763818461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152116950493306509212307 15228175425739959763818461)
              ·
                refine ⟨5710565784652484911431923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15228175425739959763818461 5710565784652484911431923)
                ·
                  refine ⟨8565848676978727367147885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710565784652484911431923 8565848676978727367147885)
                  ·
                    refine ⟨3212193253867022762680457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8565848676978727367147885 3212193253867022762680457)
                    ·
                      refine ⟨2409144940400267072010343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212193253867022762680457 2409144940400267072010343)
                      ·
                        rfl

theorem cell23_4691793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_4691793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691793 prefixEnd_4691793 := by exact prefixLift 4691793
  have htrace : WordTrace (prefixWord ++ tailWord_4691793) baseStart_4691793 baseEnd_4691793 := by
    simpa [prefixWord, tailWord_4691793, baseEnd_4691793] using wordTrace_append hprefix tailTrace_4691793
  have hstable : (prefixWord ++ tailWord_4691793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691793).length < 2 ^ (prefixWord ++ tailWord_4691793).sum := by decide
  have hdescent : baseEnd_4691793 < baseStart_4691793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691829 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 7]
def baseStart_4691829 : Nat := 118140960795 + 4691829 * 2 ^ 59
def prefixEnd_4691829 : Nat := 4983230072969 + 3 ^ 40 * 4691829 * 2
def baseEnd_4691829 : Nat := 267684825078203214573353

theorem tailTrace_4691829 : CollatzResearch.WordTrace tailWord_4691829 prefixEnd_4691829 267684825078203214573353 := by
  unfold tailWord_4691829
  simp only [CollatzResearch.WordTrace]
  refine ⟨171125062119312308443510541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114083374746208205629007027 171125062119312308443510541)
  ·
    refine ⟨64171898294742115666316453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171125062119312308443510541 64171898294742115666316453)
    ·
      refine ⟨12032230930264146687434335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64171898294742115666316453 12032230930264146687434335)
      ·
        refine ⟨18048346395396220031151503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032230930264146687434335 18048346395396220031151503)
        ·
          refine ⟨27072519593094330046727255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18048346395396220031151503 27072519593094330046727255)
          ·
            refine ⟨40608779389641495070090883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27072519593094330046727255 40608779389641495070090883)
            ·
              refine ⟨60913169084462242605136325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40608779389641495070090883 60913169084462242605136325)
              ·
                refine ⟨11421219203336670488463061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60913169084462242605136325 11421219203336670488463061)
                ·
                  refine ⟨267684825078203214573353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11421219203336670488463061 267684825078203214573353)
                  ·
                    rfl

theorem cell23_4691829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_4691829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691829 prefixEnd_4691829 := by exact prefixLift 4691829
  have htrace : WordTrace (prefixWord ++ tailWord_4691829) baseStart_4691829 baseEnd_4691829 := by
    simpa [prefixWord, tailWord_4691829, baseEnd_4691829] using wordTrace_append hprefix tailTrace_4691829
  have hstable : (prefixWord ++ tailWord_4691829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691829).length < 2 ^ (prefixWord ++ tailWord_4691829).sum := by decide
  have hdescent : baseEnd_4691829 < baseStart_4691829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4691832 : Nat := 118140960795 + 4691832 * 2 ^ 59
def prefixEnd_4691832 : Nat := 4983230072969 + 3 ^ 40 * 4691832 * 2
def baseEnd_4691832 : Nat := 2409164966145792419422663

theorem tailTrace_4691832 : CollatzResearch.WordTrace tailWord_4691832 prefixEnd_4691832 2409164966145792419422663 := by
  unfold tailWord_4691832
  simp only [CollatzResearch.WordTrace]
  refine ⟨85562585769150719977934875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114083447692200959970579833 85562585769150719977934875)
  ·
    refine ⟨128343878653726079966902313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85562585769150719977934875 128343878653726079966902313)
    ·
      refine ⟨96257908990294559975176735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128343878653726079966902313 96257908990294559975176735)
      ·
        refine ⟨144386863485441839962765103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96257908990294559975176735 144386863485441839962765103)
        ·
          refine ⟨216580295228162759944147655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144386863485441839962765103 216580295228162759944147655)
          ·
            refine ⟨324870442842244139916221483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216580295228162759944147655 324870442842244139916221483)
            ·
              refine ⟨487305664263366209874332225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324870442842244139916221483 487305664263366209874332225)
              ·
                refine ⟨365479248197524657405749169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487305664263366209874332225 365479248197524657405749169)
                ·
                  refine ⟨274109436148143493054311877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365479248197524657405749169 274109436148143493054311877)
                  ·
                    refine ⟨51395519277776904947683477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274109436148143493054311877 51395519277776904947683477)
                    ·
                      refine ⟨2409164966145792419422663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51395519277776904947683477 2409164966145792419422663)
                      ·
                        rfl

theorem cell23_4691832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4691832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691832 prefixEnd_4691832 := by exact prefixLift 4691832
  have htrace : WordTrace (prefixWord ++ tailWord_4691832) baseStart_4691832 baseEnd_4691832 := by
    simpa [prefixWord, tailWord_4691832, baseEnd_4691832] using wordTrace_append hprefix tailTrace_4691832
  have hstable : (prefixWord ++ tailWord_4691832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691832).length < 2 ^ (prefixWord ++ tailWord_4691832).sum := by decide
  have hdescent : baseEnd_4691832 < baseStart_4691832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691863 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 5]
def baseStart_4691863 : Nat := 118140960795 + 4691863 * 2 ^ 59
def prefixEnd_4691863 : Nat := 4983230072969 + 3 ^ 40 * 4691863 * 2
def baseEnd_4691863 : Nat := 267686764894009088681669

theorem tailTrace_4691863 : CollatzResearch.WordTrace tailWord_4691863 prefixEnd_4691863 267686764894009088681669 := by
  unfold tailWord_4691863
  simp only [CollatzResearch.WordTrace]
  refine ⟨171126302201189132250248243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114084201467459421500165495 171126302201189132250248243)
  ·
    refine ⟨256689453301783698375372365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171126302201189132250248243 256689453301783698375372365)
    ·
      refine ⟨96258544988168886890764637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256689453301783698375372365 96258544988168886890764637)
      ·
        refine ⟨36096954370563332584036739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96258544988168886890764637 36096954370563332584036739)
        ·
          refine ⟨54145431555844998876055109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36096954370563332584036739 54145431555844998876055109)
          ·
            refine ⟨10152268416720937289260333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54145431555844998876055109 10152268416720937289260333)
            ·
              refine ⟨3807100656270351483472625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10152268416720937289260333 3807100656270351483472625)
              ·
                refine ⟨2855325492202763612604469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807100656270351483472625 2855325492202763612604469)
                ·
                  refine ⟨267686764894009088681669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2855325492202763612604469 267686764894009088681669)
                  ·
                    rfl

theorem cell23_4691863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 5].length) (baseStart_4691863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691863 prefixEnd_4691863 := by exact prefixLift 4691863
  have htrace : WordTrace (prefixWord ++ tailWord_4691863) baseStart_4691863 baseEnd_4691863 := by
    simpa [prefixWord, tailWord_4691863, baseEnd_4691863] using wordTrace_append hprefix tailTrace_4691863
  have hstable : (prefixWord ++ tailWord_4691863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691863).length < 2 ^ (prefixWord ++ tailWord_4691863).sum := by decide
  have hdescent : baseEnd_4691863 < baseStart_4691863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691869 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4691869 : Nat := 118140960795 + 4691869 * 2 ^ 59
def prefixEnd_4691869 : Nat := 4983230072969 + 3 ^ 40 * 4691869 * 2
def baseEnd_4691869 : Nat := 2409183964930008774659993

theorem tailTrace_4691869 : CollatzResearch.WordTrace tailWord_4691869 prefixEnd_4691869 2409183964930008774659993 := by
  unfold tailWord_4691869
  simp only [CollatzResearch.WordTrace]
  refine ⟨171126521039167395274966661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114084347359444930183311107 171126521039167395274966661)
  ·
    refine ⟨32086222694843886614056249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171126521039167395274966661 32086222694843886614056249)
    ·
      refine ⟨24064667021132914960542187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32086222694843886614056249 24064667021132914960542187)
      ·
        refine ⟨36097000531699372440813281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24064667021132914960542187 36097000531699372440813281)
        ·
          refine ⟨27072750398774529330609961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36097000531699372440813281 27072750398774529330609961)
          ·
            refine ⟨20304562799080896997957471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27072750398774529330609961 20304562799080896997957471)
            ·
              refine ⟨30456844198621345496936207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20304562799080896997957471 30456844198621345496936207)
              ·
                refine ⟨45685266297932018245404311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30456844198621345496936207 45685266297932018245404311)
                ·
                  refine ⟨68527899446898027368106467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45685266297932018245404311 68527899446898027368106467)
                  ·
                    refine ⟨102791849170347041052159701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68527899446898027368106467 102791849170347041052159701)
                    ·
                      refine ⟨2409183964930008774659993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102791849170347041052159701 2409183964930008774659993)
                      ·
                        rfl

theorem cell23_4691869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4691869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691869 prefixEnd_4691869 := by exact prefixLift 4691869
  have htrace : WordTrace (prefixWord ++ tailWord_4691869) baseStart_4691869 baseEnd_4691869 := by
    simpa [prefixWord, tailWord_4691869, baseEnd_4691869] using wordTrace_append hprefix tailTrace_4691869
  have hstable : (prefixWord ++ tailWord_4691869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691869).length < 2 ^ (prefixWord ++ tailWord_4691869).sum := by decide
  have hdescent : baseEnd_4691869 < baseStart_4691869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691874 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4691874 : Nat := 118140960795 + 4691874 * 2 ^ 59
def prefixEnd_4691874 : Nat := 4983230072969 + 3 ^ 40 * 4691874 * 2
def baseEnd_4691874 : Nat := 2409186532333281255097471

theorem tailTrace_4691874 : CollatzResearch.WordTrace tailWord_4691874 prefixEnd_4691874 2409186532333281255097471 := by
  unfold tailWord_4691874
  simp only [CollatzResearch.WordTrace]
  refine ⟨42781675851037320282224669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114084468936099520752599117 42781675851037320282224669)
  ·
    refine ⟨16043128444138995105834251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42781675851037320282224669 16043128444138995105834251)
    ·
      refine ⟨24064692666208492658751377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16043128444138995105834251 24064692666208492658751377)
      ·
        refine ⟨18048519499656369494063533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24064692666208492658751377 18048519499656369494063533)
        ·
          refine ⟨6768194812371138560273825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18048519499656369494063533 6768194812371138560273825)
          ·
            refine ⟨5076146109278353920205369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6768194812371138560273825 5076146109278353920205369)
            ·
              refine ⟨3807109581958765440154027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5076146109278353920205369 3807109581958765440154027)
              ·
                refine ⟨5710664372938148160231041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807109581958765440154027 5710664372938148160231041)
                ·
                  refine ⟨4282998279703611120173281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5710664372938148160231041 4282998279703611120173281)
                  ·
                    refine ⟨3212248709777708340129961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4282998279703611120173281 3212248709777708340129961)
                    ·
                      refine ⟨2409186532333281255097471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212248709777708340129961 2409186532333281255097471)
                      ·
                        rfl

theorem cell23_4691874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4691874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691874 prefixEnd_4691874 := by exact prefixLift 4691874
  have htrace : WordTrace (prefixWord ++ tailWord_4691874) baseStart_4691874 baseEnd_4691874 := by
    simpa [prefixWord, tailWord_4691874, baseEnd_4691874] using wordTrace_append hprefix tailTrace_4691874
  have hstable : (prefixWord ++ tailWord_4691874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691874).length < 2 ^ (prefixWord ++ tailWord_4691874).sum := by decide
  have hdescent : baseEnd_4691874 < baseStart_4691874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691896 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_4691896 : Nat := 118140960795 + 4691896 * 2 ^ 59
def prefixEnd_4691896 : Nat := 4983230072969 + 3 ^ 40 * 4691896 * 2
def baseEnd_4691896 : Nat := 2409197828907680169022369

theorem tailTrace_4691896 : CollatzResearch.WordTrace tailWord_4691896 prefixEnd_4691896 2409197828907680169022369 := by
  unfold tailWord_4691896
  simp only [CollatzResearch.WordTrace]
  refine ⟨85563752905034789443099771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114085003873379719257466361 85563752905034789443099771)
  ·
    refine ⟨128345629357552184164649657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85563752905034789443099771 128345629357552184164649657)
    ·
      refine ⟨96259222018164138123487243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128345629357552184164649657 96259222018164138123487243)
      ·
        refine ⟨144388833027246207185230865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96259222018164138123487243 144388833027246207185230865)
        ·
          refine ⟨108291624770434655388923149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144388833027246207185230865 108291624770434655388923149)
          ·
            refine ⟨40609359288912995770846181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108291624770434655388923149 40609359288912995770846181)
            ·
              refine ⟨7614254866671186707033659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40609359288912995770846181 7614254866671186707033659)
              ·
                refine ⟨11421382300006780060550489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614254866671186707033659 11421382300006780060550489)
                ·
                  refine ⟨8566036725005085045412867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11421382300006780060550489 8566036725005085045412867)
                  ·
                    refine ⟨12849055087507627568119301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566036725005085045412867 12849055087507627568119301)
                    ·
                      refine ⟨2409197828907680169022369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12849055087507627568119301 2409197828907680169022369)
                      ·
                        rfl

theorem cell23_4691896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_4691896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691896 prefixEnd_4691896 := by exact prefixLift 4691896
  have htrace : WordTrace (prefixWord ++ tailWord_4691896) baseStart_4691896 baseEnd_4691896 := by
    simpa [prefixWord, tailWord_4691896, baseEnd_4691896] using wordTrace_append hprefix tailTrace_4691896
  have hstable : (prefixWord ++ tailWord_4691896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691896).length < 2 ^ (prefixWord ++ tailWord_4691896).sum := by decide
  have hdescent : baseEnd_4691896 < baseStart_4691896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691950 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4691950 : Nat := 118140960795 + 4691950 * 2 ^ 59
def prefixEnd_4691950 : Nat := 4983230072969 + 3 ^ 40 * 4691950 * 2
def baseEnd_4691950 : Nat := 2409225556863022957747121

theorem tailTrace_4691950 : CollatzResearch.WordTrace tailWord_4691950 prefixEnd_4691950 2409225556863022957747121 := by
  unfold tailWord_4691950
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391184418984243263583163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114086316901249297405776869 21391184418984243263583163)
  ·
    refine ⟨32086776628476364895374745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21391184418984243263583163 32086776628476364895374745)
    ·
      refine ⟨24065082471357273671531059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32086776628476364895374745 24065082471357273671531059)
      ·
        refine ⟨36097623707035910507296589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24065082471357273671531059 36097623707035910507296589)
        ·
          refine ⟨13536608890138466440236221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36097623707035910507296589 13536608890138466440236221)
          ·
            refine ⟨5076228333801924915088583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13536608890138466440236221 5076228333801924915088583)
            ·
              refine ⟨7614342500702887372632875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076228333801924915088583 7614342500702887372632875)
              ·
                refine ⟨11421513751054331058949313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614342500702887372632875 11421513751054331058949313)
                ·
                  refine ⟨8566135313290748294211985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11421513751054331058949313 8566135313290748294211985)
                  ·
                    refine ⟨6424601484968061220658989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8566135313290748294211985 6424601484968061220658989)
                    ·
                      refine ⟨2409225556863022957747121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424601484968061220658989 2409225556863022957747121)
                      ·
                        rfl

theorem cell23_4691950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4691950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691950 prefixEnd_4691950 := by exact prefixLift 4691950
  have htrace : WordTrace (prefixWord ++ tailWord_4691950) baseStart_4691950 baseEnd_4691950 := by
    simpa [prefixWord, tailWord_4691950, baseEnd_4691950] using wordTrace_append hprefix tailTrace_4691950
  have hstable : (prefixWord ++ tailWord_4691950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691950).length < 2 ^ (prefixWord ++ tailWord_4691950).sum := by decide
  have hdescent : baseEnd_4691950 < baseStart_4691950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4691980 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_4691980 : Nat := 118140960795 + 4691980 * 2 ^ 59
def prefixEnd_4691980 : Nat := 4983230072969 + 3 ^ 40 * 4691980 * 2
def baseEnd_4691980 : Nat := 2409240961282657840371983

theorem tailTrace_4691980 : CollatzResearch.WordTrace tailWord_4691980 prefixEnd_4691980 2409240961282657840371983 := by
  unfold tailWord_4691980
  simp only [CollatzResearch.WordTrace]
  refine ⟨85565284770882630616128697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114087046361176840821504929 85565284770882630616128697)
  ·
    refine ⟨64173963578161972962096523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85565284770882630616128697 64173963578161972962096523)
    ·
      refine ⟨96260945367242959443144785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64173963578161972962096523 96260945367242959443144785)
      ·
        refine ⟨72195709025432219582358589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96260945367242959443144785 72195709025432219582358589)
        ·
          refine ⟨27073390884537082343384471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72195709025432219582358589 27073390884537082343384471)
          ·
            refine ⟨40610086326805623515076707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27073390884537082343384471 40610086326805623515076707)
            ·
              refine ⟨60915129490208435272615061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40610086326805623515076707 60915129490208435272615061)
              ·
                refine ⟨2855396694853520403403831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60915129490208435272615061 2855396694853520403403831)
                ·
                  refine ⟨4283095042280280605105747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855396694853520403403831 4283095042280280605105747)
                  ·
                    refine ⟨6424642563420420907658621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283095042280280605105747 6424642563420420907658621)
                    ·
                      refine ⟨2409240961282657840371983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424642563420420907658621 2409240961282657840371983)
                      ·
                        rfl

theorem cell23_4691980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_4691980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4691980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4691980 prefixEnd_4691980 := by exact prefixLift 4691980
  have htrace : WordTrace (prefixWord ++ tailWord_4691980) baseStart_4691980 baseEnd_4691980 := by
    simpa [prefixWord, tailWord_4691980, baseEnd_4691980] using wordTrace_append hprefix tailTrace_4691980
  have hstable : (prefixWord ++ tailWord_4691980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4691980).length < 2 ^ (prefixWord ++ tailWord_4691980).sum := by decide
  have hdescent : baseEnd_4691980 < baseStart_4691980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4691980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692003 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 4]
def baseStart_4692003 : Nat := 118140960795 + 4692003 * 2 ^ 59
def prefixEnd_4692003 : Nat := 4983230072969 + 3 ^ 40 * 4692003 * 2
def baseEnd_4692003 : Nat := 2409252771337711250384377

theorem tailTrace_4692003 : CollatzResearch.WordTrace tailWord_4692003 prefixEnd_4692003 2409252771337711250384377 := by
  unfold tailWord_4692003
  simp only [CollatzResearch.WordTrace]
  refine ⟨171131408420681936160344663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114087605613787957440229775 171131408420681936160344663)
  ·
    refine ⟨256697112631022904240516995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171131408420681936160344663 256697112631022904240516995)
    ·
      refine ⟨385045668946534356360775493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256697112631022904240516995 385045668946534356360775493)
      ·
        refine ⟨72196062927475191817645405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385045668946534356360775493 72196062927475191817645405)
        ·
          refine ⟨27073523597803196931617027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72196062927475191817645405 27073523597803196931617027)
          ·
            refine ⟨40610285396704795397425541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27073523597803196931617027 40610285396704795397425541)
            ·
              refine ⟨7614428511882149137017289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40610285396704795397425541 7614428511882149137017289)
              ·
                refine ⟨5710821383911611852762967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7614428511882149137017289 5710821383911611852762967)
                ·
                  refine ⟨8566232075867417779144451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710821383911611852762967 8566232075867417779144451)
                  ·
                    refine ⟨12849348113801126668716677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566232075867417779144451 12849348113801126668716677)
                    ·
                      refine ⟨2409252771337711250384377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12849348113801126668716677 2409252771337711250384377)
                      ·
                        rfl

theorem cell23_4692003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_4692003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692003 prefixEnd_4692003 := by exact prefixLift 4692003
  have htrace : WordTrace (prefixWord ++ tailWord_4692003) baseStart_4692003 baseEnd_4692003 := by
    simpa [prefixWord, tailWord_4692003, baseEnd_4692003] using wordTrace_append hprefix tailTrace_4692003
  have hstable : (prefixWord ++ tailWord_4692003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692003).length < 2 ^ (prefixWord ++ tailWord_4692003).sum := by decide
  have hdescent : baseEnd_4692003 < baseStart_4692003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692014 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4692014 : Nat := 118140960795 + 4692014 * 2 ^ 59
def prefixEnd_4692014 : Nat := 4983230072969 + 3 ^ 40 * 4692014 * 2
def baseEnd_4692014 : Nat := 2409258419624910707346827

theorem tailTrace_4692014 : CollatzResearch.WordTrace tailWord_4692014 prefixEnd_4692014 2409258419624910707346827 := by
  unfold tailWord_4692014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21391476202955260629874387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114087873082428056692663397 21391476202955260629874387)
  ·
    refine ⟨32087214304432890944811581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21391476202955260629874387 32087214304432890944811581)
    ·
      refine ⟨12032705364162334104304343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32087214304432890944811581 12032705364162334104304343)
      ·
        refine ⟨18049058046243501156456515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12032705364162334104304343 18049058046243501156456515)
        ·
          refine ⟨27073587069365251734684773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18049058046243501156456515 27073587069365251734684773)
          ·
            refine ⟨5076297575505984700253395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27073587069365251734684773 5076297575505984700253395)
            ·
              refine ⟨7614446363258977050380093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076297575505984700253395 7614446363258977050380093)
              ·
                refine ⟨2855417386222116393892535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7614446363258977050380093 2855417386222116393892535)
                ·
                  refine ⟨4283126079333174590838803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855417386222116393892535 4283126079333174590838803)
                  ·
                    refine ⟨6424689118999761886258205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283126079333174590838803 6424689118999761886258205)
                    ·
                      refine ⟨2409258419624910707346827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424689118999761886258205 2409258419624910707346827)
                      ·
                        rfl

theorem cell23_4692014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4692014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692014 prefixEnd_4692014 := by exact prefixLift 4692014
  have htrace : WordTrace (prefixWord ++ tailWord_4692014) baseStart_4692014 baseEnd_4692014 := by
    simpa [prefixWord, tailWord_4692014, baseEnd_4692014] using wordTrace_append hprefix tailTrace_4692014
  have hstable : (prefixWord ++ tailWord_4692014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692014).length < 2 ^ (prefixWord ++ tailWord_4692014).sum := by decide
  have hdescent : baseEnd_4692014 < baseStart_4692014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692023 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_4692023 : Nat := 118140960795 + 4692023 * 2 ^ 59
def prefixEnd_4692023 : Nat := 4983230072969 + 3 ^ 40 * 4692023 * 2
def baseEnd_4692023 : Nat := 2409263040950801172134285

theorem tailTrace_4692023 : CollatzResearch.WordTrace tailWord_4692023 prefixEnd_4692023 2409263040950801172134285 := by
  unfold tailWord_4692023
  simp only [CollatzResearch.WordTrace]
  refine ⟨171132137880609479576072723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114088091920406319717381815 171132137880609479576072723)
  ·
    refine ⟨256698206820914219364109085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171132137880609479576072723 256698206820914219364109085)
    ·
      refine ⟨96261827557842832261540907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256698206820914219364109085 96261827557842832261540907)
      ·
        refine ⟨144392741336764248392311361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96261827557842832261540907 144392741336764248392311361)
        ·
          refine ⟨108294556002573186294233521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144392741336764248392311361 108294556002573186294233521)
          ·
            refine ⟨81220917001929889720675141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108294556002573186294233521 81220917001929889720675141)
            ·
              refine ⟨15228921937861854322626589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81220917001929889720675141 15228921937861854322626589)
              ·
                refine ⟨5710845726698195370984971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15228921937861854322626589 5710845726698195370984971)
                ·
                  refine ⟨8566268590047293056477457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710845726698195370984971 8566268590047293056477457)
                  ·
                    refine ⟨6424701442535469792358093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8566268590047293056477457 6424701442535469792358093)
                    ·
                      refine ⟨2409263040950801172134285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6424701442535469792358093 2409263040950801172134285)
                      ·
                        rfl

theorem cell23_4692023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_4692023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692023 prefixEnd_4692023 := by exact prefixLift 4692023
  have htrace : WordTrace (prefixWord ++ tailWord_4692023) baseStart_4692023 baseEnd_4692023 := by
    simpa [prefixWord, tailWord_4692023, baseEnd_4692023] using wordTrace_append hprefix tailTrace_4692023
  have hstable : (prefixWord ++ tailWord_4692023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692023).length < 2 ^ (prefixWord ++ tailWord_4692023).sum := by decide
  have hdescent : baseEnd_4692023 < baseStart_4692023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692054 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4692054 : Nat := 118140960795 + 4692054 * 2 ^ 59
def prefixEnd_4692054 : Nat := 4983230072969 + 3 ^ 40 * 4692054 * 2
def baseEnd_4692054 : Nat := 2409278958851090550846643

theorem tailTrace_4692054 : CollatzResearch.WordTrace tailWord_4692054 prefixEnd_4692054 2409278958851090550846643 := by
  unfold tailWord_4692054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10695829283968573241903201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114088845695664781246967477 10695829283968573241903201)
  ·
    refine ⟨8021871962976429931427401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10695829283968573241903201 8021871962976429931427401)
    ·
      refine ⟨6016403972232322448570551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8021871962976429931427401 6016403972232322448570551)
      ·
        refine ⟨9024605958348483672855827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016403972232322448570551 9024605958348483672855827)
        ·
          refine ⟨13536908937522725509283741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9024605958348483672855827 13536908937522725509283741)
          ·
            refine ⟨5076340851571022065981403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13536908937522725509283741 5076340851571022065981403)
            ·
              refine ⟨7614511277356533098972105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076340851571022065981403 7614511277356533098972105)
              ·
                refine ⟨5710883458017399824229079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7614511277356533098972105 5710883458017399824229079)
                ·
                  refine ⟨8566325187026099736343619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5710883458017399824229079 8566325187026099736343619)
                  ·
                    refine ⟨12849487780539149604515429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566325187026099736343619 12849487780539149604515429)
                    ·
                      refine ⟨2409278958851090550846643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12849487780539149604515429 2409278958851090550846643)
                      ·
                        rfl

theorem cell23_4692054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4692054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692054 prefixEnd_4692054 := by exact prefixLift 4692054
  have htrace : WordTrace (prefixWord ++ tailWord_4692054) baseStart_4692054 baseEnd_4692054 := by
    simpa [prefixWord, tailWord_4692054, baseEnd_4692054] using wordTrace_append hprefix tailTrace_4692054
  have hstable : (prefixWord ++ tailWord_4692054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692054).length < 2 ^ (prefixWord ++ tailWord_4692054).sum := by decide
  have hdescent : baseEnd_4692054 < baseStart_4692054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692161 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4692161 : Nat := 118140960795 + 4692161 * 2 ^ 59
def prefixEnd_4692161 : Nat := 4983230072969 + 3 ^ 40 * 4692161 * 2
def baseEnd_4692161 : Nat := 2409333901281121632208651

theorem tailTrace_4692161 : CollatzResearch.WordTrace tailWord_4692161 prefixEnd_4692161 2409333901281121632208651 := by
  unfold tailWord_4692161
  simp only [CollatzResearch.WordTrace]
  refine ⟨171137171154109529144596337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114091447436073019429730891 171137171154109529144596337)
  ·
    refine ⟨128352878365582146858447253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171137171154109529144596337 128352878365582146858447253)
    ·
      refine ⟨6016541173386663133989715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128352878365582146858447253 6016541173386663133989715)
      ·
        refine ⟨9024811760079994700984573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016541173386663133989715 9024811760079994700984573)
        ·
          refine ⟨3384304410029998012869215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9024811760079994700984573 3384304410029998012869215)
          ·
            refine ⟨5076456615044997019303823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384304410029998012869215 5076456615044997019303823)
            ·
              refine ⟨7614684922567495528955735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076456615044997019303823 7614684922567495528955735)
              ·
                refine ⟨11422027383851243293433603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614684922567495528955735 11422027383851243293433603)
                ·
                  refine ⟨17133041075776864940150405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11422027383851243293433603 17133041075776864940150405)
                  ·
                    refine ⟨3212445201708162176278201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17133041075776864940150405 3212445201708162176278201)
                    ·
                      refine ⟨2409333901281121632208651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212445201708162176278201 2409333901281121632208651)
                      ·
                        rfl

theorem cell23_4692161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4692161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692161 prefixEnd_4692161 := by exact prefixLift 4692161
  have htrace : WordTrace (prefixWord ++ tailWord_4692161) baseStart_4692161 baseEnd_4692161 := by
    simpa [prefixWord, tailWord_4692161, baseEnd_4692161] using wordTrace_append hprefix tailTrace_4692161
  have hstable : (prefixWord ++ tailWord_4692161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692161).length < 2 ^ (prefixWord ++ tailWord_4692161).sum := by decide
  have hdescent : baseEnd_4692161 < baseStart_4692161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692183 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_4692183 : Nat := 118140960795 + 4692183 * 2 ^ 59
def prefixEnd_4692183 : Nat := 4983230072969 + 3 ^ 40 * 4692183 * 2
def baseEnd_4692183 : Nat := 2409345197855520546133549

theorem tailTrace_4692183 : CollatzResearch.WordTrace tailWord_4692183 prefixEnd_4692183 2409345197855520546133549 := by
  unfold tailWord_4692183
  simp only [CollatzResearch.WordTrace]
  refine ⟨171137973560029826901897203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114091982373353217934598135 171137973560029826901897203)
  ·
    refine ⟨256706960340044740352845805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171137973560029826901897203 256706960340044740352845805)
    ·
      refine ⟨96265110127516777632317177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256706960340044740352845805 96265110127516777632317177)
      ·
        refine ⟨72198832595637583224237883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96265110127516777632317177 72198832595637583224237883)
        ·
          refine ⟨108298248893456374836356825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72198832595637583224237883 108298248893456374836356825)
          ·
            refine ⟨81223686670092281127267619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108298248893456374836356825 81223686670092281127267619)
            ·
              refine ⟨121835530005138421690901429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81223686670092281127267619 121835530005138421690901429)
              ·
                refine ⟨11422080937981727033522009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121835530005138421690901429 11422080937981727033522009)
                ·
                  refine ⟨8566560703486295275141507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422080937981727033522009 8566560703486295275141507)
                  ·
                    refine ⟨12849841055229442912712261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566560703486295275141507 12849841055229442912712261)
                    ·
                      refine ⟨2409345197855520546133549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12849841055229442912712261 2409345197855520546133549)
                      ·
                        rfl

theorem cell23_4692183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_4692183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692183 prefixEnd_4692183 := by exact prefixLift 4692183
  have htrace : WordTrace (prefixWord ++ tailWord_4692183) baseStart_4692183 baseEnd_4692183 := by
    simpa [prefixWord, tailWord_4692183, baseEnd_4692183] using wordTrace_append hprefix tailTrace_4692183
  have hstable : (prefixWord ++ tailWord_4692183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692183).length < 2 ^ (prefixWord ++ tailWord_4692183).sum := by decide
  have hdescent : baseEnd_4692183 < baseStart_4692183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692200 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4692200 : Nat := 118140960795 + 4692200 * 2 ^ 59
def prefixEnd_4692200 : Nat := 4983230072969 + 3 ^ 40 * 4692200 * 2
def baseEnd_4692200 : Nat := 2409353927026646979620971

theorem tailTrace_4692200 : CollatzResearch.WordTrace tailWord_4692200 prefixEnd_4692200 2409353927026646979620971 := by
  unfold tailWord_4692200
  simp only [CollatzResearch.WordTrace]
  refine ⟨85569296800484119402633027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114092395733978825870177369 85569296800484119402633027)
  ·
    refine ⟨128353945200726179103949541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85569296800484119402633027 128353945200726179103949541)
    ·
      refine ⟨24066364725136158581990539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128353945200726179103949541 24066364725136158581990539)
      ·
        refine ⟨36099547087704237872985809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24066364725136158581990539 36099547087704237872985809)
        ·
          refine ⟨27074660315778178404739357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36099547087704237872985809 27074660315778178404739357)
          ·
            refine ⟨10152997618416816901777259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27074660315778178404739357 10152997618416816901777259)
            ·
              refine ⟨15229496427625225352665889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152997618416816901777259 15229496427625225352665889)
              ·
                refine ⟨11422122320718919014499417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15229496427625225352665889 11422122320718919014499417)
                ·
                  refine ⟨8566591740539189260874563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422122320718919014499417 8566591740539189260874563)
                  ·
                    refine ⟨12849887610808783891311845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8566591740539189260874563 12849887610808783891311845)
                    ·
                      refine ⟨2409353927026646979620971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12849887610808783891311845 2409353927026646979620971)
                      ·
                        rfl

theorem cell23_4692200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4692200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692200 prefixEnd_4692200 := by exact prefixLift 4692200
  have htrace : WordTrace (prefixWord ++ tailWord_4692200) baseStart_4692200 baseEnd_4692200 := by
    simpa [prefixWord, tailWord_4692200, baseEnd_4692200] using wordTrace_append hprefix tailTrace_4692200
  have hstable : (prefixWord ++ tailWord_4692200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692200).length < 2 ^ (prefixWord ++ tailWord_4692200).sum := by decide
  have hdescent : baseEnd_4692200 < baseStart_4692200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692223 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 6]
def baseStart_4692223 : Nat := 118140960795 + 4692223 * 2 ^ 59
def prefixEnd_4692223 : Nat := 4983230072969 + 3 ^ 40 * 4692223 * 2
def baseEnd_4692223 : Nat := 267707304120188932181485

theorem tailTrace_4692223 : CollatzResearch.WordTrace tailWord_4692223 prefixEnd_4692223 267707304120188932181485 := by
  unfold tailWord_4692223
  simp only [CollatzResearch.WordTrace]
  refine ⟨171139432479884913733353323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114092954986589942488902215 171139432479884913733353323)
  ·
    refine ⟨256709148719827370600029985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171139432479884913733353323 256709148719827370600029985)
    ·
      refine ⟨192531861539870527950022489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256709148719827370600029985 192531861539870527950022489)
      ·
        refine ⟨144398896154902895962516867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192531861539870527950022489 144398896154902895962516867)
        ·
          refine ⟨216598344232354343943775301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144398896154902895962516867 216598344232354343943775301)
          ·
            refine ⟨40612189543566439489457869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216598344232354343943775301 40612189543566439489457869)
            ·
              refine ⟨15229571078837414808546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40612189543566439489457869 15229571078837414808546701)
              ·
                refine ⟨5711089154564030553205013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15229571078837414808546701 5711089154564030553205013)
                ·
                  refine ⟨267707304120188932181485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5711089154564030553205013 267707304120188932181485)
                  ·
                    rfl

theorem cell23_4692223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 6].length) (baseStart_4692223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692223 prefixEnd_4692223 := by exact prefixLift 4692223
  have htrace : WordTrace (prefixWord ++ tailWord_4692223) baseStart_4692223 baseEnd_4692223 := by
    simpa [prefixWord, tailWord_4692223, baseEnd_4692223] using wordTrace_append hprefix tailTrace_4692223
  have hstable : (prefixWord ++ tailWord_4692223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692223).length < 2 ^ (prefixWord ++ tailWord_4692223).sum := by decide
  have hdescent : baseEnd_4692223 < baseStart_4692223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692254 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4692254 : Nat := 118140960795 + 4692254 * 2 ^ 59
def prefixEnd_4692254 : Nat := 4983230072969 + 3 ^ 40 * 4692254 * 2
def baseEnd_4692254 : Nat := 2409381654981989768345723

theorem tailTrace_4692254 : CollatzResearch.WordTrace tailWord_4692254 prefixEnd_4692254 2409381654981989768345723 := by
  unfold tailWord_4692254
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392570392846575753466477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114093708761848404018487877 21392570392846575753466477)
  ·
    refine ⟨8022213897317465907549929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21392570392846575753466477 8022213897317465907549929)
    ·
      refine ⟨6016660422988099430662447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8022213897317465907549929 6016660422988099430662447)
      ·
        refine ⟨9024990634482149145993671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016660422988099430662447 9024990634482149145993671)
        ·
          refine ⟨13537485951723223718990507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9024990634482149145993671 13537485951723223718990507)
          ·
            refine ⟨20306228927584835578485761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13537485951723223718990507 20306228927584835578485761)
            ·
              refine ⟨15229671695688626683864321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20306228927584835578485761 15229671695688626683864321)
              ·
                refine ⟨11422253771766470012898241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15229671695688626683864321 11422253771766470012898241)
                ·
                  refine ⟨8566690328824852509673681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11422253771766470012898241 8566690328824852509673681)
                  ·
                    refine ⟨6425017746618639382255261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8566690328824852509673681 6425017746618639382255261)
                    ·
                      refine ⟨2409381654981989768345723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425017746618639382255261 2409381654981989768345723)
                      ·
                        rfl

theorem cell23_4692254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4692254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692254 prefixEnd_4692254 := by exact prefixLift 4692254
  have htrace : WordTrace (prefixWord ++ tailWord_4692254) baseStart_4692254 baseEnd_4692254 := by
    simpa [prefixWord, tailWord_4692254, baseEnd_4692254] using wordTrace_append hprefix tailTrace_4692254
  have hstable : (prefixWord ++ tailWord_4692254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692254).length < 2 ^ (prefixWord ++ tailWord_4692254).sum := by decide
  have hdescent : baseEnd_4692254 < baseStart_4692254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692261 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_4692261 : Nat := 118140960795 + 4692261 * 2 ^ 59
def prefixEnd_4692261 : Nat := 4983230072969 + 3 ^ 40 * 4692261 * 2
def baseEnd_4692261 : Nat := 803128416448857080319397

theorem tailTrace_4692261 : CollatzResearch.WordTrace tailWord_4692261 prefixEnd_4692261 803128416448857080319397 := by
  unfold tailWord_4692261
  simp only [CollatzResearch.WordTrace]
  refine ⟨171140818453747246223236637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114093878969164830815491091 171140818453747246223236637)
  ·
    refine ⟨64177806920155217333713739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171140818453747246223236637 64177806920155217333713739)
    ·
      refine ⟨96266710380232826000570609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64177806920155217333713739 96266710380232826000570609)
      ·
        refine ⟨72200032785174619500427957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96266710380232826000570609 72200032785174619500427957)
        ·
          refine ⟨6768753073610120578165121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72200032785174619500427957 6768753073610120578165121)
          ·
            refine ⟨5076564805207590433623841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6768753073610120578165121 5076564805207590433623841)
            ·
              refine ⟨3807423603905692825217881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5076564805207590433623841 3807423603905692825217881)
              ·
                refine ⟨2855567702929269618913411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807423603905692825217881 2855567702929269618913411)
                ·
                  refine ⟨4283351554393904428370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855567702929269618913411 4283351554393904428370117)
                  ·
                    refine ⟨803128416448857080319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283351554393904428370117 803128416448857080319397)
                    ·
                      rfl

theorem cell23_4692261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_4692261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692261 prefixEnd_4692261 := by exact prefixLift 4692261
  have htrace : WordTrace (prefixWord ++ tailWord_4692261) baseStart_4692261 baseEnd_4692261 := by
    simpa [prefixWord, tailWord_4692261, baseEnd_4692261] using wordTrace_append hprefix tailTrace_4692261
  have hstable : (prefixWord ++ tailWord_4692261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692261).length < 2 ^ (prefixWord ++ tailWord_4692261).sum := by decide
  have hdescent : baseEnd_4692261 < baseStart_4692261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692300 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_4692300 : Nat := 118140960795 + 4692300 * 2 ^ 59
def prefixEnd_4692300 : Nat := 4983230072969 + 3 ^ 40 * 4692300 * 2
def baseEnd_4692300 : Nat := 803135091697365529456837

theorem tailTrace_4692300 : CollatzResearch.WordTrace tailWord_4692300 prefixEnd_4692300 803135091697365529456837 := by
  unfold tailWord_4692300
  simp only [CollatzResearch.WordTrace]
  refine ⟨85571120450302977941953177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114094827267070637255937569 85571120450302977941953177)
  ·
    refine ⟨64178340337727233456464883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85571120450302977941953177 64178340337727233456464883)
    ·
      refine ⟨96267510506590850184697325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64178340337727233456464883 96267510506590850184697325)
      ·
        refine ⟨36100316439971568819261497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96267510506590850184697325 36100316439971568819261497)
        ·
          refine ⟨27075237329978676614446123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36100316439971568819261497 27075237329978676614446123)
          ·
            refine ⟨40612855994968014921669185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27075237329978676614446123 40612855994968014921669185)
            ·
              refine ⟨30459641996226011191251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40612855994968014921669185 30459641996226011191251889)
              ·
                refine ⟨22844731497169508393438917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30459641996226011191251889 22844731497169508393438917)
                ·
                  refine ⟨4283387155719282823769797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22844731497169508393438917 4283387155719282823769797)
                  ·
                    refine ⟨803135091697365529456837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283387155719282823769797 803135091697365529456837)
                    ·
                      rfl

theorem cell23_4692300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_4692300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692300 prefixEnd_4692300 := by exact prefixLift 4692300
  have htrace : WordTrace (prefixWord ++ tailWord_4692300) baseStart_4692300 baseEnd_4692300 := by
    simpa [prefixWord, tailWord_4692300, baseEnd_4692300] using wordTrace_append hprefix tailTrace_4692300
  have hstable : (prefixWord ++ tailWord_4692300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692300).length < 2 ^ (prefixWord ++ tailWord_4692300).sum := by decide
  have hdescent : baseEnd_4692300 < baseStart_4692300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692303 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4]
def baseStart_4692303 : Nat := 118140960795 + 4692303 * 2 ^ 59
def prefixEnd_4692303 : Nat := 4983230072969 + 3 ^ 40 * 4692303 * 2
def baseEnd_4692303 : Nat := 2409406815534060076632997

theorem tailTrace_4692303 : CollatzResearch.WordTrace tailWord_4692303 prefixEnd_4692303 2409406815534060076632997 := by
  unfold tailWord_4692303
  simp only [CollatzResearch.WordTrace]
  refine ⟨171142350319595087396265563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114094900213063391597510375 171142350319595087396265563)
  ·
    refine ⟨256713525479392631094398345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171142350319595087396265563 256713525479392631094398345)
    ·
      refine ⟨192535144109544473320798759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256713525479392631094398345 192535144109544473320798759)
      ·
        refine ⟨288802716164316709981198139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192535144109544473320798759 288802716164316709981198139)
        ·
          refine ⟨433204074246475064971797209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288802716164316709981198139 433204074246475064971797209)
          ·
            refine ⟨324903055684856298728847907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433204074246475064971797209 324903055684856298728847907)
            ·
              refine ⟨487354583527284448093271861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324903055684856298728847907 487354583527284448093271861)
              ·
                refine ⟨45689492205682917008744237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 487354583527284448093271861 45689492205682917008744237)
                ·
                  refine ⟨17133559577131093878279089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45689492205682917008744237 17133559577131093878279089)
                  ·
                    refine ⟨12850169682848320408709317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17133559577131093878279089 12850169682848320408709317)
                    ·
                      refine ⟨2409406815534060076632997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12850169682848320408709317 2409406815534060076632997)
                      ·
                        rfl

theorem cell23_4692303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_4692303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692303 prefixEnd_4692303 := by exact prefixLift 4692303
  have htrace : WordTrace (prefixWord ++ tailWord_4692303) baseStart_4692303 baseEnd_4692303 := by
    simpa [prefixWord, tailWord_4692303, baseEnd_4692303] using wordTrace_append hprefix tailTrace_4692303
  have hstable : (prefixWord ++ tailWord_4692303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692303).length < 2 ^ (prefixWord ++ tailWord_4692303).sum := by decide
  have hdescent : baseEnd_4692303 < baseStart_4692303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692324 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_4692324 : Nat := 118140960795 + 4692324 * 2 ^ 59
def prefixEnd_4692324 : Nat := 4983230072969 + 3 ^ 40 * 4692324 * 2
def baseEnd_4692324 : Nat := 2409417598627804494470401

theorem tailTrace_4692324 : CollatzResearch.WordTrace tailWord_4692324 prefixEnd_4692324 2409417598627804494470401 := by
  unfold tailWord_4692324
  simp only [CollatzResearch.WordTrace]
  refine ⟨85571558126259503991390013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114095410835012671988520017 85571558126259503991390013)
  ·
    refine ⟨32089334297347313996771255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85571558126259503991390013 32089334297347313996771255)
    ·
      refine ⟨48134001446020970995156883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32089334297347313996771255 48134001446020970995156883)
      ·
        refine ⟨72201002169031456492735325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48134001446020970995156883 72201002169031456492735325)
        ·
          refine ⟨27075375813386796184775747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72201002169031456492735325 27075375813386796184775747)
          ·
            refine ⟨40613063720080194277163621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27075375813386796184775747 40613063720080194277163621)
            ·
              refine ⟨7614949447515036426968179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40613063720080194277163621 7614949447515036426968179)
              ·
                refine ⟨11422424171272554640452269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7614949447515036426968179 11422424171272554640452269)
                ·
                  refine ⟨4283409064227207990169601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11422424171272554640452269 4283409064227207990169601)
                  ·
                    refine ⟨3212556798170405992627201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283409064227207990169601 3212556798170405992627201)
                    ·
                      refine ⟨2409417598627804494470401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212556798170405992627201 2409417598627804494470401)
                      ·
                        rfl

theorem cell23_4692324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_4692324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692324 prefixEnd_4692324 := by exact prefixLift 4692324
  have htrace : WordTrace (prefixWord ++ tailWord_4692324) baseStart_4692324 baseEnd_4692324 := by
    simpa [prefixWord, tailWord_4692324, baseEnd_4692324] using wordTrace_append hprefix tailTrace_4692324
  have hstable : (prefixWord ++ tailWord_4692324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692324).length < 2 ^ (prefixWord ++ tailWord_4692324).sum := by decide
  have hdescent : baseEnd_4692324 < baseStart_4692324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692391 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4692391 : Nat := 118140960795 + 4692391 * 2 ^ 59
def prefixEnd_4692391 : Nat := 4983230072969 + 3 ^ 40 * 4692391 * 2
def baseEnd_4692391 : Nat := 2409452001831655732332593

theorem tailTrace_4692391 : CollatzResearch.WordTrace tailWord_4692391 prefixEnd_4692391 2409452001831655732332593 := by
  unfold tailWord_4692391
  simp only [CollatzResearch.WordTrace]
  refine ⟨171145559943276278425469027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114097039962184185616979351 171145559943276278425469027)
  ·
    refine ⟨256718339914914417638203541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171145559943276278425469027 256718339914914417638203541)
    ·
      refine ⟨12033672183511613326790791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 256718339914914417638203541 12033672183511613326790791)
      ·
        refine ⟨18050508275267419990186187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12033672183511613326790791 18050508275267419990186187)
        ·
          refine ⟨27075762412901129985279281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18050508275267419990186187 27075762412901129985279281)
          ·
            refine ⟨20306821809675847488959461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27075762412901129985279281 20306821809675847488959461)
            ·
              refine ⟨3807529089314221404179899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20306821809675847488959461 3807529089314221404179899)
              ·
                refine ⟨5711293633971332106269849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3807529089314221404179899 5711293633971332106269849)
                ·
                  refine ⟨4283470225478499079702387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711293633971332106269849 4283470225478499079702387)
                  ·
                    refine ⟨6425205338217748619553581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283470225478499079702387 6425205338217748619553581)
                    ·
                      refine ⟨2409452001831655732332593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425205338217748619553581 2409452001831655732332593)
                      ·
                        rfl

theorem cell23_4692391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4692391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692391 prefixEnd_4692391 := by exact prefixLift 4692391
  have htrace : WordTrace (prefixWord ++ tailWord_4692391) baseStart_4692391 baseEnd_4692391 := by
    simpa [prefixWord, tailWord_4692391, baseEnd_4692391] using wordTrace_append hprefix tailTrace_4692391
  have hstable : (prefixWord ++ tailWord_4692391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692391).length < 2 ^ (prefixWord ++ tailWord_4692391).sum := by decide
  have hdescent : baseEnd_4692391 < baseStart_4692391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692393 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_4692393 : Nat := 118140960795 + 4692393 * 2 ^ 59
def prefixEnd_4692393 : Nat := 4983230072969 + 3 ^ 40 * 4692393 * 2
def baseEnd_4692393 : Nat := 2409453028792964724507583

theorem tailTrace_4692393 : CollatzResearch.WordTrace tailWord_4692393 prefixEnd_4692393 2409453028792964724507583 := by
  unfold tailWord_4692393
  simp only [CollatzResearch.WordTrace]
  refine ⟨171145632889269032767041833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114097088592846021844694555 171145632889269032767041833)
  ·
    refine ⟨128359224666951774575281375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171145632889269032767041833 128359224666951774575281375)
    ·
      refine ⟨192538837000427661862922063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128359224666951774575281375 192538837000427661862922063)
      ·
        refine ⟨288808255500641492794383095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192538837000427661862922063 288808255500641492794383095)
        ·
          refine ⟨433212383250962239191574643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288808255500641492794383095 433212383250962239191574643)
          ·
            refine ⟨649818574876443358787361965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433212383250962239191574643 649818574876443358787361965)
            ·
              refine ⟨243681965578666259545260737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649818574876443358787361965 243681965578666259545260737)
              ·
                refine ⟨182761474183999694658945553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243681965578666259545260737 182761474183999694658945553)
                ·
                  refine ⟨137071105637999770994209165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182761474183999694658945553 137071105637999770994209165)
                  ·
                    refine ⟨51401664614249914122828437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137071105637999770994209165 51401664614249914122828437)
                    ·
                      refine ⟨2409453028792964724507583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51401664614249914122828437 2409453028792964724507583)
                      ·
                        rfl

theorem cell23_4692393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_4692393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692393 prefixEnd_4692393 := by exact prefixLift 4692393
  have htrace : WordTrace (prefixWord ++ tailWord_4692393) baseStart_4692393 baseEnd_4692393 := by
    simpa [prefixWord, tailWord_4692393, baseEnd_4692393] using wordTrace_append hprefix tailTrace_4692393
  have hstable : (prefixWord ++ tailWord_4692393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692393).length < 2 ^ (prefixWord ++ tailWord_4692393).sum := by decide
  have hdescent : baseEnd_4692393 < baseStart_4692393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692401 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4692401 : Nat := 118140960795 + 4692401 * 2 ^ 59
def prefixEnd_4692401 : Nat := 4983230072969 + 3 ^ 40 * 4692401 * 2
def baseEnd_4692401 : Nat := 2409457136638200693207547

theorem tailTrace_4692401 : CollatzResearch.WordTrace tailWord_4692401 prefixEnd_4692401 2409457136638200693207547 := by
  unfold tailWord_4692401
  simp only [CollatzResearch.WordTrace]
  refine ⟨171145924673240050133333057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114097283115493366755555371 171145924673240050133333057)
  ·
    refine ⟨128359443504930037599999793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171145924673240050133333057 128359443504930037599999793)
    ·
      refine ⟨96269582628697528199999845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128359443504930037599999793 96269582628697528199999845)
      ·
        refine ⟨18050546742880786537499971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96269582628697528199999845 18050546742880786537499971)
        ·
          refine ⟨27075820114321179806249957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18050546742880786537499971 27075820114321179806249957)
          ·
            refine ⟨5076716271435221213671867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27075820114321179806249957 5076716271435221213671867)
            ·
              refine ⟨7615074407152831820507801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076716271435221213671867 7615074407152831820507801)
              ·
                refine ⟨5711305805364623865380851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7615074407152831820507801 5711305805364623865380851)
                ·
                  refine ⟨8566958708046935798071277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5711305805364623865380851 8566958708046935798071277)
                  ·
                    refine ⟨3212609515517600924276729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8566958708046935798071277 3212609515517600924276729)
                    ·
                      refine ⟨2409457136638200693207547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212609515517600924276729 2409457136638200693207547)
                      ·
                        rfl

theorem cell23_4692401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4692401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692401 prefixEnd_4692401 := by exact prefixLift 4692401
  have htrace : WordTrace (prefixWord ++ tailWord_4692401) baseStart_4692401 baseEnd_4692401 := by
    simpa [prefixWord, tailWord_4692401, baseEnd_4692401] using wordTrace_append hprefix tailTrace_4692401
  have hstable : (prefixWord ++ tailWord_4692401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692401).length < 2 ^ (prefixWord ++ tailWord_4692401).sum := by decide
  have hdescent : baseEnd_4692401 < baseStart_4692401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692414 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_4692414 : Nat := 118140960795 + 4692414 * 2 ^ 59
def prefixEnd_4692414 : Nat := 4983230072969 + 3 ^ 40 * 4692414 * 2
def baseEnd_4692414 : Nat := 2409463811886709142344987

theorem tailTrace_4692414 : CollatzResearch.WordTrace tailWord_4692414 prefixEnd_4692414 2409463811886709142344987 := by
  unfold tailWord_4692414
  simp only [CollatzResearch.WordTrace]
  refine ⟨21393299852774119169194537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114097599214795302235704197 21393299852774119169194537)
  ·
    refine ⟨16044974889580589376895903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21393299852774119169194537 16044974889580589376895903)
    ·
      refine ⟨24067462334370884065343855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16044974889580589376895903 24067462334370884065343855)
      ·
        refine ⟨36101193501556326098015783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067462334370884065343855 36101193501556326098015783)
        ·
          refine ⟨54151790252334489147023675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36101193501556326098015783 54151790252334489147023675)
          ·
            refine ⟨81227685378501733720535513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54151790252334489147023675 81227685378501733720535513)
            ·
              refine ⟨60920764033876300290401635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81227685378501733720535513 60920764033876300290401635)
              ·
                refine ⟨91381146050814450435602453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60920764033876300290401635 91381146050814450435602453)
                ·
                  refine ⟨4283491221131927364168865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91381146050814450435602453 4283491221131927364168865)
                  ·
                    refine ⟨3212618415848945523126649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283491221131927364168865 3212618415848945523126649)
                    ·
                      refine ⟨2409463811886709142344987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212618415848945523126649 2409463811886709142344987)
                      ·
                        rfl

theorem cell23_4692414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_4692414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692414 prefixEnd_4692414 := by exact prefixLift 4692414
  have htrace : WordTrace (prefixWord ++ tailWord_4692414) baseStart_4692414 baseEnd_4692414 := by
    simpa [prefixWord, tailWord_4692414, baseEnd_4692414] using wordTrace_append hprefix tailTrace_4692414
  have hstable : (prefixWord ++ tailWord_4692414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692414).length < 2 ^ (prefixWord ++ tailWord_4692414).sum := by decide
  have hdescent : baseEnd_4692414 < baseStart_4692414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692447 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3]
def baseStart_4692447 : Nat := 118140960795 + 4692447 * 2 ^ 59
def prefixEnd_4692447 : Nat := 4983230072969 + 3 ^ 40 * 4692447 * 2
def baseEnd_4692447 : Nat := 2409480756748307513232335

theorem tailTrace_4692447 : CollatzResearch.WordTrace tailWord_4692447 prefixEnd_4692447 2409480756748307513232335 := by
  unfold tailWord_4692447
  simp only [CollatzResearch.WordTrace]
  refine ⟨171147602431073399989507595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114098401620715599993005063 171147602431073399989507595)
  ·
    refine ⟨256721403646610099984261393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171147602431073399989507595 256721403646610099984261393)
    ·
      refine ⟨192541052734957574988196045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256721403646610099984261393 192541052734957574988196045)
      ·
        refine ⟨72202894775609090620573517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192541052734957574988196045 72202894775609090620573517)
        ·
          refine ⟨27076085540853408982715069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72202894775609090620573517 27076085540853408982715069)
          ·
            refine ⟨10153532077820028368518151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27076085540853408982715069 10153532077820028368518151)
            ·
              refine ⟨15230298116730042552777227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10153532077820028368518151 15230298116730042552777227)
              ·
                refine ⟨22845447175095063829165841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15230298116730042552777227 22845447175095063829165841)
                ·
                  refine ⟨17134085381321297871874381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22845447175095063829165841 17134085381321297871874381)
                  ·
                    refine ⟨6425282017995486701952893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17134085381321297871874381 6425282017995486701952893)
                    ·
                      refine ⟨2409480756748307513232335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425282017995486701952893 2409480756748307513232335)
                      ·
                        rfl

theorem cell23_4692447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_4692447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692447 prefixEnd_4692447 := by exact prefixLift 4692447
  have htrace : WordTrace (prefixWord ++ tailWord_4692447) baseStart_4692447 baseEnd_4692447 := by
    simpa [prefixWord, tailWord_4692447, baseEnd_4692447] using wordTrace_append hprefix tailTrace_4692447
  have hstable : (prefixWord ++ tailWord_4692447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692447).length < 2 ^ (prefixWord ++ tailWord_4692447).sum := by decide
  have hdescent : baseEnd_4692447 < baseStart_4692447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692482 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4692482 : Nat := 118140960795 + 4692482 * 2 ^ 59
def prefixEnd_4692482 : Nat := 4983230072969 + 3 ^ 40 * 4692482 * 2
def baseEnd_4692482 : Nat := 2409498728571214876294675

theorem tailTrace_4692482 : CollatzResearch.WordTrace tailWord_4692482 prefixEnd_4692482 2409498728571214876294675 := by
  unfold tailWord_4692482
  simp only [CollatzResearch.WordTrace]
  refine ⟨42787219746486650241757925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114099252657297733978021133 42787219746486650241757925)
  ·
    refine ⟨8022603702466246920329611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42787219746486650241757925 8022603702466246920329611)
    ·
      refine ⟨12033905553699370380494417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8022603702466246920329611 12033905553699370380494417)
      ·
        refine ⟨9025429165274527785370813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12033905553699370380494417 9025429165274527785370813)
        ·
          refine ⟨3384535936977947919514055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9025429165274527785370813 3384535936977947919514055)
          ·
            refine ⟨5076803905466921879271083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384535936977947919514055 5076803905466921879271083)
            ·
              refine ⟨7615205858200382818906625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076803905466921879271083 7615205858200382818906625)
              ·
                refine ⟨5711404393650287114179969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7615205858200382818906625 5711404393650287114179969)
                ·
                  refine ⟨4283553295237715335634977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711404393650287114179969 4283553295237715335634977)
                  ·
                    refine ⟨3212664971428286501726233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283553295237715335634977 3212664971428286501726233)
                    ·
                      refine ⟨2409498728571214876294675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212664971428286501726233 2409498728571214876294675)
                      ·
                        rfl

theorem cell23_4692482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4692482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692482 prefixEnd_4692482 := by exact prefixLift 4692482
  have htrace : WordTrace (prefixWord ++ tailWord_4692482) baseStart_4692482 baseEnd_4692482 := by
    simpa [prefixWord, tailWord_4692482, baseEnd_4692482] using wordTrace_append hprefix tailTrace_4692482
  have hstable : (prefixWord ++ tailWord_4692482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692482).length < 2 ^ (prefixWord ++ tailWord_4692482).sum := by decide
  have hdescent : baseEnd_4692482 < baseStart_4692482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692504 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_4692504 : Nat := 118140960795 + 4692504 * 2 ^ 59
def prefixEnd_4692504 : Nat := 4983230072969 + 3 ^ 40 * 4692504 * 2
def baseEnd_4692504 : Nat := 2409510025145613790219573

theorem tailTrace_4692504 : CollatzResearch.WordTrace tailWord_4692504 prefixEnd_4692504 2409510025145613790219573 := by
  unfold tailWord_4692504
  simp only [CollatzResearch.WordTrace]
  refine ⟨85574840695933449362166283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114099787594577932482888377 85574840695933449362166283)
  ·
    refine ⟨128362261043900174043249425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85574840695933449362166283 128362261043900174043249425)
    ·
      refine ⟨96271695782925130532437069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128362261043900174043249425 96271695782925130532437069)
      ·
        refine ⟨36101885918596923949663901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96271695782925130532437069 36101885918596923949663901)
        ·
          refine ⟨13538207219473846481123963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36101885918596923949663901 13538207219473846481123963)
          ·
            refine ⟨20307310829210769721685945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13538207219473846481123963 20307310829210769721685945)
            ·
              refine ⟨15230483121908077291264459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20307310829210769721685945 15230483121908077291264459)
              ·
                refine ⟨22845724682862115936896689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15230483121908077291264459 22845724682862115936896689)
                ·
                  refine ⟨17134293512146586952672517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22845724682862115936896689 17134293512146586952672517)
                  ·
                    refine ⟨3212680033527485053626097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17134293512146586952672517 3212680033527485053626097)
                    ·
                      refine ⟨2409510025145613790219573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212680033527485053626097 2409510025145613790219573)
                      ·
                        rfl

theorem cell23_4692504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_4692504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692504 prefixEnd_4692504 := by exact prefixLift 4692504
  have htrace : WordTrace (prefixWord ++ tailWord_4692504) baseStart_4692504 baseEnd_4692504 := by
    simpa [prefixWord, tailWord_4692504, baseEnd_4692504] using wordTrace_append hprefix tailTrace_4692504
  have hstable : (prefixWord ++ tailWord_4692504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692504).length < 2 ^ (prefixWord ++ tailWord_4692504).sum := by decide
  have hdescent : baseEnd_4692504 < baseStart_4692504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692587 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 4, 4]
def baseStart_4692587 : Nat := 118140960795 + 4692587 * 2 ^ 59
def prefixEnd_4692587 : Nat := 4983230072969 + 3 ^ 40 * 4692587 * 2
def baseEnd_4692587 : Nat := 803184214679978988493897

theorem tailTrace_4692587 : CollatzResearch.WordTrace tailWord_4692587 prefixEnd_4692587 803184214679978988493897 := by
  unfold tailWord_4692587
  simp only [CollatzResearch.WordTrace]
  refine ⟨171152708650566203899604015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114101805767044135933069343 171152708650566203899604015)
  ·
    refine ⟨256729062975849305849406023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171152708650566203899604015 256729062975849305849406023)
    ·
      refine ⟨385093594463773958774109035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256729062975849305849406023 385093594463773958774109035)
      ·
        refine ⟨577640391695660938161163553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385093594463773958774109035 577640391695660938161163553)
        ·
          refine ⟨433230293771745703620872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577640391695660938161163553 433230293771745703620872665)
          ·
            refine ⟨324922720328809277715654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433230293771745703620872665 324922720328809277715654499)
            ·
              refine ⟨487384080493213916573481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324922720328809277715654499 487384080493213916573481749)
              ·
                refine ⟨22846128773119402339381957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 487384080493213916573481749 22846128773119402339381957)
                ·
                  refine ⟨4283649144959887938634117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22846128773119402339381957 4283649144959887938634117)
                  ·
                    refine ⟨803184214679978988493897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283649144959887938634117 803184214679978988493897)
                    ·
                      rfl

theorem cell23_4692587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 4].length) (baseStart_4692587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692587 prefixEnd_4692587 := by exact prefixLift 4692587
  have htrace : WordTrace (prefixWord ++ tailWord_4692587) baseStart_4692587 baseEnd_4692587 := by
    simpa [prefixWord, tailWord_4692587, baseEnd_4692587] using wordTrace_append hprefix tailTrace_4692587
  have hstable : (prefixWord ++ tailWord_4692587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692587).length < 2 ^ (prefixWord ++ tailWord_4692587).sum := by decide
  have hdescent : baseEnd_4692587 < baseStart_4692587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692604 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_4692604 : Nat := 118140960795 + 4692604 * 2 ^ 59
def prefixEnd_4692604 : Nat := 4983230072969 + 3 ^ 40 * 4692604 * 2
def baseEnd_4692604 : Nat := 803187124403687799656371

theorem tailTrace_4692604 : CollatzResearch.WordTrace tailWord_4692604 prefixEnd_4692604 803187124403687799656371 := by
  unfold tailWord_4692604
  simp only [CollatzResearch.WordTrace]
  refine ⟨85576664345752307901486433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114102219127669743868648577 85576664345752307901486433)
  ·
    refine ⟨64182498259314230926114825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85576664345752307901486433 64182498259314230926114825)
    ·
      refine ⟨48136873694485673194586119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64182498259314230926114825 48136873694485673194586119)
      ·
        refine ⟨72205310541728509791879179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48136873694485673194586119 72205310541728509791879179)
        ·
          refine ⟨108307965812592764687818769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72205310541728509791879179 108307965812592764687818769)
          ·
            refine ⟨81230974359444573515864077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108307965812592764687818769 81230974359444573515864077)
            ·
              refine ⟨30461615384791715068449029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81230974359444573515864077 30461615384791715068449029)
              ·
                refine ⟨5711552884648446575334193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30461615384791715068449029 5711552884648446575334193)
                ·
                  refine ⟨4283664663486334931500645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711552884648446575334193 4283664663486334931500645)
                  ·
                    refine ⟨803187124403687799656371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283664663486334931500645 803187124403687799656371)
                    ·
                      rfl

theorem cell23_4692604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_4692604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692604 prefixEnd_4692604 := by exact prefixLift 4692604
  have htrace : WordTrace (prefixWord ++ tailWord_4692604) baseStart_4692604 baseEnd_4692604 := by
    simpa [prefixWord, tailWord_4692604, baseEnd_4692604] using wordTrace_append hprefix tailTrace_4692604
  have hstable : (prefixWord ++ tailWord_4692604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692604).length < 2 ^ (prefixWord ++ tailWord_4692604).sum := by decide
  have hdescent : baseEnd_4692604 < baseStart_4692604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692627 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3]
def baseStart_4692627 : Nat := 118140960795 + 4692627 * 2 ^ 59
def prefixEnd_4692627 : Nat := 4983230072969 + 3 ^ 40 * 4692627 * 2
def baseEnd_4692627 : Nat := 2409573183266116808981507

theorem tailTrace_4692627 : CollatzResearch.WordTrace tailWord_4692627 prefixEnd_4692627 2409573183266116808981507 := by
  unfold tailWord_4692627
  simp only [CollatzResearch.WordTrace]
  refine ⟨171154167570421290731060135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114102778380280860487373423 171154167570421290731060135)
  ·
    refine ⟨256731251355631936096590203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171154167570421290731060135 256731251355631936096590203)
    ·
      refine ⟨385096877033447904144885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256731251355631936096590203 385096877033447904144885305)
      ·
        refine ⟨288822657775085928108663979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385096877033447904144885305 288822657775085928108663979)
        ·
          refine ⟨433233986662628892162995969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288822657775085928108663979 433233986662628892162995969)
          ·
            refine ⟨324925489996971669122246977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433233986662628892162995969 324925489996971669122246977)
            ·
              refine ⟨243694117497728751841685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324925489996971669122246977 243694117497728751841685233)
              ·
                refine ⟨182770588123296563881263925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243694117497728751841685233 182770588123296563881263925)
                ·
                  refine ⟨17134742636559052863868493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182770588123296563881263925 17134742636559052863868493)
                  ·
                    refine ⟨6425528488709644823950685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17134742636559052863868493 6425528488709644823950685)
                    ·
                      refine ⟨2409573183266116808981507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425528488709644823950685 2409573183266116808981507)
                      ·
                        rfl

theorem cell23_4692627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_4692627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692627 prefixEnd_4692627 := by exact prefixLift 4692627
  have htrace : WordTrace (prefixWord ++ tailWord_4692627) baseStart_4692627 baseEnd_4692627 := by
    simpa [prefixWord, tailWord_4692627, baseEnd_4692627] using wordTrace_append hprefix tailTrace_4692627
  have hstable : (prefixWord ++ tailWord_4692627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692627).length < 2 ^ (prefixWord ++ tailWord_4692627).sum := by decide
  have hdescent : baseEnd_4692627 < baseStart_4692627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692628 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4692628 : Nat := 118140960795 + 4692628 * 2 ^ 59
def prefixEnd_4692628 : Nat := 4983230072969 + 3 ^ 40 * 4692628 * 2
def baseEnd_4692628 : Nat := 2409573696746771305069003

theorem tailTrace_4692628 : CollatzResearch.WordTrace tailWord_4692628 prefixEnd_4692628 2409573696746771305069003 := by
  unfold tailWord_4692628
  simp only [CollatzResearch.WordTrace]
  refine ⟨85577102021708833950923269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114102802695611778601231025 85577102021708833950923269)
  ·
    refine ⟨16045706629070406365798113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85577102021708833950923269 16045706629070406365798113)
    ·
      refine ⟨12034279971802804774348585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16045706629070406365798113 12034279971802804774348585)
      ·
        refine ⟨9025709978852103580761439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12034279971802804774348585 9025709978852103580761439)
        ·
          refine ⟨13538564968278155371142159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9025709978852103580761439 13538564968278155371142159)
          ·
            refine ⟨20307847452417233056713239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13538564968278155371142159 20307847452417233056713239)
            ·
              refine ⟨30461771178625849585069859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20307847452417233056713239 30461771178625849585069859)
              ·
                refine ⟨45692656767938774377604789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30461771178625849585069859 45692656767938774377604789)
                ·
                  refine ⟨4283686571994260097900449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45692656767938774377604789 4283686571994260097900449)
                  ·
                    refine ⟨3212764928995695073425337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283686571994260097900449 3212764928995695073425337)
                    ·
                      refine ⟨2409573696746771305069003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212764928995695073425337 2409573696746771305069003)
                      ·
                        rfl

theorem cell23_4692628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4692628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692628 prefixEnd_4692628 := by exact prefixLift 4692628
  have htrace : WordTrace (prefixWord ++ tailWord_4692628) baseStart_4692628 baseEnd_4692628 := by
    simpa [prefixWord, tailWord_4692628, baseEnd_4692628] using wordTrace_append hprefix tailTrace_4692628
  have hstable : (prefixWord ++ tailWord_4692628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692628).length < 2 ^ (prefixWord ++ tailWord_4692628).sum := by decide
  have hdescent : baseEnd_4692628 < baseStart_4692628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692644 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_4692644 : Nat := 118140960795 + 4692644 * 2 ^ 59
def prefixEnd_4692644 : Nat := 4983230072969 + 3 ^ 40 * 4692644 * 2
def baseEnd_4692644 : Nat := 2409581912437243242468929

theorem tailTrace_4692644 : CollatzResearch.WordTrace tailWord_4692644 prefixEnd_4692644 2409581912437243242468929 := by
  unfold tailWord_4692644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85577393805679851317214493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114103191740906468422952657 85577393805679851317214493)
  ·
    refine ⟨32091522677129944243955435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85577393805679851317214493 32091522677129944243955435)
    ·
      refine ⟨48137284015694916365933153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32091522677129944243955435 48137284015694916365933153)
      ·
        refine ⟨36102963011771187274449865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48137284015694916365933153 36102963011771187274449865)
        ·
          refine ⟨27077222258828390455837399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36102963011771187274449865 27077222258828390455837399)
          ·
            refine ⟨40615833388242585683756099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27077222258828390455837399 40615833388242585683756099)
            ·
              refine ⟨60923750082363878525634149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40615833388242585683756099 60923750082363878525634149)
              ·
                refine ⟨11423203140443227223556403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60923750082363878525634149 11423203140443227223556403)
                ·
                  refine ⟨17134804710664840835334605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11423203140443227223556403 17134804710664840835334605)
                  ·
                    refine ⟨6425551766499315313250477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17134804710664840835334605 6425551766499315313250477)
                    ·
                      refine ⟨2409581912437243242468929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425551766499315313250477 2409581912437243242468929)
                      ·
                        rfl

theorem cell23_4692644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_4692644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692644 prefixEnd_4692644 := by exact prefixLift 4692644
  have htrace : WordTrace (prefixWord ++ tailWord_4692644) baseStart_4692644 baseEnd_4692644 := by
    simpa [prefixWord, tailWord_4692644, baseEnd_4692644] using wordTrace_append hprefix tailTrace_4692644
  have hstable : (prefixWord ++ tailWord_4692644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692644).length < 2 ^ (prefixWord ++ tailWord_4692644).sum := by decide
  have hdescent : baseEnd_4692644 < baseStart_4692644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692662 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4692662 : Nat := 118140960795 + 4692662 * 2 ^ 59
def prefixEnd_4692662 : Nat := 4983230072969 + 3 ^ 40 * 4692662 * 2
def baseEnd_4692662 : Nat := 2409591155089024172043847

theorem tailTrace_4692662 : CollatzResearch.WordTrace tailWord_4692662 prefixEnd_4692662 2409591155089024172043847 := by
  unfold tailWord_4692662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697215257830905731786515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114103629416862994472389493 10697215257830905731786515)
  ·
    refine ⟨16045822886746358597679773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10697215257830905731786515 16045822886746358597679773)
    ·
      refine ⟨6017183582529884474129915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16045822886746358597679773 6017183582529884474129915)
      ·
        refine ⟨9025775373794826711194873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017183582529884474129915 9025775373794826711194873)
        ·
          refine ⟨6769331530346120033396155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9025775373794826711194873 6769331530346120033396155)
          ·
            refine ⟨10153997295519180050094233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769331530346120033396155 10153997295519180050094233)
            ·
              refine ⟨7615497971639385037570675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10153997295519180050094233 7615497971639385037570675)
              ·
                refine ⟨11423246957459077556356013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615497971639385037570675 11423246957459077556356013)
                ·
                  refine ⟨4283717609047154083633505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11423246957459077556356013 4283717609047154083633505)
                  ·
                    refine ⟨3212788206785365562725129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283717609047154083633505 3212788206785365562725129)
                    ·
                      refine ⟨2409591155089024172043847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212788206785365562725129 2409591155089024172043847)
                      ·
                        rfl

theorem cell23_4692662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4692662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692662 prefixEnd_4692662 := by exact prefixLift 4692662
  have htrace : WordTrace (prefixWord ++ tailWord_4692662) baseStart_4692662 baseEnd_4692662 := by
    simpa [prefixWord, tailWord_4692662, baseEnd_4692662] using wordTrace_append hprefix tailTrace_4692662
  have hstable : (prefixWord ++ tailWord_4692662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692662).length < 2 ^ (prefixWord ++ tailWord_4692662).sum := by decide
  have hdescent : baseEnd_4692662 < baseStart_4692662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692685 : List Nat := [1, 6, 2, 1, 3, 1, 2, 7]
def baseStart_4692685 : Nat := 118140960795 + 4692685 * 2 ^ 59
def prefixEnd_4692685 : Nat := 4983230072969 + 3 ^ 40 * 4692685 * 2
def baseEnd_4692685 : Nat := 89244554264595466002083

theorem tailTrace_4692685 : CollatzResearch.WordTrace tailWord_4692685 prefixEnd_4692685 89244554264595466002083 := by
  unfold tailWord_4692685
  simp only [CollatzResearch.WordTrace]
  refine ⟨171156283004211166636671509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114104188669474111091114339 171156283004211166636671509)
  ·
    refine ⟨8022950765822398436093977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171156283004211166636671509 8022950765822398436093977)
    ·
      refine ⟨6017213074366798827070483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8022950765822398436093977 6017213074366798827070483)
      ·
        refine ⟨9025819611550198240605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017213074366798827070483 9025819611550198240605725)
        ·
          refine ⟨3384682354331324340227147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9025819611550198240605725 3384682354331324340227147)
          ·
            refine ⟨5077023531496986510340721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384682354331324340227147 5077023531496986510340721)
            ·
              refine ⟨3807767648622739882755541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5077023531496986510340721 3807767648622739882755541)
              ·
                refine ⟨89244554264595466002083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3807767648622739882755541 89244554264595466002083)
                ·
                  rfl

theorem cell23_4692685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 7].length) (baseStart_4692685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692685 prefixEnd_4692685 := by exact prefixLift 4692685
  have htrace : WordTrace (prefixWord ++ tailWord_4692685) baseStart_4692685 baseEnd_4692685 := by
    simpa [prefixWord, tailWord_4692685, baseEnd_4692685] using wordTrace_append hprefix tailTrace_4692685
  have hstable : (prefixWord ++ tailWord_4692685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692685).length < 2 ^ (prefixWord ++ tailWord_4692685).sum := by decide
  have hdescent : baseEnd_4692685 < baseStart_4692685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692718 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4692718 : Nat := 118140960795 + 4692718 * 2 ^ 59
def prefixEnd_4692718 : Nat := 4983230072969 + 3 ^ 40 * 4692718 * 2
def baseEnd_4692718 : Nat := 2409619910005675952943589

theorem tailTrace_4692718 : CollatzResearch.WordTrace tailWord_4692718 prefixEnd_4692718 2409619910005675952943589 := by
  unfold tailWord_4692718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21394685826636451659077851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114104991075394408848415205 21394685826636451659077851)
  ·
    refine ⟨32092028739954677488616777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21394685826636451659077851 32092028739954677488616777)
    ·
      refine ⟨24069021554966008116462583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32092028739954677488616777 24069021554966008116462583)
      ·
        refine ⟨36103532332449012174693875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24069021554966008116462583 36103532332449012174693875)
        ·
          refine ⟨54155298498673518262040813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36103532332449012174693875 54155298498673518262040813)
          ·
            refine ⟨20308236937002569348265305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54155298498673518262040813 20308236937002569348265305)
            ·
              refine ⟨15231177702751927011198979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20308236937002569348265305 15231177702751927011198979)
              ·
                refine ⟨22846766554127890516798469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15231177702751927011198979 22846766554127890516798469)
                ·
                  refine ⟨4283768728898979471899713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22846766554127890516798469 4283768728898979471899713)
                  ·
                    refine ⟨3212826546674234603924785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283768728898979471899713 3212826546674234603924785)
                    ·
                      refine ⟨2409619910005675952943589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212826546674234603924785 2409619910005675952943589)
                      ·
                        rfl

theorem cell23_4692718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4692718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692718 prefixEnd_4692718 := by exact prefixLift 4692718
  have htrace : WordTrace (prefixWord ++ tailWord_4692718) baseStart_4692718 baseEnd_4692718 := by
    simpa [prefixWord, tailWord_4692718, baseEnd_4692718] using wordTrace_append hprefix tailTrace_4692718
  have hstable : (prefixWord ++ tailWord_4692718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692718).length < 2 ^ (prefixWord ++ tailWord_4692718).sum := by decide
  have hdescent : baseEnd_4692718 < baseStart_4692718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692747 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_4692747 : Nat := 118140960795 + 4692747 * 2 ^ 59
def prefixEnd_4692747 : Nat := 4983230072969 + 3 ^ 40 * 4692747 * 2
def baseEnd_4692747 : Nat := 2409634800944656339480955

theorem tailTrace_4692747 : CollatzResearch.WordTrace tailWord_4692747 prefixEnd_4692747 2409634800944656339480955 := by
  unfold tailWord_4692747
  simp only [CollatzResearch.WordTrace]
  refine ⟨171158544329986551225428495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114105696219991034150285663 171158544329986551225428495)
  ·
    refine ⟨256737816494979826838142743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171158544329986551225428495 256737816494979826838142743)
    ·
      refine ⟨385106724742469740257214115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256737816494979826838142743 385106724742469740257214115)
      ·
        refine ⟨577660087113704610385821173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385106724742469740257214115 577660087113704610385821173)
        ·
          refine ⟨54155633166909807223670735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 577660087113704610385821173 54155633166909807223670735)
          ·
            refine ⟨81233449750364710835506103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54155633166909807223670735 81233449750364710835506103)
            ·
              refine ⟨121850174625547066253259155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81233449750364710835506103 121850174625547066253259155)
              ·
                refine ⟨182775261938320599379888733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121850174625547066253259155 182775261938320599379888733)
                ·
                  refine ⟨68540723226870224767458275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182775261938320599379888733 68540723226870224767458275)
                  ·
                    refine ⟨102811084840305337151187413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68540723226870224767458275 102811084840305337151187413)
                    ·
                      refine ⟨2409634800944656339480955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102811084840305337151187413 2409634800944656339480955)
                      ·
                        rfl

theorem cell23_4692747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_4692747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692747 prefixEnd_4692747 := by exact prefixLift 4692747
  have htrace : WordTrace (prefixWord ++ tailWord_4692747) baseStart_4692747 baseEnd_4692747 := by
    simpa [prefixWord, tailWord_4692747, baseEnd_4692747] using wordTrace_append hprefix tailTrace_4692747
  have hstable : (prefixWord ++ tailWord_4692747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692747).length < 2 ^ (prefixWord ++ tailWord_4692747).sum := by decide
  have hdescent : baseEnd_4692747 < baseStart_4692747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692764 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4692764 : Nat := 118140960795 + 4692764 * 2 ^ 59
def prefixEnd_4692764 : Nat := 4983230072969 + 3 ^ 40 * 4692764 * 2
def baseEnd_4692764 : Nat := 2409643530115782772968377

theorem tailTrace_4692764 : CollatzResearch.WordTrace tailWord_4692764 prefixEnd_4692764 2409643530115782772968377 := by
  unfold tailWord_4692764
  simp only [CollatzResearch.WordTrace]
  refine ⟨85579582185462481564398673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114106109580616642085864897 85579582185462481564398673)
  ·
    refine ⟨64184686639096861173299005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85579582185462481564398673 64184686639096861173299005)
    ·
      refine ⟨24069257489661322939987127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64184686639096861173299005 24069257489661322939987127)
      ·
        refine ⟨36103886234491984409980691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24069257489661322939987127 36103886234491984409980691)
        ·
          refine ⟨54155829351737976614971037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36103886234491984409980691 54155829351737976614971037)
          ·
            refine ⟨20308436006901741230614139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54155829351737976614971037 20308436006901741230614139)
            ·
              refine ⟨30462654010352611845921209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20308436006901741230614139 30462654010352611845921209)
              ·
                refine ⟨22846990507764458884440907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30462654010352611845921209 22846990507764458884440907)
                ·
                  refine ⟨34270485761646688326661361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22846990507764458884440907 34270485761646688326661361)
                  ·
                    refine ⟨25702864321235016244996021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34270485761646688326661361 25702864321235016244996021)
                    ·
                      refine ⟨2409643530115782772968377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25702864321235016244996021 2409643530115782772968377)
                      ·
                        rfl

theorem cell23_4692764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4692764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692764 prefixEnd_4692764 := by exact prefixLift 4692764
  have htrace : WordTrace (prefixWord ++ tailWord_4692764) baseStart_4692764 baseEnd_4692764 := by
    simpa [prefixWord, tailWord_4692764, baseEnd_4692764] using wordTrace_append hprefix tailTrace_4692764
  have hstable : (prefixWord ++ tailWord_4692764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692764).length < 2 ^ (prefixWord ++ tailWord_4692764).sum := by decide
  have hdescent : baseEnd_4692764 < baseStart_4692764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692784 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_4692784 : Nat := 118140960795 + 4692784 * 2 ^ 59
def prefixEnd_4692784 : Nat := 4983230072969 + 3 ^ 40 * 4692784 * 2
def baseEnd_4692784 : Nat := 803217933242957564906095

theorem tailTrace_4692784 : CollatzResearch.WordTrace tailWord_4692784 prefixEnd_4692784 803217933242957564906095 := by
  unfold tailWord_4692784
  simp only [CollatzResearch.WordTrace]
  refine ⟨85579946915426253272262703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114106595887235004363016937 85579946915426253272262703)
  ·
    refine ⟨128369920373139379908394055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85579946915426253272262703 128369920373139379908394055)
    ·
      refine ⟨192554880559709069862591083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128369920373139379908394055 192554880559709069862591083)
      ·
        refine ⟨288832320839563604793886625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192554880559709069862591083 288832320839563604793886625)
        ·
          refine ⟨216624240629672703595414969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288832320839563604793886625 216624240629672703595414969)
          ·
            refine ⟨162468180472254527696561227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216624240629672703595414969 162468180472254527696561227)
            ·
              refine ⟨243702270708381791544841841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162468180472254527696561227 243702270708381791544841841)
              ·
                refine ⟨182776703031286343658631381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243702270708381791544841841 182776703031286343658631381)
                ·
                  refine ⟨4283828977295773679499173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182776703031286343658631381 4283828977295773679499173)
                  ·
                    refine ⟨803217933242957564906095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283828977295773679499173 803217933242957564906095)
                    ·
                      rfl

theorem cell23_4692784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_4692784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692784 prefixEnd_4692784 := by exact prefixLift 4692784
  have htrace : WordTrace (prefixWord ++ tailWord_4692784) baseStart_4692784 baseEnd_4692784 := by
    simpa [prefixWord, tailWord_4692784, baseEnd_4692784] using wordTrace_append hprefix tailTrace_4692784
  have hstable : (prefixWord ++ tailWord_4692784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692784).length < 2 ^ (prefixWord ++ tailWord_4692784).sum := by decide
  have hdescent : baseEnd_4692784 < baseStart_4692784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692791 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_4692791 : Nat := 118140960795 + 4692791 * 2 ^ 59
def prefixEnd_4692791 : Nat := 4983230072969 + 3 ^ 40 * 4692791 * 2
def baseEnd_4692791 : Nat := 2409657394093454167330753

theorem tailTrace_4692791 : CollatzResearch.WordTrace tailWord_4692791 prefixEnd_4692791 2409657394093454167330753 := by
  unfold tailWord_4692791
  simp only [CollatzResearch.WordTrace]
  refine ⟨171160149141827146740030227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114106766094551431160020151 171160149141827146740030227)
  ·
    refine ⟨256740223712740720110045341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171160149141827146740030227 256740223712740720110045341)
    ·
      refine ⟨96277583892277770041267003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256740223712740720110045341 96277583892277770041267003)
      ·
        refine ⟨144416375838416655061900505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96277583892277770041267003 144416375838416655061900505)
        ·
          refine ⟨108312281878812491296425379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144416375838416655061900505 108312281878812491296425379)
          ·
            refine ⟨162468422818218736944638069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108312281878812491296425379 162468422818218736944638069)
            ·
              refine ⟨15231414639208006588559819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162468422818218736944638069 15231414639208006588559819)
              ·
                refine ⟨22847121958812009882839729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15231414639208006588559819 22847121958812009882839729)
                ·
                  refine ⟨17135341469109007412129797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22847121958812009882839729 17135341469109007412129797)
                  ·
                    refine ⟨3212876525457938889774337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17135341469109007412129797 3212876525457938889774337)
                    ·
                      refine ⟨2409657394093454167330753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212876525457938889774337 2409657394093454167330753)
                      ·
                        rfl

theorem cell23_4692791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_4692791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692791 prefixEnd_4692791 := by exact prefixLift 4692791
  have htrace : WordTrace (prefixWord ++ tailWord_4692791) baseStart_4692791 baseEnd_4692791 := by
    simpa [prefixWord, tailWord_4692791, baseEnd_4692791] using wordTrace_append hprefix tailTrace_4692791
  have hstable : (prefixWord ++ tailWord_4692791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692791).length < 2 ^ (prefixWord ++ tailWord_4692791).sum := by decide
  have hdescent : baseEnd_4692791 < baseStart_4692791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692824 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_4692824 : Nat := 118140960795 + 4692824 * 2 ^ 59
def prefixEnd_4692824 : Nat := 4983230072969 + 3 ^ 40 * 4692824 * 2
def baseEnd_4692824 : Nat := 2409674338955052538218101

theorem tailTrace_4692824 : CollatzResearch.WordTrace tailWord_4692824 prefixEnd_4692824 2409674338955052538218101 := by
  unfold tailWord_4692824
  simp only [CollatzResearch.WordTrace]
  refine ⟨85580676375353796687990763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114107568500471728917321017 85580676375353796687990763)
  ·
    refine ⟨128371014563030695031986145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85580676375353796687990763 128371014563030695031986145)
    ·
      refine ⟨96278260922273021273989609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128371014563030695031986145 96278260922273021273989609)
      ·
        refine ⟨72208695691704765955492207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96278260922273021273989609 72208695691704765955492207)
        ·
          refine ⟨108313043537557148933238311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72208695691704765955492207 108313043537557148933238311)
          ·
            refine ⟨162469565306335723399857467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108313043537557148933238311 162469565306335723399857467)
            ·
              refine ⟨243704347959503585099786201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162469565306335723399857467 243704347959503585099786201)
              ·
                refine ⟨182778260969627688824839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243704347959503585099786201 182778260969627688824839651)
                ·
                  refine ⟨274167391454441533237259477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182778260969627688824839651 274167391454441533237259477)
                  ·
                    refine ⟨6425798237213473435248269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 274167391454441533237259477 6425798237213473435248269)
                    ·
                      refine ⟨2409674338955052538218101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425798237213473435248269 2409674338955052538218101)
                      ·
                        rfl

theorem cell23_4692824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_4692824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692824 prefixEnd_4692824 := by exact prefixLift 4692824
  have htrace : WordTrace (prefixWord ++ tailWord_4692824) baseStart_4692824 baseEnd_4692824 := by
    simpa [prefixWord, tailWord_4692824, baseEnd_4692824] using wordTrace_append hprefix tailTrace_4692824
  have hstable : (prefixWord ++ tailWord_4692824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692824).length < 2 ^ (prefixWord ++ tailWord_4692824).sum := by decide
  have hdescent : baseEnd_4692824 < baseStart_4692824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692851 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 5, 2]
def baseStart_4692851 : Nat := 118140960795 + 4692851 * 2 ^ 59
def prefixEnd_4692851 : Nat := 4983230072969 + 3 ^ 40 * 4692851 * 2
def baseEnd_4692851 : Nat := 2409688202932723932580477

theorem tailTrace_4692851 : CollatzResearch.WordTrace tailWord_4692851 prefixEnd_4692851 2409688202932723932580477 := by
  unfold tailWord_4692851
  simp only [CollatzResearch.WordTrace]
  refine ⟨171162337521609776987214407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114108225014406517991476271 171162337521609776987214407)
  ·
    refine ⟨256743506282414665480821611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171162337521609776987214407 256743506282414665480821611)
    ·
      refine ⟨385115259423621998221232417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256743506282414665480821611 385115259423621998221232417)
      ·
        refine ⟨288836444567716498665924313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385115259423621998221232417 288836444567716498665924313)
        ·
          refine ⟨216627333425787373999443235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288836444567716498665924313 216627333425787373999443235)
          ·
            refine ⟨324941000138681060999164853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216627333425787373999443235 324941000138681060999164853)
            ·
              refine ⟨30463218763001349468671705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324941000138681060999164853 30463218763001349468671705)
              ·
                refine ⟨22847414072251012101503779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30463218763001349468671705 22847414072251012101503779)
                ·
                  refine ⟨34271121108376518152255669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22847414072251012101503779 34271121108376518152255669)
                  ·
                    refine ⟨3212917603910298576773969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34271121108376518152255669 3212917603910298576773969)
                    ·
                      refine ⟨2409688202932723932580477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212917603910298576773969 2409688202932723932580477)
                      ·
                        rfl

theorem cell23_4692851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 5, 2].length) (baseStart_4692851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692851 prefixEnd_4692851 := by exact prefixLift 4692851
  have htrace : WordTrace (prefixWord ++ tailWord_4692851) baseStart_4692851 baseEnd_4692851 := by
    simpa [prefixWord, tailWord_4692851, baseEnd_4692851] using wordTrace_append hprefix tailTrace_4692851
  have hstable : (prefixWord ++ tailWord_4692851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692851).length < 2 ^ (prefixWord ++ tailWord_4692851).sum := by decide
  have hdescent : baseEnd_4692851 < baseStart_4692851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692861 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_4692861 : Nat := 118140960795 + 4692861 * 2 ^ 59
def prefixEnd_4692861 : Nat := 4983230072969 + 3 ^ 40 * 4692861 * 2
def baseEnd_4692861 : Nat := 803231112579756297818477

theorem tailTrace_4692861 : CollatzResearch.WordTrace tailWord_4692861 prefixEnd_4692861 803231112579756297818477 := by
  unfold tailWord_4692861
  simp only [CollatzResearch.WordTrace]
  refine ⟨171162702251573548695078437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114108468167715699130052291 171162702251573548695078437)
  ·
    refine ⟨32093006672170040380327207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171162702251573548695078437 32093006672170040380327207)
    ·
      refine ⟨48139510008255060570490811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32093006672170040380327207 48139510008255060570490811)
      ·
        refine ⟨72209265012382590855736217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48139510008255060570490811 72209265012382590855736217)
        ·
          refine ⟨54156948759286943141802163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72209265012382590855736217 54156948759286943141802163)
          ·
            refine ⟨81235423138930414712703245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54156948759286943141802163 81235423138930414712703245)
            ·
              refine ⟨30463283677098905517263717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81235423138930414712703245 30463283677098905517263717)
              ·
                refine ⟨5711865689456044784486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30463283677098905517263717 5711865689456044784486947)
                ·
                  refine ⟨8567798534184067176730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5711865689456044784486947 8567798534184067176730421)
                  ·
                    refine ⟨803231112579756297818477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8567798534184067176730421 803231112579756297818477)
                    ·
                      rfl

theorem cell23_4692861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_4692861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692861 prefixEnd_4692861 := by exact prefixLift 4692861
  have htrace : WordTrace (prefixWord ++ tailWord_4692861) baseStart_4692861 baseEnd_4692861 := by
    simpa [prefixWord, tailWord_4692861, baseEnd_4692861] using wordTrace_append hprefix tailTrace_4692861
  have hstable : (prefixWord ++ tailWord_4692861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692861).length < 2 ^ (prefixWord ++ tailWord_4692861).sum := by decide
  have hdescent : baseEnd_4692861 < baseStart_4692861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692868 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4692868 : Nat := 118140960795 + 4692868 * 2 ^ 59
def prefixEnd_4692868 : Nat := 4983230072969 + 3 ^ 40 * 4692868 * 2
def baseEnd_4692868 : Nat := 2409696932103850366067899

theorem tailTrace_4692868 : CollatzResearch.WordTrace tailWord_4692868 prefixEnd_4692868 2409696932103850366067899 := by
  unfold tailWord_4692868
  simp only [CollatzResearch.WordTrace]
  refine ⟨85581478781274094445291629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114108638375032125927055505 85581478781274094445291629)
  ·
    refine ⟨32093054542977785416984361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85581478781274094445291629 32093054542977785416984361)
    ·
      refine ⟨24069790907233339062738271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32093054542977785416984361 24069790907233339062738271)
      ·
        refine ⟨36104686360850008594107407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24069790907233339062738271 36104686360850008594107407)
        ·
          refine ⟨54157029541275012891161111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36104686360850008594107407 54157029541275012891161111)
          ·
            refine ⟨81235544311912519336741667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54157029541275012891161111 81235544311912519336741667)
            ·
              refine ⟨121853316467868779005112501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81235544311912519336741667 121853316467868779005112501)
              ·
                refine ⟨11423748418862698031729297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121853316467868779005112501 11423748418862698031729297)
                ·
                  refine ⟨8567811314147023523796973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11423748418862698031729297 8567811314147023523796973)
                  ·
                    refine ⟨3212929242805133821423865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8567811314147023523796973 3212929242805133821423865)
                    ·
                      refine ⟨2409696932103850366067899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212929242805133821423865 2409696932103850366067899)
                      ·
                        rfl

theorem cell23_4692868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4692868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692868 prefixEnd_4692868 := by exact prefixLift 4692868
  have htrace : WordTrace (prefixWord ++ tailWord_4692868) baseStart_4692868 baseEnd_4692868 := by
    simpa [prefixWord, tailWord_4692868, baseEnd_4692868] using wordTrace_append hprefix tailTrace_4692868
  have hstable : (prefixWord ++ tailWord_4692868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692868).length < 2 ^ (prefixWord ++ tailWord_4692868).sum := by decide
  have hdescent : baseEnd_4692868 < baseStart_4692868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692875 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 1, 1, 3]
def baseStart_4692875 : Nat := 118140960795 + 4692875 * 2 ^ 59
def prefixEnd_4692875 : Nat := 4983230072969 + 3 ^ 40 * 4692875 * 2
def baseEnd_4692875 : Nat := 2409700526468431838680367

theorem tailTrace_4692875 : CollatzResearch.WordTrace tailWord_4692875 prefixEnd_4692875 2409700526468431838680367 := by
  unfold tailWord_4692875
  simp only [CollatzResearch.WordTrace]
  refine ⟨171163212873522829086088079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114108808582348552724058719 171163212873522829086088079)
  ·
    refine ⟨256744819310284243629132119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171163212873522829086088079 256744819310284243629132119)
    ·
      refine ⟨385117228965426365443698179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256744819310284243629132119 385117228965426365443698179)
      ·
        refine ⟨577675843448139548165547269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385117228965426365443698179 577675843448139548165547269)
        ·
          refine ⟨108314220646526165281040113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 577675843448139548165547269 108314220646526165281040113)
          ·
            refine ⟨81235665484894623960780085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108314220646526165281040113 81235665484894623960780085)
            ·
              refine ⟨7615843639208870996323133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81235665484894623960780085 7615843639208870996323133)
              ·
                refine ⟨2855941364703326623621175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7615843639208870996323133 2855941364703326623621175)
                ·
                  refine ⟨4283912047054989935431763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855941364703326623621175 4283912047054989935431763)
                  ·
                    refine ⟨6425868070582484903147645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283912047054989935431763 6425868070582484903147645)
                    ·
                      refine ⟨2409700526468431838680367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425868070582484903147645 2409700526468431838680367)
                      ·
                        rfl

theorem cell23_4692875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 1, 3].length) (baseStart_4692875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692875 prefixEnd_4692875 := by exact prefixLift 4692875
  have htrace : WordTrace (prefixWord ++ tailWord_4692875) baseStart_4692875 baseEnd_4692875 := by
    simpa [prefixWord, tailWord_4692875, baseEnd_4692875] using wordTrace_append hprefix tailTrace_4692875
  have hstable : (prefixWord ++ tailWord_4692875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692875).length < 2 ^ (prefixWord ++ tailWord_4692875).sum := by decide
  have hdescent : baseEnd_4692875 < baseStart_4692875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692886 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4692886 : Nat := 118140960795 + 4692886 * 2 ^ 59
def prefixEnd_4692886 : Nat := 4983230072969 + 3 ^ 40 * 4692886 * 2
def baseEnd_4692886 : Nat := 803235391585210431880939

theorem tailTrace_4692886 : CollatzResearch.WordTrace tailWord_4692886 prefixEnd_4692886 803235391585210431880939 := by
  unfold tailWord_4692886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10697725879780186122796157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114109076050988651976492341 10697725879780186122796157)
  ·
    refine ⟨4011647204917569796048559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10697725879780186122796157 4011647204917569796048559)
    ·
      refine ⟨6017470807376354694072839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011647204917569796048559 6017470807376354694072839)
      ·
        refine ⟨9026206211064532041109259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017470807376354694072839 9026206211064532041109259)
        ·
          refine ⟨13539309316596798061663889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026206211064532041109259 13539309316596798061663889)
          ·
            refine ⟨10154481987447598546247917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13539309316596798061663889 10154481987447598546247917)
            ·
              refine ⟨3807930745292849454842969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10154481987447598546247917 3807930745292849454842969)
              ·
                refine ⟨2855948058969637091132227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3807930745292849454842969 2855948058969637091132227)
                ·
                  refine ⟨4283922088454455636698341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855948058969637091132227 4283922088454455636698341)
                  ·
                    refine ⟨803235391585210431880939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283922088454455636698341 803235391585210431880939)
                    ·
                      rfl

theorem cell23_4692886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4692886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692886 prefixEnd_4692886 := by exact prefixLift 4692886
  have htrace : WordTrace (prefixWord ++ tailWord_4692886) baseStart_4692886 baseEnd_4692886 := by
    simpa [prefixWord, tailWord_4692886, baseEnd_4692886] using wordTrace_append hprefix tailTrace_4692886
  have hstable : (prefixWord ++ tailWord_4692886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692886).length < 2 ^ (prefixWord ++ tailWord_4692886).sum := by decide
  have hdescent : baseEnd_4692886 < baseStart_4692886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692892 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4692892 : Nat := 118140960795 + 4692892 * 2 ^ 59
def prefixEnd_4692892 : Nat := 4983230072969 + 3 ^ 40 * 4692892 * 2
def baseEnd_4692892 : Nat := 2409709255639558272167789

theorem tailTrace_4692892 : CollatzResearch.WordTrace tailWord_4692892 prefixEnd_4692892 2409709255639558272167789 := by
  unfold tailWord_4692892
  simp only [CollatzResearch.WordTrace]
  refine ⟨85581916457230620494728465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114109221942974160659637953 85581916457230620494728465)
  ·
    refine ⟨64186437342922965371046349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85581916457230620494728465 64186437342922965371046349)
    ·
      refine ⟨24069914003596112014142381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64186437342922965371046349 24069914003596112014142381)
      ·
        refine ⟨9026217751348542005303393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24069914003596112014142381 9026217751348542005303393)
        ·
          refine ⟨6769663313511406503977545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9026217751348542005303393 6769663313511406503977545)
          ·
            refine ⟨5077247485133554877983159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769663313511406503977545 5077247485133554877983159)
            ·
              refine ⟨7615871227700332316974739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077247485133554877983159 7615871227700332316974739)
              ·
                refine ⟨11423806841550498475462109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7615871227700332316974739 11423806841550498475462109)
                ·
                  refine ⟨4283927565581436928298291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11423806841550498475462109 4283927565581436928298291)
                  ·
                    refine ⟨6425891348372155392447437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4283927565581436928298291 6425891348372155392447437)
                    ·
                      refine ⟨2409709255639558272167789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425891348372155392447437 2409709255639558272167789)
                      ·
                        rfl

theorem cell23_4692892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4692892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692892 prefixEnd_4692892 := by exact prefixLift 4692892
  have htrace : WordTrace (prefixWord ++ tailWord_4692892) baseStart_4692892 baseEnd_4692892 := by
    simpa [prefixWord, tailWord_4692892, baseEnd_4692892] using wordTrace_append hprefix tailTrace_4692892
  have hstable : (prefixWord ++ tailWord_4692892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692892).length < 2 ^ (prefixWord ++ tailWord_4692892).sum := by decide
  have hdescent : baseEnd_4692892 < baseStart_4692892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692931 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3]
def baseStart_4692931 : Nat := 118140960795 + 4692931 * 2 ^ 59
def prefixEnd_4692931 : Nat := 4983230072969 + 3 ^ 40 * 4692931 * 2
def baseEnd_4692931 : Nat := 2409729281385083619580109

theorem tailTrace_4692931 : CollatzResearch.WordTrace tailWord_4692931 prefixEnd_4692931 2409729281385083619580109 := by
  unfold tailWord_4692931
  simp only [CollatzResearch.WordTrace]
  refine ⟨171165255361319950650126647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114110170240879967100084431 171165255361319950650126647)
  ·
    refine ⟨256747883041979925975189971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171165255361319950650126647 256747883041979925975189971)
    ·
      refine ⟨385121824562969888962784957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256747883041979925975189971 385121824562969888962784957)
      ·
        refine ⟨144420684211113708361044359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385121824562969888962784957 144420684211113708361044359)
        ·
          refine ⟨216631026316670562541566539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144420684211113708361044359 216631026316670562541566539)
          ·
            refine ⟨324946539475005843812349809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216631026316670562541566539 324946539475005843812349809)
            ·
              refine ⟨243709904606254382859262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324946539475005843812349809 243709904606254382859262357)
              ·
                refine ⟨11423901778418174196527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243709904606254382859262357 11423901778418174196527923)
                ·
                  refine ⟨17135852667627261294791885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11423901778418174196527923 17135852667627261294791885)
                  ·
                    refine ⟨6425944750360222985546957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17135852667627261294791885 6425944750360222985546957)
                    ·
                      refine ⟨2409729281385083619580109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6425944750360222985546957 2409729281385083619580109)
                      ·
                        rfl

theorem cell23_4692931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_4692931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692931 prefixEnd_4692931 := by exact prefixLift 4692931
  have htrace : WordTrace (prefixWord ++ tailWord_4692931) baseStart_4692931 baseEnd_4692931 := by
    simpa [prefixWord, tailWord_4692931, baseEnd_4692931] using wordTrace_append hprefix tailTrace_4692931
  have hstable : (prefixWord ++ tailWord_4692931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692931).length < 2 ^ (prefixWord ++ tailWord_4692931).sum := by decide
  have hdescent : baseEnd_4692931 < baseStart_4692931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4692949 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4692949 : Nat := 118140960795 + 4692949 * 2 ^ 59
def prefixEnd_4692949 : Nat := 4983230072969 + 3 ^ 40 * 4692949 * 2
def baseEnd_4692949 : Nat := 2409738524036864549155027

theorem tailTrace_4692949 : CollatzResearch.WordTrace tailWord_4692949 prefixEnd_4692949 2409738524036864549155027 := by
  unfold tailWord_4692949
  simp only [CollatzResearch.WordTrace]
  refine ⟨171165911875254739724281901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114110607916836493149521267 171165911875254739724281901)
  ·
    refine ⟨64187216953220527396605713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171165911875254739724281901 64187216953220527396605713)
    ·
      refine ⟨48140412714915395547454285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64187216953220527396605713 48140412714915395547454285)
      ·
        refine ⟨18052654768093273330295357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48140412714915395547454285 18052654768093273330295357)
        ·
          refine ⟨6769745538034977498860759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18052654768093273330295357 6769745538034977498860759)
          ·
            refine ⟨10154618307052466248291139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6769745538034977498860759 10154618307052466248291139)
            ·
              refine ⟨15231927460578699372436709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10154618307052466248291139 15231927460578699372436709)
              ·
                refine ⟨2855986398858506132331883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15231927460578699372436709 2855986398858506132331883)
                ·
                  refine ⟨4283979598287759198497825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855986398858506132331883 4283979598287759198497825)
                  ·
                    refine ⟨3212984698715819398873369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4283979598287759198497825 3212984698715819398873369)
                    ·
                      refine ⟨2409738524036864549155027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3212984698715819398873369 2409738524036864549155027)
                      ·
                        rfl

theorem cell23_4692949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4692949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4692949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4692949 prefixEnd_4692949 := by exact prefixLift 4692949
  have htrace : WordTrace (prefixWord ++ tailWord_4692949) baseStart_4692949 baseEnd_4692949 := by
    simpa [prefixWord, tailWord_4692949, baseEnd_4692949] using wordTrace_append hprefix tailTrace_4692949
  have hstable : (prefixWord ++ tailWord_4692949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4692949).length < 2 ^ (prefixWord ++ tailWord_4692949).sum := by decide
  have hdescent : baseEnd_4692949 < baseStart_4692949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4692949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693028 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 7]
def baseStart_4693028 : Nat := 118140960795 + 4693028 * 2 ^ 59
def prefixEnd_4693028 : Nat := 4983230072969 + 3 ^ 40 * 4693028 * 2
def baseEnd_4693028 : Nat := 267753232112063304451907

theorem tailTrace_4693028 : CollatzResearch.WordTrace tailWord_4693028 prefixEnd_4693028 267753232112063304451907 := by
  unfold tailWord_4693028
  simp only [CollatzResearch.WordTrace]
  refine ⟨85584396620984268108203869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114112528827979024144271825 85584396620984268108203869)
  ·
    refine ⟨32094148732869100540576451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85584396620984268108203869 32094148732869100540576451)
    ·
      refine ⟨48141223099303650810864677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32094148732869100540576451 48141223099303650810864677)
      ·
        refine ⟨9026479331119434527037127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48141223099303650810864677 9026479331119434527037127)
        ·
          refine ⟨13539718996679151790555691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026479331119434527037127 13539718996679151790555691)
          ·
            refine ⟨20309578495018727685833537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13539718996679151790555691 20309578495018727685833537)
            ·
              refine ⟨15232183871264045764375153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20309578495018727685833537 15232183871264045764375153)
              ·
                refine ⟨11424137903448034323281365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15232183871264045764375153 11424137903448034323281365)
                ·
                  refine ⟨267753232112063304451907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11424137903448034323281365 267753232112063304451907)
                  ·
                    rfl

theorem cell23_4693028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_4693028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693028 prefixEnd_4693028 := by exact prefixLift 4693028
  have htrace : WordTrace (prefixWord ++ tailWord_4693028) baseStart_4693028 baseEnd_4693028 := by
    simpa [prefixWord, tailWord_4693028, baseEnd_4693028] using wordTrace_append hprefix tailTrace_4693028
  have hstable : (prefixWord ++ tailWord_4693028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693028).length < 2 ^ (prefixWord ++ tailWord_4693028).sum := by decide
  have hdescent : baseEnd_4693028 < baseStart_4693028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693041 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_4693041 : Nat := 118140960795 + 4693041 * 2 ^ 59
def prefixEnd_4693041 : Nat := 4983230072969 + 3 ^ 40 * 4693041 * 2
def baseEnd_4693041 : Nat := 803261921419026063068201

theorem tailTrace_4693041 : CollatzResearch.WordTrace tailWord_4693041 prefixEnd_4693041 803261921419026063068201 := by
  unfold tailWord_4693041
  simp only [CollatzResearch.WordTrace]
  refine ⟨171169267390921439436630977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114112844927280959624420651 171169267390921439436630977)
  ·
    refine ⟨128376950543191079577473233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171169267390921439436630977 128376950543191079577473233)
    ·
      refine ⟨96282712907393309683104925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128376950543191079577473233 96282712907393309683104925)
      ·
        refine ⟨36106017340272491131164347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96282712907393309683104925 36106017340272491131164347)
        ·
          refine ⟨54159026010408736696746521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36106017340272491131164347 54159026010408736696746521)
          ·
            refine ⟨40619269507806552522559891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54159026010408736696746521 40619269507806552522559891)
            ·
              refine ⟨60928904261709828783839837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40619269507806552522559891 60928904261709828783839837)
              ·
                refine ⟨22848339098141185793939939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60928904261709828783839837 22848339098141185793939939)
                ·
                  refine ⟨34272508647211778690909909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22848339098141185793939939 34272508647211778690909909)
                  ·
                    refine ⟨803261921419026063068201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34272508647211778690909909 803261921419026063068201)
                    ·
                      rfl

theorem cell23_4693041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_4693041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693041 prefixEnd_4693041 := by exact prefixLift 4693041
  have htrace : WordTrace (prefixWord ++ tailWord_4693041) baseStart_4693041 baseEnd_4693041 := by
    simpa [prefixWord, tailWord_4693041, baseEnd_4693041] using wordTrace_append hprefix tailTrace_4693041
  have hstable : (prefixWord ++ tailWord_4693041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693041).length < 2 ^ (prefixWord ++ tailWord_4693041).sum := by decide
  have hdescent : baseEnd_4693041 < baseStart_4693041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693062 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_4693062 : Nat := 118140960795 + 4693062 * 2 ^ 59
def prefixEnd_4693062 : Nat := 4983230072969 + 3 ^ 40 * 4693062 * 2
def baseEnd_4693062 : Nat := 267755171927869178560223

theorem tailTrace_4693062 : CollatzResearch.WordTrace tailWord_4693062 prefixEnd_4693062 267755171927869178560223 := by
  unfold tailWord_4693062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349063541370167500723295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114113355549230240015430293 5349063541370167500723295)
  ·
    refine ⟨8023595312055251251084943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5349063541370167500723295 8023595312055251251084943)
    ·
      refine ⟨12035392968082876876627415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8023595312055251251084943 12035392968082876876627415)
      ·
        refine ⟨18053089452124315314941123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12035392968082876876627415 18053089452124315314941123)
        ·
          refine ⟨27079634178186472972411685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18053089452124315314941123 27079634178186472972411685)
          ·
            refine ⟨5077431408409963682327191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27079634178186472972411685 5077431408409963682327191)
            ·
              refine ⟨7616147112614945523490787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077431408409963682327191 7616147112614945523490787)
              ·
                refine ⟨11424220668922418285236181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616147112614945523490787 11424220668922418285236181)
                ·
                  refine ⟨267755171927869178560223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11424220668922418285236181 267755171927869178560223)
                  ·
                    rfl

theorem cell23_4693062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_4693062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693062 prefixEnd_4693062 := by exact prefixLift 4693062
  have htrace : WordTrace (prefixWord ++ tailWord_4693062) baseStart_4693062 baseEnd_4693062 := by
    simpa [prefixWord, tailWord_4693062, baseEnd_4693062] using wordTrace_append hprefix tailTrace_4693062
  have hstable : (prefixWord ++ tailWord_4693062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693062).length < 2 ^ (prefixWord ++ tailWord_4693062).sum := by decide
  have hdescent : baseEnd_4693062 < baseStart_4693062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693088 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_4693088 : Nat := 118140960795 + 4693088 * 2 ^ 59
def prefixEnd_4693088 : Nat := 4983230072969 + 3 ^ 40 * 4693088 * 2
def baseEnd_4693088 : Nat := 803269965949279835105629

theorem tailTrace_4693088 : CollatzResearch.WordTrace tailWord_4693088 prefixEnd_4693088 803269965949279835105629 := by
  unfold tailWord_4693088
  simp only [CollatzResearch.WordTrace]
  refine ⟨85585490810875583231795959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114113987747834110975727945 85585490810875583231795959)
  ·
    refine ⟨128378236216313374847693939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85585490810875583231795959 128378236216313374847693939)
    ·
      refine ⟨192567354324470062271540909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128378236216313374847693939 192567354324470062271540909)
      ·
        refine ⟨72212757871676273351827841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192567354324470062271540909 72212757871676273351827841)
        ·
          refine ⟨54159568403757205013870881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72212757871676273351827841 54159568403757205013870881)
          ·
            refine ⟨40619676302817903760403161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54159568403757205013870881 40619676302817903760403161)
            ·
              refine ⟨30464757227113427820302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40619676302817903760403161 30464757227113427820302371)
              ·
                refine ⟨45697135840670141730453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30464757227113427820302371 45697135840670141730453557)
                ·
                  refine ⟨4284106485062825787230021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45697135840670141730453557 4284106485062825787230021)
                  ·
                    refine ⟨803269965949279835105629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284106485062825787230021 803269965949279835105629)
                    ·
                      rfl

theorem cell23_4693088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_4693088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693088 prefixEnd_4693088 := by exact prefixLift 4693088
  have htrace : WordTrace (prefixWord ++ tailWord_4693088) baseStart_4693088 baseEnd_4693088 := by
    simpa [prefixWord, tailWord_4693088, baseEnd_4693088] using wordTrace_append hprefix tailTrace_4693088
  have hstable : (prefixWord ++ tailWord_4693088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693088).length < 2 ^ (prefixWord ++ tailWord_4693088).sum := by decide
  have hdescent : baseEnd_4693088 < baseStart_4693088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693091 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4693091 : Nat := 118140960795 + 4693091 * 2 ^ 59
def prefixEnd_4693091 : Nat := 4983230072969 + 3 ^ 40 * 4693091 * 2
def baseEnd_4693091 : Nat := 2409811438289802993579373

theorem tailTrace_4693091 : CollatzResearch.WordTrace tailWord_4693091 prefixEnd_4693091 2409811438289802993579373 := by
  unfold tailWord_4693091
  simp only [CollatzResearch.WordTrace]
  refine ⟨171171091040740297975951127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114114060693826865317300751 171171091040740297975951127)
  ·
    refine ⟨256756636561110446963926691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171171091040740297975951127 256756636561110446963926691)
    ·
      refine ⟨385134954841665670445890037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256756636561110446963926691 385134954841665670445890037)
      ·
        refine ⟨36106402016406156604302191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 385134954841665670445890037 36106402016406156604302191)
        ·
          refine ⟨54159603024609234906453287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36106402016406156604302191 54159603024609234906453287)
          ·
            refine ⟨81239404536913852359679931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54159603024609234906453287 81239404536913852359679931)
            ·
              refine ⟨121859106805370778539519897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81239404536913852359679931 121859106805370778539519897)
              ·
                refine ⟨91394330104028083904639923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121859106805370778539519897 91394330104028083904639923)
                ·
                  refine ⟨137091495156042125856959885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91394330104028083904639923 137091495156042125856959885)
                  ·
                    refine ⟨51409310683515797196359957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137091495156042125856959885 51409310683515797196359957)
                    ·
                      refine ⟨2409811438289802993579373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51409310683515797196359957 2409811438289802993579373)
                      ·
                        rfl

theorem cell23_4693091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4693091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693091 prefixEnd_4693091 := by exact prefixLift 4693091
  have htrace : WordTrace (prefixWord ++ tailWord_4693091) baseStart_4693091 baseEnd_4693091 := by
    simpa [prefixWord, tailWord_4693091, baseEnd_4693091] using wordTrace_append hprefix tailTrace_4693091
  have hstable : (prefixWord ++ tailWord_4693091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693091).length < 2 ^ (prefixWord ++ tailWord_4693091).sum := by decide
  have hdescent : baseEnd_4693091 < baseStart_4693091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693095 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_4693095 : Nat := 118140960795 + 4693095 * 2 ^ 59
def prefixEnd_4693095 : Nat := 4983230072969 + 3 ^ 40 * 4693095 * 2
def baseEnd_4693095 : Nat := 2409813492212420977929355

theorem tailTrace_4693095 : CollatzResearch.WordTrace tailWord_4693095 prefixEnd_4693095 2409813492212420977929355 := by
  unfold tailWord_4693095
  simp only [CollatzResearch.WordTrace]
  refine ⟨171171236932725806659096739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114114157955150537772731159 171171236932725806659096739)
  ·
    refine ⟨256756855399088709988645109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171171236932725806659096739 256756855399088709988645109)
    ·
      refine ⟨24070955193664566561435479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256756855399088709988645109 24070955193664566561435479)
      ·
        refine ⟨36106432790496849842153219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24070955193664566561435479 36106432790496849842153219)
        ·
          refine ⟨54159649185745274763229829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36106432790496849842153219 54159649185745274763229829)
          ·
            refine ⟨10154934222327239018105593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54159649185745274763229829 10154934222327239018105593)
            ·
              refine ⟨7616200666745429263579195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10154934222327239018105593 7616200666745429263579195)
              ·
                refine ⟨11424301000118143895368793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616200666745429263579195 11424301000118143895368793)
                ·
                  refine ⟨8568225750088607921526595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11424301000118143895368793 8568225750088607921526595)
                  ·
                    refine ⟨12852338625132911882289893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8568225750088607921526595 12852338625132911882289893)
                    ·
                      refine ⟨2409813492212420977929355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12852338625132911882289893 2409813492212420977929355)
                      ·
                        rfl

theorem cell23_4693095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_4693095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693095 prefixEnd_4693095 := by exact prefixLift 4693095
  have htrace : WordTrace (prefixWord ++ tailWord_4693095) baseStart_4693095 baseEnd_4693095 := by
    simpa [prefixWord, tailWord_4693095, baseEnd_4693095] using wordTrace_append hprefix tailTrace_4693095
  have hstable : (prefixWord ++ tailWord_4693095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693095).length < 2 ^ (prefixWord ++ tailWord_4693095).sum := by decide
  have hdescent : baseEnd_4693095 < baseStart_4693095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693186 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4693186 : Nat := 118140960795 + 4693186 * 2 ^ 59
def prefixEnd_4693186 : Nat := 4983230072969 + 3 ^ 40 * 4693186 * 2
def baseEnd_4693186 : Nat := 267762246550220013543493

theorem tailTrace_4693186 : CollatzResearch.WordTrace tailWord_4693186 prefixEnd_4693186 267762246550220013543493 := by
  unfold tailWord_4693186
  simp only [CollatzResearch.WordTrace]
  refine ⟨42793638993849032300164853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114116370650264086133772941 42793638993849032300164853)
  ·
    refine ⟨4011903655673346778140455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42793638993849032300164853 4011903655673346778140455)
    ·
      refine ⟨6017855483510020167210683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011903655673346778140455 6017855483510020167210683)
      ·
        refine ⟨9026783225265030250816025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017855483510020167210683 9026783225265030250816025)
        ·
          refine ⟨6770087418948772688112019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9026783225265030250816025 6770087418948772688112019)
          ·
            refine ⟨10155131128423159032168029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770087418948772688112019 10155131128423159032168029)
            ·
              refine ⟨3808174173158684637063011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10155131128423159032168029 3808174173158684637063011)
              ·
                refine ⟨5712261259738026955594517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808174173158684637063011 5712261259738026955594517)
                ·
                  refine ⟨267762246550220013543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5712261259738026955594517 267762246550220013543493)
                  ·
                    rfl

theorem cell23_4693186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4693186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693186 prefixEnd_4693186 := by exact prefixLift 4693186
  have htrace : WordTrace (prefixWord ++ tailWord_4693186) baseStart_4693186 baseEnd_4693186 := by
    simpa [prefixWord, tailWord_4693186, baseEnd_4693186] using wordTrace_append hprefix tailTrace_4693186
  have hstable : (prefixWord ++ tailWord_4693186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693186).length < 2 ^ (prefixWord ++ tailWord_4693186).sum := by decide
  have hdescent : baseEnd_4693186 < baseStart_4693186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693202 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4693202 : Nat := 118140960795 + 4693202 * 2 ^ 59
def prefixEnd_4693202 : Nat := 4983230072969 + 3 ^ 40 * 4693202 * 2
def baseEnd_4693202 : Nat := 2409868434642452059291363

theorem tailTrace_4693202 : CollatzResearch.WordTrace tailWord_4693202 prefixEnd_4693202 2409868434642452059291363 := by
  unfold tailWord_4693202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42793784885834540983310465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114116759695558775955494573 42793784885834540983310465)
  ·
    refine ⟨32095338664375905737482849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42793784885834540983310465 32095338664375905737482849)
    ·
      refine ⟨24071503998281929303112137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32095338664375905737482849 24071503998281929303112137)
      ·
        refine ⟨18053627998711446977334103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24071503998281929303112137 18053627998711446977334103)
        ·
          refine ⟨27080441998067170466001155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18053627998711446977334103 27080441998067170466001155)
          ·
            refine ⟨40620662997100755699001733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27080441998067170466001155 40620662997100755699001733)
            ·
              refine ⟨7616374311956391693562825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40620662997100755699001733 7616374311956391693562825)
              ·
                refine ⟨5712280733967293770172119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7616374311956391693562825 5712280733967293770172119)
                ·
                  refine ⟨8568421100950940655258179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5712280733967293770172119 8568421100950940655258179)
                  ·
                    refine ⟨12852631651426410982887269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8568421100950940655258179 12852631651426410982887269)
                    ·
                      refine ⟨2409868434642452059291363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12852631651426410982887269 2409868434642452059291363)
                      ·
                        rfl

theorem cell23_4693202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4693202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693202 prefixEnd_4693202 := by exact prefixLift 4693202
  have htrace : WordTrace (prefixWord ++ tailWord_4693202) baseStart_4693202 baseEnd_4693202 := by
    simpa [prefixWord, tailWord_4693202, baseEnd_4693202] using wordTrace_append hprefix tailTrace_4693202
  have hstable : (prefixWord ++ tailWord_4693202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693202).length < 2 ^ (prefixWord ++ tailWord_4693202).sum := by decide
  have hdescent : baseEnd_4693202 < baseStart_4693202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693213 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4693213 : Nat := 118140960795 + 4693213 * 2 ^ 59
def prefixEnd_4693213 : Nat := 4983230072969 + 3 ^ 40 * 4693213 * 2
def baseEnd_4693213 : Nat := 2409874082929651516253813

theorem tailTrace_4693213 : CollatzResearch.WordTrace tailWord_4693213 prefixEnd_4693213 2409874082929651516253813 := by
  unfold tailWord_4693213
  simp only [CollatzResearch.WordTrace]
  refine ⟨171175540746298312811892293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114117027164198875207928195 171175540746298312811892293)
  ·
    refine ⟨32095413889930933652229805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171175540746298312811892293 32095413889930933652229805)
    ·
      refine ⟨12035780208724100119586177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32095413889930933652229805 12035780208724100119586177)
      ·
        refine ⟨9026835156543075089689633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12035780208724100119586177 9026835156543075089689633)
        ·
          refine ⟨6770126367407306317267225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9026835156543075089689633 6770126367407306317267225)
          ·
            refine ⟨5077594775555479737950419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770126367407306317267225 5077594775555479737950419)
            ·
              refine ⟨7616392163333219606925629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077594775555479737950419 7616392163333219606925629)
              ·
                refine ⟨2856147061249957352597111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7616392163333219606925629 2856147061249957352597111)
                ·
                  refine ⟨4284220591874936028895667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856147061249957352597111 4284220591874936028895667)
                  ·
                    refine ⟨6426330887812404043343501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4284220591874936028895667 6426330887812404043343501)
                    ·
                      refine ⟨2409874082929651516253813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6426330887812404043343501 2409874082929651516253813)
                      ·
                        rfl

theorem cell23_4693213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4693213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693213 prefixEnd_4693213 := by exact prefixLift 4693213
  have htrace : WordTrace (prefixWord ++ tailWord_4693213) baseStart_4693213 baseEnd_4693213 := by
    simpa [prefixWord, tailWord_4693213, baseEnd_4693213] using wordTrace_append hprefix tailTrace_4693213
  have hstable : (prefixWord ++ tailWord_4693213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693213).length < 2 ^ (prefixWord ++ tailWord_4693213).sum := by decide
  have hdescent : baseEnd_4693213 < baseStart_4693213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693245 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_4693245 : Nat := 118140960795 + 4693245 * 2 ^ 59
def prefixEnd_4693245 : Nat := 4983230072969 + 3 ^ 40 * 4693245 * 2
def baseEnd_4693245 : Nat := 2409890514310595391053665

theorem tailTrace_4693245 : CollatzResearch.WordTrace tailWord_4693245 prefixEnd_4693245 2409890514310595391053665 := by
  unfold tailWord_4693245
  simp only [CollatzResearch.WordTrace]
  refine ⟨171176707882182382277057189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114117805254788254851371459 171176707882182382277057189)
  ·
    refine ⟨32095632727909196676948223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171176707882182382277057189 32095632727909196676948223)
    ·
      refine ⟨48143449091863795015422335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32095632727909196676948223 48143449091863795015422335)
      ·
        refine ⟨72215173637795692523133503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48143449091863795015422335 72215173637795692523133503)
        ·
          refine ⟨108322760456693538784700255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72215173637795692523133503 108322760456693538784700255)
          ·
            refine ⟨162484140685040308177050383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108322760456693538784700255 162484140685040308177050383)
            ·
              refine ⟨243726211027560462265575575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162484140685040308177050383 243726211027560462265575575)
              ·
                refine ⟨365589316541340693398363363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243726211027560462265575575 365589316541340693398363363)
                ·
                  refine ⟨548383974812011040097545045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365589316541340693398363363 548383974812011040097545045)
                  ·
                    refine ⟨3213187352414127188071553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 548383974812011040097545045 3213187352414127188071553)
                    ·
                      refine ⟨2409890514310595391053665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213187352414127188071553 2409890514310595391053665)
                      ·
                        rfl

theorem cell23_4693245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_4693245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693245 prefixEnd_4693245 := by exact prefixLift 4693245
  have htrace : WordTrace (prefixWord ++ tailWord_4693245) baseStart_4693245 baseEnd_4693245 := by
    simpa [prefixWord, tailWord_4693245, baseEnd_4693245] using wordTrace_append hprefix tailTrace_4693245
  have hstable : (prefixWord ++ tailWord_4693245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693245).length < 2 ^ (prefixWord ++ tailWord_4693245).sum := by decide
  have hdescent : baseEnd_4693245 < baseStart_4693245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693246 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4693246 : Nat := 118140960795 + 4693246 * 2 ^ 59
def prefixEnd_4693246 : Nat := 4983230072969 + 3 ^ 40 * 4693246 * 2
def baseEnd_4693246 : Nat := 803297009263749962380387

theorem tailTrace_4693246 : CollatzResearch.WordTrace tailWord_4693246 prefixEnd_4693246 803297009263749962380387 := by
  unfold tailWord_4693246
  simp only [CollatzResearch.WordTrace]
  refine ⟨21397093044397344930980449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114117829570119172965229061 21397093044397344930980449)
  ·
    refine ⟨16047819783298008698235337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21397093044397344930980449 16047819783298008698235337)
    ·
      refine ⟨12035864837473506523676503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16047819783298008698235337 12035864837473506523676503)
      ·
        refine ⟨18053797256210259785514755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12035864837473506523676503 18053797256210259785514755)
        ·
          refine ⟨27080695884315389678272133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18053797256210259785514755 27080695884315389678272133)
          ·
            refine ⟨5077630478309135564676025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27080695884315389678272133 5077630478309135564676025)
            ·
              refine ⟨3808222858731851673507019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5077630478309135564676025 3808222858731851673507019)
              ·
                refine ⟨5712334288097777510260529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808222858731851673507019 5712334288097777510260529)
                ·
                  refine ⟨4284250716073333132695397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5712334288097777510260529 4284250716073333132695397)
                  ·
                    refine ⟨803297009263749962380387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284250716073333132695397 803297009263749962380387)
                    ·
                      rfl

theorem cell23_4693246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4693246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693246 prefixEnd_4693246 := by exact prefixLift 4693246
  have htrace : WordTrace (prefixWord ++ tailWord_4693246) baseStart_4693246 baseEnd_4693246 := by
    simpa [prefixWord, tailWord_4693246, baseEnd_4693246] using wordTrace_append hprefix tailTrace_4693246
  have hstable : (prefixWord ++ tailWord_4693246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693246).length < 2 ^ (prefixWord ++ tailWord_4693246).sum := by decide
  have hdescent : baseEnd_4693246 < baseStart_4693246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693256 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_4693256 : Nat := 118140960795 + 4693256 * 2 ^ 59
def prefixEnd_4693256 : Nat := 4983230072969 + 3 ^ 40 * 4693256 * 2
def baseEnd_4693256 : Nat := 2409896162597794848016115

theorem tailTrace_4693256 : CollatzResearch.WordTrace tailWord_4693256 prefixEnd_4693256 2409896162597794848016115 := by
  unfold tailWord_4693256
  simp only [CollatzResearch.WordTrace]
  refine ⟨85588554542571265577853811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114118072723428354103805081 85588554542571265577853811)
  ·
    refine ⟨128382831813856898366780717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85588554542571265577853811 128382831813856898366780717)
    ·
      refine ⟨48143561930196336887542769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128382831813856898366780717 48143561930196336887542769)
      ·
        refine ⟨36107671447647252665657077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48143561930196336887542769 36107671447647252665657077)
        ·
          refine ⟨3385094198216929937405351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36107671447647252665657077 3385094198216929937405351)
          ·
            refine ⟨5077641297325394906108027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385094198216929937405351 5077641297325394906108027)
            ·
              refine ⟨7616461945988092359162041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077641297325394906108027 7616461945988092359162041)
              ·
                refine ⟨5712346459491069269371531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7616461945988092359162041 5712346459491069269371531)
                ·
                  refine ⟨8568519689236603904057297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5712346459491069269371531 8568519689236603904057297)
                  ·
                    refine ⟨6426389766927452928042973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8568519689236603904057297 6426389766927452928042973)
                    ·
                      refine ⟨2409896162597794848016115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6426389766927452928042973 2409896162597794848016115)
                      ·
                        rfl

theorem cell23_4693256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_4693256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693256 prefixEnd_4693256 := by exact prefixLift 4693256
  have htrace : WordTrace (prefixWord ++ tailWord_4693256) baseStart_4693256 baseEnd_4693256 := by
    simpa [prefixWord, tailWord_4693256, baseEnd_4693256] using wordTrace_append hprefix tailTrace_4693256
  have hstable : (prefixWord ++ tailWord_4693256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693256).length < 2 ^ (prefixWord ++ tailWord_4693256).sum := by decide
  have hdescent : baseEnd_4693256 < baseStart_4693256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693258 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4693258 : Nat := 118140960795 + 4693258 * 2 ^ 59
def prefixEnd_4693258 : Nat := 4983230072969 + 3 ^ 40 * 4693258 * 2
def baseEnd_4693258 : Nat := 2409897189559103840191105

theorem tailTrace_4693258 : CollatzResearch.WordTrace tailWord_4693258 prefixEnd_4693258 2409897189559103840191105 := by
  unfold tailWord_4693258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42794295507783821374320107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114118121354090190331520285 42794295507783821374320107)
  ·
    refine ⟨64191443261675732061480161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42794295507783821374320107 64191443261675732061480161)
    ·
      refine ⟨48143582446256799046110121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64191443261675732061480161 48143582446256799046110121)
      ·
        refine ⟨36107686834692599284582591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48143582446256799046110121 36107686834692599284582591)
        ·
          refine ⟨54161530252038898926873887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36107686834692599284582591 54161530252038898926873887)
          ·
            refine ⟨81242295378058348390310831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54161530252038898926873887 81242295378058348390310831)
            ·
              refine ⟨121863443067087522585466247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81242295378058348390310831 121863443067087522585466247)
              ·
                refine ⟨182795164600631283878199371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121863443067087522585466247 182795164600631283878199371)
                ·
                  refine ⟨274192746900946925817299057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182795164600631283878199371 274192746900946925817299057)
                  ·
                    refine ⟨205644560175710194362974293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 274192746900946925817299057 205644560175710194362974293)
                    ·
                      refine ⟨2409897189559103840191105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205644560175710194362974293 2409897189559103840191105)
                      ·
                        rfl

theorem cell23_4693258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4693258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693258 prefixEnd_4693258 := by exact prefixLift 4693258
  have htrace : WordTrace (prefixWord ++ tailWord_4693258) baseStart_4693258 baseEnd_4693258 := by
    simpa [prefixWord, tailWord_4693258, baseEnd_4693258] using wordTrace_append hprefix tailTrace_4693258
  have hstable : (prefixWord ++ tailWord_4693258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693258).length < 2 ^ (prefixWord ++ tailWord_4693258).sum := by decide
  have hdescent : baseEnd_4693258 < baseStart_4693258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693345 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_4693345 : Nat := 118140960795 + 4693345 * 2 ^ 59
def prefixEnd_4693345 : Nat := 4983230072969 + 3 ^ 40 * 4693345 * 2
def baseEnd_4693345 : Nat := 803313954125348333267735

theorem tailTrace_4693345 : CollatzResearch.WordTrace tailWord_4693345 prefixEnd_4693345 803313954125348333267735 := by
  unfold tailWord_4693345
  simp only [CollatzResearch.WordTrace]
  refine ⟨171180355181820099355697489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114120236787880066237131659 171180355181820099355697489)
  ·
    refine ⟨128385266386365074516773117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171180355181820099355697489 128385266386365074516773117)
    ·
      refine ⟨48144474894886902943789919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128385266386365074516773117 48144474894886902943789919)
      ·
        refine ⟨72216712342330354415684879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48144474894886902943789919 72216712342330354415684879)
        ·
          refine ⟨108325068513495531623527319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72216712342330354415684879 108325068513495531623527319)
          ·
            refine ⟨162487602770243297435290979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108325068513495531623527319 162487602770243297435290979)
            ·
              refine ⟨243731404155364946152936469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162487602770243297435290979 243731404155364946152936469)
              ·
                refine ⟨11424909569782731850918897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 243731404155364946152936469 11424909569782731850918897)
                ·
                  refine ⟨8568682177337048888189173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11424909569782731850918897 8568682177337048888189173)
                  ·
                    refine ⟨803313954125348333267735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8568682177337048888189173 803313954125348333267735)
                    ·
                      rfl

theorem cell23_4693345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_4693345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693345 prefixEnd_4693345 := by exact prefixLift 4693345
  have htrace : WordTrace (prefixWord ++ tailWord_4693345) baseStart_4693345 baseEnd_4693345 := by
    simpa [prefixWord, tailWord_4693345, baseEnd_4693345] using wordTrace_append hprefix tailTrace_4693345
  have hstable : (prefixWord ++ tailWord_4693345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693345).length < 2 ^ (prefixWord ++ tailWord_4693345).sum := by decide
  have hdescent : baseEnd_4693345 < baseStart_4693345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693436 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4693436 : Nat := 118140960795 + 4693436 * 2 ^ 59
def prefixEnd_4693436 : Nat := 4983230072969 + 3 ^ 40 * 4693436 * 2
def baseEnd_4693436 : Nat := 2409988589115604143765287

theorem tailTrace_4693436 : CollatzResearch.WordTrace tailWord_4693436 prefixEnd_4693436 2409988589115604143765287 := by
  unfold tailWord_4693436
  simp only [CollatzResearch.WordTrace]
  refine ⟨85591837112245210948630081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114122449482993614598173441 85591837112245210948630081)
  ·
    refine ⟨64193877834183908211472561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85591837112245210948630081 64193877834183908211472561)
    ·
      refine ⟨48145408375637931158604421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64193877834183908211472561 48145408375637931158604421)
      ·
        refine ⟨9027264070432112092238329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48145408375637931158604421 9027264070432112092238329)
        ·
          refine ⟨6770448052824084069178747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027264070432112092238329 6770448052824084069178747)
          ·
            refine ⟨10155672079236126103768121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770448052824084069178747 10155672079236126103768121)
            ·
              refine ⟨7616754059427094577826091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10155672079236126103768121 7616754059427094577826091)
              ·
                refine ⟨11425131089140641866739137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616754059427094577826091 11425131089140641866739137)
                ·
                  refine ⟨8568848316855481400054353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11425131089140641866739137 8568848316855481400054353)
                  ·
                    refine ⟨6426636237641611050040765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8568848316855481400054353 6426636237641611050040765)
                    ·
                      refine ⟨2409988589115604143765287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6426636237641611050040765 2409988589115604143765287)
                      ·
                        rfl

theorem cell23_4693436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4693436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693436 prefixEnd_4693436 := by exact prefixLift 4693436
  have htrace : WordTrace (prefixWord ++ tailWord_4693436) baseStart_4693436 baseEnd_4693436 := by
    simpa [prefixWord, tailWord_4693436, baseEnd_4693436] using wordTrace_append hprefix tailTrace_4693436
  have hstable : (prefixWord ++ tailWord_4693436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693436).length < 2 ^ (prefixWord ++ tailWord_4693436).sum := by decide
  have hdescent : baseEnd_4693436 < baseStart_4693436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693460 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_4693460 : Nat := 118140960795 + 4693460 * 2 ^ 59
def prefixEnd_4693460 : Nat := 4983230072969 + 3 ^ 40 * 4693460 * 2
def baseEnd_4693460 : Nat := 803333637550437349955059

theorem tailTrace_4693460 : CollatzResearch.WordTrace tailWord_4693460 prefixEnd_4693460 803333637550437349955059 := by
  unfold tailWord_4693460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85592274788201736998066917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114123033050935649330755889 85592274788201736998066917)
  ·
    refine ⟨16048551522787825687137547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85592274788201736998066917 16048551522787825687137547)
    ·
      refine ⟨24072827284181738530706321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16048551522787825687137547 24072827284181738530706321)
      ·
        refine ⟨18054620463136303898029741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24072827284181738530706321 18054620463136303898029741)
        ·
          refine ⟨6770482673676113961761153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18054620463136303898029741 6770482673676113961761153)
          ·
            refine ⟨5077862005257085471320865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770482673676113961761153 5077862005257085471320865)
            ·
              refine ⟨3808396503942814103490649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5077862005257085471320865 3808396503942814103490649)
              ·
                refine ⟨2856297377957110577617987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3808396503942814103490649 2856297377957110577617987)
                ·
                  refine ⟨4284446066935665866426981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856297377957110577617987 4284446066935665866426981)
                  ·
                    refine ⟨803333637550437349955059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284446066935665866426981 803333637550437349955059)
                    ·
                      rfl

theorem cell23_4693460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_4693460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693460 prefixEnd_4693460 := by exact prefixLift 4693460
  have htrace : WordTrace (prefixWord ++ tailWord_4693460) baseStart_4693460 baseEnd_4693460 := by
    simpa [prefixWord, tailWord_4693460, baseEnd_4693460] using wordTrace_append hprefix tailTrace_4693460
  have hstable : (prefixWord ++ tailWord_4693460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693460).length < 2 ^ (prefixWord ++ tailWord_4693460).sum := by decide
  have hdescent : baseEnd_4693460 < baseStart_4693460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693493 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4693493 : Nat := 118140960795 + 4693493 * 2 ^ 59
def prefixEnd_4693493 : Nat := 4983230072969 + 3 ^ 40 * 4693493 * 2
def baseEnd_4693493 : Nat := 2410017857512910420752525

theorem tailTrace_4693493 : CollatzResearch.WordTrace tailWord_4693493 prefixEnd_4693493 2410017857512910420752525 := by
  unfold tailWord_4693493
  simp only [CollatzResearch.WordTrace]
  refine ⟨171185753185283920632085133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114123835456855947088056755 171185753185283920632085133)
  ·
    refine ⟨64194657444481470237031925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171185753185283920632085133 64194657444481470237031925)
    ·
      refine ⟨6018249135420137834721743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64194657444481470237031925 6018249135420137834721743)
      ·
        refine ⟨9027373703130206752082615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018249135420137834721743 9027373703130206752082615)
        ·
          refine ⟨13541060554695310128123923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027373703130206752082615 13541060554695310128123923)
          ·
            refine ⟨20311590832042965192185885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13541060554695310128123923 20311590832042965192185885)
            ·
              refine ⟨7616846562016111947069707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20311590832042965192185885 7616846562016111947069707)
              ·
                refine ⟨11425269843024167920604561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616846562016111947069707 11425269843024167920604561)
                ·
                  refine ⟨8568952382268125940453421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11425269843024167920604561 8568952382268125940453421)
                  ·
                    refine ⟨3213357143350547227670033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8568952382268125940453421 3213357143350547227670033)
                    ·
                      refine ⟨2410017857512910420752525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213357143350547227670033 2410017857512910420752525)
                      ·
                        rfl

theorem cell23_4693493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4693493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693493 prefixEnd_4693493 := by exact prefixLift 4693493
  have htrace : WordTrace (prefixWord ++ tailWord_4693493) baseStart_4693493 baseEnd_4693493 := by
    simpa [prefixWord, tailWord_4693493, baseEnd_4693493] using wordTrace_append hprefix tailTrace_4693493
  have hstable : (prefixWord ++ tailWord_4693493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693493).length < 2 ^ (prefixWord ++ tailWord_4693493).sum := by decide
  have hdescent : baseEnd_4693493 < baseStart_4693493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693523 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 1, 2, 2]
def baseStart_4693523 : Nat := 118140960795 + 4693523 * 2 ^ 59
def prefixEnd_4693523 : Nat := 4983230072969 + 3 ^ 40 * 4693523 * 2
def baseEnd_4693523 : Nat := 2410033261932545303377387

theorem tailTrace_4693523 : CollatzResearch.WordTrace tailWord_4693523 prefixEnd_4693523 2410033261932545303377387 := by
  unfold tailWord_4693523
  simp only [CollatzResearch.WordTrace]
  refine ⟨171186847375175235755677223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114124564916783490503784815 171186847375175235755677223)
  ·
    refine ⟨256780271062762853633515835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171186847375175235755677223 256780271062762853633515835)
    ·
      refine ⟨385170406594144280450273753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256780271062762853633515835 385170406594144280450273753)
      ·
        refine ⟨288877804945608210337705315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385170406594144280450273753 288877804945608210337705315)
        ·
          refine ⟨433316707418412315506557973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288877804945608210337705315 433316707418412315506557973)
          ·
            refine ⟨20311720660238077289369905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 433316707418412315506557973 20311720660238077289369905)
            ·
              refine ⟨15233790495178557967027429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20311720660238077289369905 15233790495178557967027429)
              ·
                refine ⟨2856335717845979618817643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15233790495178557967027429 2856335717845979618817643)
                ·
                  refine ⟨4284503576768969428226465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856335717845979618817643 4284503576768969428226465)
                  ·
                    refine ⟨3213377682576727071169849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284503576768969428226465 3213377682576727071169849)
                    ·
                      refine ⟨2410033261932545303377387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213377682576727071169849 2410033261932545303377387)
                      ·
                        rfl

theorem cell23_4693523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 2, 2].length) (baseStart_4693523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693523 prefixEnd_4693523 := by exact prefixLift 4693523
  have htrace : WordTrace (prefixWord ++ tailWord_4693523) baseStart_4693523 baseEnd_4693523 := by
    simpa [prefixWord, tailWord_4693523, baseEnd_4693523] using wordTrace_append hprefix tailTrace_4693523
  have hstable : (prefixWord ++ tailWord_4693523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693523).length < 2 ^ (prefixWord ++ tailWord_4693523).sum := by decide
  have hdescent : baseEnd_4693523 < baseStart_4693523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693536 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4693536 : Nat := 118140960795 + 4693536 * 2 ^ 59
def prefixEnd_4693536 : Nat := 4983230072969 + 3 ^ 40 * 4693536 * 2
def baseEnd_4693536 : Nat := 2410039937181053752514827

theorem tailTrace_4693536 : CollatzResearch.WordTrace tailWord_4693536 prefixEnd_4693536 2410039937181053752514827 := by
  unfold tailWord_4693536
  simp only [CollatzResearch.WordTrace]
  refine ⟨85593660762064069487950231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114124881016085425983933641 85593660762064069487950231)
  ·
    refine ⟨128390491143096104231925347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85593660762064069487950231 128390491143096104231925347)
    ·
      refine ⟨192585736714644156347888021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128390491143096104231925347 192585736714644156347888021)
      ·
        refine ⟨9027456408498944828807251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192585736714644156347888021 9027456408498944828807251)
        ·
          refine ⟨13541184612748417243210877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027456408498944828807251 13541184612748417243210877)
          ·
            refine ⟨5077944229780656466204079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13541184612748417243210877 5077944229780656466204079)
            ·
              refine ⟨7616916344670984699306119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077944229780656466204079 7616916344670984699306119)
              ·
                refine ⟨11425374517006477048959179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616916344670984699306119 11425374517006477048959179)
                ·
                  refine ⟨17138061775509715573438769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11425374517006477048959179 17138061775509715573438769)
                  ·
                    refine ⟨12853546331632286680079077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17138061775509715573438769 12853546331632286680079077)
                    ·
                      refine ⟨2410039937181053752514827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12853546331632286680079077 2410039937181053752514827)
                      ·
                        rfl

theorem cell23_4693536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4693536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693536 prefixEnd_4693536 := by exact prefixLift 4693536
  have htrace : WordTrace (prefixWord ++ tailWord_4693536) baseStart_4693536 baseEnd_4693536 := by
    simpa [prefixWord, tailWord_4693536, baseEnd_4693536] using wordTrace_append hprefix tailTrace_4693536
  have hstable : (prefixWord ++ tailWord_4693536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693536).length < 2 ^ (prefixWord ++ tailWord_4693536).sum := by decide
  have hdescent : baseEnd_4693536 < baseStart_4693536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693574 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_4693574 : Nat := 118140960795 + 4693574 * 2 ^ 59
def prefixEnd_4693574 : Nat := 4983230072969 + 3 ^ 40 * 4693574 * 2
def baseEnd_4693574 : Nat := 2410059449445924603839653

theorem tailTrace_4693574 : CollatzResearch.WordTrace tailWord_4693574 prefixEnd_4693574 2410059449445924603839653 := by
  unfold tailWord_4693574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349647109312202233305743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114125804998660314310522517 5349647109312202233305743)
  ·
    refine ⟨8024470663968303349958615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5349647109312202233305743 8024470663968303349958615)
    ·
      refine ⟨12036705995952455024937923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8024470663968303349958615 12036705995952455024937923)
      ·
        refine ⟨18055058993928682537406885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12036705995952455024937923 18055058993928682537406885)
        ·
          refine ⟨3385323561361627975763791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18055058993928682537406885 3385323561361627975763791)
          ·
            refine ⟨5077985342042441963645687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385323561361627975763791 5077985342042441963645687)
            ·
              refine ⟨7616978013063662945468531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077985342042441963645687 7616978013063662945468531)
              ·
                refine ⟨11425467019595494418202797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7616978013063662945468531 11425467019595494418202797)
                ·
                  refine ⟨4284550132348310406826049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11425467019595494418202797 4284550132348310406826049)
                  ·
                    refine ⟨3213412599261232805119537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284550132348310406826049 3213412599261232805119537)
                    ·
                      refine ⟨2410059449445924603839653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213412599261232805119537 2410059449445924603839653)
                      ·
                        rfl

theorem cell23_4693574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_4693574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693574 prefixEnd_4693574 := by exact prefixLift 4693574
  have htrace : WordTrace (prefixWord ++ tailWord_4693574) baseStart_4693574 baseEnd_4693574 := by
    simpa [prefixWord, tailWord_4693574, baseEnd_4693574] using wordTrace_append hprefix tailTrace_4693574
  have hstable : (prefixWord ++ tailWord_4693574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693574).length < 2 ^ (prefixWord ++ tailWord_4693574).sum := by decide
  have hdescent : baseEnd_4693574 < baseStart_4693574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693582 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4693582 : Nat := 118140960795 + 4693582 * 2 ^ 59
def prefixEnd_4693582 : Nat := 4983230072969 + 3 ^ 40 * 4693582 * 2
def baseEnd_4693582 : Nat := 2410063557291160572539615

theorem tailTrace_4693582 : CollatzResearch.WordTrace tailWord_4693582 prefixEnd_4693582 2410063557291160572539615 := by
  unfold tailWord_4693582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21398624910245186104009375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114125999521307659221383333 21398624910245186104009375)
  ·
    refine ⟨32097937365367779156014063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21398624910245186104009375 32097937365367779156014063)
    ·
      refine ⟨48146906048051668734021095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32097937365367779156014063 48146906048051668734021095)
      ·
        refine ⟨72220359072077503101031643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48146906048051668734021095 72220359072077503101031643)
        ·
          refine ⟨108330538608116254651547465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72220359072077503101031643 108330538608116254651547465)
          ·
            refine ⟨81247903956087190988660599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108330538608116254651547465 81247903956087190988660599)
            ·
              refine ⟨121871855934130786482990899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81247903956087190988660599 121871855934130786482990899)
              ·
                refine ⟨182807783901196179724486349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121871855934130786482990899 182807783901196179724486349)
                ·
                  refine ⟨68552918962948567396682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182807783901196179724486349 68552918962948567396682381)
                  ·
                    refine ⟨25707344611105712773755893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68552918962948567396682381 25707344611105712773755893)
                    ·
                      refine ⟨2410063557291160572539615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25707344611105712773755893 2410063557291160572539615)
                      ·
                        rfl

theorem cell23_4693582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4693582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693582 prefixEnd_4693582 := by exact prefixLift 4693582
  have htrace : WordTrace (prefixWord ++ tailWord_4693582) baseStart_4693582 baseEnd_4693582 := by
    simpa [prefixWord, tailWord_4693582, baseEnd_4693582] using wordTrace_append hprefix tailTrace_4693582
  have hstable : (prefixWord ++ tailWord_4693582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693582).length < 2 ^ (prefixWord ++ tailWord_4693582).sum := by decide
  have hdescent : baseEnd_4693582 < baseStart_4693582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693592 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4693592 : Nat := 118140960795 + 4693592 * 2 ^ 59
def prefixEnd_4693592 : Nat := 4983230072969 + 3 ^ 40 * 4693592 * 2
def baseEnd_4693592 : Nat := 2410068692097705533414569

theorem tailTrace_4693592 : CollatzResearch.WordTrace tailWord_4693592 prefixEnd_4693592 2410068692097705533414569 := by
  unfold tailWord_4693592
  simp only [CollatzResearch.WordTrace]
  refine ⟨85594682005962630269969515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114126242674616840359959353 85594682005962630269969515)
  ·
    refine ⟨128392023008943945404954273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85594682005962630269969515 128392023008943945404954273)
    ·
      refine ⟨96294017256707959053715705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128392023008943945404954273 96294017256707959053715705)
      ·
        refine ⟨72220512942530969290286779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96294017256707959053715705 72220512942530969290286779)
        ·
          refine ⟨108330769413796453935430169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72220512942530969290286779 108330769413796453935430169)
          ·
            refine ⟨81248077060347340451572627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108330769413796453935430169 81248077060347340451572627)
            ·
              refine ⟨121872115590521010677358941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81248077060347340451572627 121872115590521010677358941)
              ·
                refine ⟨45702043346445379004009603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121872115590521010677358941 45702043346445379004009603)
                ·
                  refine ⟨68553065019668068506014405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45702043346445379004009603 68553065019668068506014405)
                  ·
                    refine ⟨12853699691187762844877701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68553065019668068506014405 12853699691187762844877701)
                    ·
                      refine ⟨2410068692097705533414569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12853699691187762844877701 2410068692097705533414569)
                      ·
                        rfl

theorem cell23_4693592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4693592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693592 prefixEnd_4693592 := by exact prefixLift 4693592
  have htrace : WordTrace (prefixWord ++ tailWord_4693592) baseStart_4693592 baseEnd_4693592 := by
    simpa [prefixWord, tailWord_4693592, baseEnd_4693592] using wordTrace_append hprefix tailTrace_4693592
  have hstable : (prefixWord ++ tailWord_4693592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693592).length < 2 ^ (prefixWord ++ tailWord_4693592).sum := by decide
  have hdescent : baseEnd_4693592 < baseStart_4693592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693613 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_4693613 : Nat := 118140960795 + 4693613 * 2 ^ 59
def prefixEnd_4693613 : Nat := 4983230072969 + 3 ^ 40 * 4693613 * 2
def baseEnd_4693613 : Nat := 2410079475191449951251973

theorem tailTrace_4693613 : CollatzResearch.WordTrace tailWord_4693613 prefixEnd_4693613 2410079475191449951251973 := by
  unfold tailWord_4693613
  simp only [CollatzResearch.WordTrace]
  refine ⟨171190129944849181126453493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114126753296566120750968995 171190129944849181126453493)
  ·
    refine ⟨16049074682329610730605015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171190129944849181126453493 16049074682329610730605015)
    ·
      refine ⟨24073612023494416095907523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049074682329610730605015 24073612023494416095907523)
      ·
        refine ⟨36110418035241624143861285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24073612023494416095907523 36110418035241624143861285)
        ·
          refine ⟨6770703381607804526973991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36110418035241624143861285 6770703381607804526973991)
          ·
            refine ⟨10156055072411706790460987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770703381607804526973991 10156055072411706790460987)
            ·
              refine ⟨15234082608617560185691481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156055072411706790460987 15234082608617560185691481)
              ·
                refine ⟨11425561956463170139268611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15234082608617560185691481 11425561956463170139268611)
                ·
                  refine ⟨17138342934694755208902917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11425561956463170139268611 17138342934694755208902917)
                  ·
                    refine ⟨3213439300255266601669297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17138342934694755208902917 3213439300255266601669297)
                    ·
                      refine ⟨2410079475191449951251973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213439300255266601669297 2410079475191449951251973)
                      ·
                        rfl

theorem cell23_4693613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_4693613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693613 prefixEnd_4693613 := by exact prefixLift 4693613
  have htrace : WordTrace (prefixWord ++ tailWord_4693613) baseStart_4693613 baseEnd_4693613 := by
    simpa [prefixWord, tailWord_4693613, baseEnd_4693613] using wordTrace_append hprefix tailTrace_4693613
  have hstable : (prefixWord ++ tailWord_4693613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693613).length < 2 ^ (prefixWord ++ tailWord_4693613).sum := by decide
  have hdescent : baseEnd_4693613 < baseStart_4693613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693646 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4693646 : Nat := 118140960795 + 4693646 * 2 ^ 59
def prefixEnd_4693646 : Nat := 4983230072969 + 3 ^ 40 * 4693646 * 2
def baseEnd_4693646 : Nat := 2410096420053048322139321

theorem tailTrace_4693646 : CollatzResearch.WordTrace tailWord_4693646 prefixEnd_4693646 2410096420053048322139321 := by
  unfold tailWord_4693646
  simp only [CollatzResearch.WordTrace]
  refine ⟨21398916694216203470300599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114127555702486418508269861 21398916694216203470300599)
  ·
    refine ⟨32098375041324305205450899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21398916694216203470300599 32098375041324305205450899)
    ·
      refine ⟨48147562561986457808176349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32098375041324305205450899 48147562561986457808176349)
      ·
        refine ⟨18055335960744921678066131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48147562561986457808176349 18055335960744921678066131)
        ·
          refine ⟨27083003941117382517099197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18055335960744921678066131 27083003941117382517099197)
          ·
            refine ⟨10156126477919018443912199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27083003941117382517099197 10156126477919018443912199)
            ·
              refine ⟨15234189716878527665868299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156126477919018443912199 15234189716878527665868299)
              ·
                refine ⟨22851284575317791498802449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15234189716878527665868299 22851284575317791498802449)
                ·
                  refine ⟨17138463431488343624101837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22851284575317791498802449 17138463431488343624101837)
                  ·
                    refine ⟨6426923786808128859038189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17138463431488343624101837 6426923786808128859038189)
                    ·
                      refine ⟨2410096420053048322139321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6426923786808128859038189 2410096420053048322139321)
                      ·
                        rfl

theorem cell23_4693646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4693646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693646 prefixEnd_4693646 := by exact prefixLift 4693646
  have htrace : WordTrace (prefixWord ++ tailWord_4693646) baseStart_4693646 baseEnd_4693646 := by
    simpa [prefixWord, tailWord_4693646, baseEnd_4693646] using wordTrace_append hprefix tailTrace_4693646
  have hstable : (prefixWord ++ tailWord_4693646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693646).length < 2 ^ (prefixWord ++ tailWord_4693646).sum := by decide
  have hdescent : baseEnd_4693646 < baseStart_4693646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693679 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 5, 4]
def baseStart_4693679 : Nat := 118140960795 + 4693679 * 2 ^ 59
def prefixEnd_4693679 : Nat := 4983230072969 + 3 ^ 40 * 4693679 * 2
def baseEnd_4693679 : Nat := 803371121638215564342223

theorem tailTrace_4693679 : CollatzResearch.WordTrace tailWord_4693679 prefixEnd_4693679 803371121638215564342223 := by
  unfold tailWord_4693679
  simp only [CollatzResearch.WordTrace]
  refine ⟨171192537162610074398356091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114128358108406716265570727 171192537162610074398356091)
  ·
    refine ⟨256788805743915111597534137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171192537162610074398356091 256788805743915111597534137)
    ·
      refine ⟨192591604307936333698150603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256788805743915111597534137 192591604307936333698150603)
      ·
        refine ⟨288887406461904500547225905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192591604307936333698150603 288887406461904500547225905)
        ·
          refine ⟨216665554846428375410419429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288887406461904500547225905 216665554846428375410419429)
          ·
            refine ⟨40624791533705320389453643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216665554846428375410419429 40624791533705320389453643)
            ·
              refine ⟨60937187300557980584180465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40624791533705320389453643 60937187300557980584180465)
              ·
                refine ⟨45702890475418485438135349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60937187300557980584180465 45702890475418485438135349)
                ·
                  refine ⟨4284645982070483009825189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45702890475418485438135349 4284645982070483009825189)
                  ·
                    refine ⟨803371121638215564342223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284645982070483009825189 803371121638215564342223)
                    ·
                      rfl

theorem cell23_4693679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_4693679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693679 prefixEnd_4693679 := by exact prefixLift 4693679
  have htrace : WordTrace (prefixWord ++ tailWord_4693679) baseStart_4693679 baseEnd_4693679 := by
    simpa [prefixWord, tailWord_4693679, baseEnd_4693679] using wordTrace_append hprefix tailTrace_4693679
  have hstable : (prefixWord ++ tailWord_4693679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693679).length < 2 ^ (prefixWord ++ tailWord_4693679).sum := by decide
  have hdescent : baseEnd_4693679 < baseStart_4693679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693696 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_4693696 : Nat := 118140960795 + 4693696 * 2 ^ 59
def prefixEnd_4693696 : Nat := 4983230072969 + 3 ^ 40 * 4693696 * 2
def baseEnd_4693696 : Nat := 803374031361924375504697

theorem tailTrace_4693696 : CollatzResearch.WordTrace tailWord_4693696 prefixEnd_4693696 803374031361924375504697 := by
  unfold tailWord_4693696
  simp only [CollatzResearch.WordTrace]
  refine ⟨85596578601774243150862471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114128771469032324201149961 85596578601774243150862471)
  ·
    refine ⟨128394867902661364726293707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85596578601774243150862471 128394867902661364726293707)
    ·
      refine ⟨192592301853992047089440561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128394867902661364726293707 192592301853992047089440561)
      ·
        refine ⟨144444226390494035317080421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192592301853992047089440561 144444226390494035317080421)
        ·
          refine ⟨27083292448217631621952579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144444226390494035317080421 27083292448217631621952579)
          ·
            refine ⟨40624938672326447432928869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27083292448217631621952579 40624938672326447432928869)
            ·
              refine ⟨7617176001061208893674163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40624938672326447432928869 7617176001061208893674163)
              ·
                refine ⟨11425764001591813340511245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617176001061208893674163 11425764001591813340511245)
                ·
                  refine ⟨4284661500596930002691717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11425764001591813340511245 4284661500596930002691717)
                  ·
                    refine ⟨803374031361924375504697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284661500596930002691717 803374031361924375504697)
                    ·
                      rfl

theorem cell23_4693696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_4693696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693696 prefixEnd_4693696 := by exact prefixLift 4693696
  have htrace : WordTrace (prefixWord ++ tailWord_4693696) baseStart_4693696 baseEnd_4693696 := by
    simpa [prefixWord, tailWord_4693696, baseEnd_4693696] using wordTrace_append hprefix tailTrace_4693696
  have hstable : (prefixWord ++ tailWord_4693696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693696).length < 2 ^ (prefixWord ++ tailWord_4693696).sum := by decide
  have hdescent : baseEnd_4693696 < baseStart_4693696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693719 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_4693719 : Nat := 118140960795 + 4693719 * 2 ^ 59
def prefixEnd_4693719 : Nat := 4983230072969 + 3 ^ 40 * 4693719 * 2
def baseEnd_4693719 : Nat := 2410133904140826536526485

theorem tailTrace_4693719 : CollatzResearch.WordTrace tailWord_4693719 prefixEnd_4693719 2410133904140826536526485 := by
  unfold tailWord_4693719
  simp only [CollatzResearch.WordTrace]
  refine ⟨171193996082465161229812211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114129330721643440819874807 171193996082465161229812211)
  ·
    refine ⟨256790994123697741844718317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171193996082465161229812211 256790994123697741844718317)
    ·
      refine ⟨96296622796386653191769369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256790994123697741844718317 96296622796386653191769369)
      ·
        refine ⟨72222467097289989893827027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96296622796386653191769369 72222467097289989893827027)
        ·
          refine ⟨108333700645934984840740541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72222467097289989893827027 108333700645934984840740541)
          ·
            refine ⟨40625137742225619315277703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108333700645934984840740541 40625137742225619315277703)
            ·
              refine ⟨60937706613338428972916555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40625137742225619315277703 60937706613338428972916555)
              ·
                refine ⟨91406559920007643459374833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60937706613338428972916555 91406559920007643459374833)
                ·
                  refine ⟨68554919940005732594531125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91406559920007643459374833 68554919940005732594531125)
                  ·
                    refine ⟨6427023744375537430737293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68554919940005732594531125 6427023744375537430737293)
                    ·
                      refine ⟨2410133904140826536526485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427023744375537430737293 2410133904140826536526485)
                      ·
                        rfl

theorem cell23_4693719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_4693719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693719 prefixEnd_4693719 := by exact prefixLift 4693719
  have htrace : WordTrace (prefixWord ++ tailWord_4693719) baseStart_4693719 baseEnd_4693719 := by
    simpa [prefixWord, tailWord_4693719, baseEnd_4693719] using wordTrace_append hprefix tailTrace_4693719
  have hstable : (prefixWord ++ tailWord_4693719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693719).length < 2 ^ (prefixWord ++ tailWord_4693719).sum := by decide
  have hdescent : baseEnd_4693719 < baseStart_4693719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693769 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_4693769 : Nat := 118140960795 + 4693769 * 2 ^ 59
def prefixEnd_4693769 : Nat := 4983230072969 + 3 ^ 40 * 4693769 * 2
def baseEnd_4693769 : Nat := 803386526057850446967085

theorem tailTrace_4693769 : CollatzResearch.WordTrace tailWord_4693769 prefixEnd_4693769 803386526057850446967085 := by
  unfold tailWord_4693769
  simp only [CollatzResearch.WordTrace]
  refine ⟨171195819732284019769132361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114130546488189346512754907 171195819732284019769132361)
  ·
    refine ⟨128396864799213014826849271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171195819732284019769132361 128396864799213014826849271)
    ·
      refine ⟨192595297198819522240273907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128396864799213014826849271 192595297198819522240273907)
      ·
        refine ⟨288892945798229283360410861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192595297198819522240273907 288892945798229283360410861)
        ·
          refine ⟨108334854674335981260154073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288892945798229283360410861 108334854674335981260154073)
          ·
            refine ⟨81251141005751985945115555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108334854674335981260154073 81251141005751985945115555)
            ·
              refine ⟨121876711508627978917673333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81251141005751985945115555 121876711508627978917673333)
              ·
                refine ⟨11425941703933873023531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121876711508627978917673333 11425941703933873023531875)
                ·
                  refine ⟨17138912555900809535297813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11425941703933873023531875 17138912555900809535297813)
                  ·
                    refine ⟨803386526057850446967085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17138912555900809535297813 803386526057850446967085)
                    ·
                      rfl

theorem cell23_4693769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_4693769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693769 prefixEnd_4693769 := by exact prefixLift 4693769
  have htrace : WordTrace (prefixWord ++ tailWord_4693769) baseStart_4693769 baseEnd_4693769 := by
    simpa [prefixWord, tailWord_4693769, baseEnd_4693769] using wordTrace_append hprefix tailTrace_4693769
  have hstable : (prefixWord ++ tailWord_4693769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693769).length < 2 ^ (prefixWord ++ tailWord_4693769).sum := by decide
  have hdescent : baseEnd_4693769 < baseStart_4693769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693786 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_4693786 : Nat := 118140960795 + 4693786 * 2 ^ 59
def prefixEnd_4693786 : Nat := 4983230072969 + 3 ^ 40 * 4693786 * 2
def baseEnd_4693786 : Nat := 803389435781559258129559

theorem tailTrace_4693786 : CollatzResearch.WordTrace tailWord_4693786 prefixEnd_4693786 803389435781559258129559 := by
  unfold tailWord_4693786
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799109943305607918125303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114130959848814954448334141 42799109943305607918125303)
  ·
    refine ⟨64198664914958411877187955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42799109943305607918125303 64198664914958411877187955)
    ·
      refine ⟨96297997372437617815781933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64198664914958411877187955 96297997372437617815781933)
      ·
        refine ⟨36111749014664106680918225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96297997372437617815781933 36111749014664106680918225)
        ·
          refine ⟨27083811760998080010688669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36111749014664106680918225 27083811760998080010688669)
          ·
            refine ⟨10156429410374280004008251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27083811760998080010688669 10156429410374280004008251)
            ·
              refine ⟨15234644115561420006012377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156429410374280004008251 15234644115561420006012377)
              ·
                refine ⟨11425983086671065004509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15234644115561420006012377 11425983086671065004509283)
                ·
                  refine ⟨17138974630006597506763925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11425983086671065004509283 17138974630006597506763925)
                  ·
                    refine ⟨803389435781559258129559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17138974630006597506763925 803389435781559258129559)
                    ·
                      rfl

theorem cell23_4693786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_4693786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693786 prefixEnd_4693786 := by exact prefixLift 4693786
  have htrace : WordTrace (prefixWord ++ tailWord_4693786) baseStart_4693786 baseEnd_4693786 := by
    simpa [prefixWord, tailWord_4693786, baseEnd_4693786] using wordTrace_append hprefix tailTrace_4693786
  have hstable : (prefixWord ++ tailWord_4693786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693786).length < 2 ^ (prefixWord ++ tailWord_4693786).sum := by decide
  have hdescent : baseEnd_4693786 < baseStart_4693786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693816 : List Nat := [2, 1, 2, 1, 3, 5, 1, 8]
def baseStart_4693816 : Nat := 118140960795 + 4693816 * 2 ^ 59
def prefixEnd_4693816 : Nat := 4983230072969 + 3 ^ 40 * 4693816 * 2
def baseEnd_4693816 : Nat := 89266063398678246556057

theorem tailTrace_4693816 : CollatzResearch.WordTrace tailWord_4693816 prefixEnd_4693816 89266063398678246556057 := by
  unfold tailWord_4693816
  simp only [CollatzResearch.WordTrace]
  refine ⟨85598766981556873398046651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114131689308742497864062201 85598766981556873398046651)
  ·
    refine ⟨128398150472335310097069977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85598766981556873398046651 128398150472335310097069977)
    ·
      refine ⟨96298612854251482572802483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128398150472335310097069977 96298612854251482572802483)
      ·
        refine ⟨144447919281377223859203725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96298612854251482572802483 144447919281377223859203725)
        ·
          refine ⟨54167969730516458947201397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144447919281377223859203725 54167969730516458947201397)
          ·
            refine ⟨5078247162235918026300131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54167969730516458947201397 5078247162235918026300131)
            ·
              refine ⟨7617370743353877039450197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078247162235918026300131 7617370743353877039450197)
              ·
                refine ⟨89266063398678246556057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7617370743353877039450197 89266063398678246556057)
                ·
                  rfl

theorem cell23_4693816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 8].length) (baseStart_4693816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693816 prefixEnd_4693816 := by exact prefixLift 4693816
  have htrace : WordTrace (prefixWord ++ tailWord_4693816) baseStart_4693816 baseEnd_4693816 := by
    simpa [prefixWord, tailWord_4693816, baseEnd_4693816] using wordTrace_append hprefix tailTrace_4693816
  have hstable : (prefixWord ++ tailWord_4693816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693816).length < 2 ^ (prefixWord ++ tailWord_4693816).sum := by decide
  have hdescent : baseEnd_4693816 < baseStart_4693816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693823 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_4693823 : Nat := 118140960795 + 4693823 * 2 ^ 59
def prefixEnd_4693823 : Nat := 4983230072969 + 3 ^ 40 * 4693823 * 2
def baseEnd_4693823 : Nat := 2410187306128894129626007

theorem tailTrace_4693823 : CollatzResearch.WordTrace tailWord_4693823 prefixEnd_4693823 2410187306128894129626007 := by
  unfold tailWord_4693823
  simp only [CollatzResearch.WordTrace]
  refine ⟨171197789274088386991598123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114131859516058924661065415 171197789274088386991598123)
  ·
    refine ⟨256796683911132580487397185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171197789274088386991598123 256796683911132580487397185)
    ·
      refine ⟨192597512933349435365547889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256796683911132580487397185 192597512933349435365547889)
      ·
        refine ⟨144448134700012076524160917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192597512933349435365547889 144448134700012076524160917)
        ·
          refine ⟨6771006314063066087070043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144448134700012076524160917 6771006314063066087070043)
          ·
            refine ⟨10156509471094599130605065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771006314063066087070043 10156509471094599130605065)
            ·
              refine ⟨7617382103320949347953799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10156509471094599130605065 7617382103320949347953799)
              ·
                refine ⟨11426073154981424021930699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617382103320949347953799 11426073154981424021930699)
                ·
                  refine ⟨17139109732472136032896049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11426073154981424021930699 17139109732472136032896049)
                  ·
                    refine ⟨12854332299354102024672037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17139109732472136032896049 12854332299354102024672037)
                    ·
                      refine ⟨2410187306128894129626007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12854332299354102024672037 2410187306128894129626007)
                      ·
                        rfl

theorem cell23_4693823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_4693823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693823 prefixEnd_4693823 := by exact prefixLift 4693823
  have htrace : WordTrace (prefixWord ++ tailWord_4693823) baseStart_4693823 baseEnd_4693823 := by
    simpa [prefixWord, tailWord_4693823, baseEnd_4693823] using wordTrace_append hprefix tailTrace_4693823
  have hstable : (prefixWord ++ tailWord_4693823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693823).length < 2 ^ (prefixWord ++ tailWord_4693823).sum := by decide
  have hdescent : baseEnd_4693823 < baseStart_4693823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693829 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_4693829 : Nat := 118140960795 + 4693829 * 2 ^ 59
def prefixEnd_4693829 : Nat := 4983230072969 + 3 ^ 40 * 4693829 * 2
def baseEnd_4693829 : Nat := 803396795670940368716993

theorem tailTrace_4693829 : CollatzResearch.WordTrace tailWord_4693829 prefixEnd_4693829 803396795670940368716993 := by
  unfold tailWord_4693829
  simp only [CollatzResearch.WordTrace]
  refine ⟨171198008112066650016316541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114132005408044433344211027 171198008112066650016316541)
  ·
    refine ⟨64199253042024993756118703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171198008112066650016316541 64199253042024993756118703)
    ·
      refine ⟨96298879563037490634178055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64199253042024993756118703 96298879563037490634178055)
      ·
        refine ⟨144448319344556235951267083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96298879563037490634178055 144448319344556235951267083)
        ·
          refine ⟨216672479016834353926900625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144448319344556235951267083 216672479016834353926900625)
          ·
            refine ⟨162504359262625765445175469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216672479016834353926900625 162504359262625765445175469)
            ·
              refine ⟨60939134723484662041940801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162504359262625765445175469 60939134723484662041940801)
              ·
                refine ⟨45704351042613496531455601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60939134723484662041940801 45704351042613496531455601)
                ·
                  refine ⟨34278263281960122398591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45704351042613496531455601 34278263281960122398591701)
                  ·
                    refine ⟨803396795670940368716993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34278263281960122398591701 803396795670940368716993)
                    ·
                      rfl

theorem cell23_4693829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_4693829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693829 prefixEnd_4693829 := by exact prefixLift 4693829
  have htrace : WordTrace (prefixWord ++ tailWord_4693829) baseStart_4693829 baseEnd_4693829 := by
    simpa [prefixWord, tailWord_4693829, baseEnd_4693829] using wordTrace_append hprefix tailTrace_4693829
  have hstable : (prefixWord ++ tailWord_4693829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693829).length < 2 ^ (prefixWord ++ tailWord_4693829).sum := by decide
  have hdescent : baseEnd_4693829 < baseStart_4693829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693844 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_4693844 : Nat := 118140960795 + 4693844 * 2 ^ 59
def prefixEnd_4693844 : Nat := 4983230072969 + 3 ^ 40 * 4693844 * 2
def baseEnd_4693844 : Nat := 2410198089222638547463411

theorem tailTrace_4693844 : CollatzResearch.WordTrace tailWord_4693844 prefixEnd_4693844 2410198089222638547463411 := by
  unfold tailWord_4693844
  simp only [CollatzResearch.WordTrace]
  refine ⟨85599277603506153789056293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114132370138008205052075057 85599277603506153789056293)
  ·
    refine ⟨16049864550657403835448055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85599277603506153789056293 16049864550657403835448055)
    ·
      refine ⟨24074796825986105753172083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049864550657403835448055 24074796825986105753172083)
      ·
        refine ⟨36112195238979158629758125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24074796825986105753172083 36112195238979158629758125)
        ·
          refine ⟨13542073214617184486159297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36112195238979158629758125 13542073214617184486159297)
          ·
            refine ⟨10156554910962888364619473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13542073214617184486159297 10156554910962888364619473)
            ·
              refine ⟨7617416183222166273464605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10156554910962888364619473 7617416183222166273464605)
              ·
                refine ⟨2856531068708312352549227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7617416183222166273464605 2856531068708312352549227)
                ·
                  refine ⟨4284796603062468528823841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856531068708312352549227 4284796603062468528823841)
                  ·
                    refine ⟨3213597452296851396617881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4284796603062468528823841 3213597452296851396617881)
                    ·
                      refine ⟨2410198089222638547463411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213597452296851396617881 2410198089222638547463411)
                      ·
                        rfl

theorem cell23_4693844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_4693844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693844 prefixEnd_4693844 := by exact prefixLift 4693844
  have htrace : WordTrace (prefixWord ++ tailWord_4693844) baseStart_4693844 baseEnd_4693844 := by
    simpa [prefixWord, tailWord_4693844, baseEnd_4693844] using wordTrace_append hprefix tailTrace_4693844
  have hstable : (prefixWord ++ tailWord_4693844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693844).length < 2 ^ (prefixWord ++ tailWord_4693844).sum := by decide
  have hdescent : baseEnd_4693844 < baseStart_4693844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693847 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_4693847 : Nat := 118140960795 + 4693847 * 2 ^ 59
def prefixEnd_4693847 : Nat := 4983230072969 + 3 ^ 40 * 4693847 * 2
def baseEnd_4693847 : Nat := 2410199629664602035725897

theorem tailTrace_4693847 : CollatzResearch.WordTrace tailWord_4693847 prefixEnd_4693847 2410199629664602035725897 := by
  unfold tailWord_4693847
  simp only [CollatzResearch.WordTrace]
  refine ⟨171198664626001439090471795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114132443084000959393647863 171198664626001439090471795)
  ·
    refine ⟨256797996939002158635707693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171198664626001439090471795 256797996939002158635707693)
    ·
      refine ⟨96299248852125809488390385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256797996939002158635707693 96299248852125809488390385)
      ·
        refine ⟨72224436639094357116292789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96299248852125809488390385 72224436639094357116292789)
        ·
          refine ⟨6771040934915095979652449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72224436639094357116292789 6771040934915095979652449)
          ·
            refine ⟨5078280701186321984739337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771040934915095979652449 5078280701186321984739337)
            ·
              refine ⟨3808710525889741488554503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078280701186321984739337 3808710525889741488554503)
              ·
                refine ⟨5713065788834612232831755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808710525889741488554503 5713065788834612232831755)
                ·
                  refine ⟨8569598683251918349247633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713065788834612232831755 8569598683251918349247633)
                  ·
                    refine ⟨6427199012438938761935725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8569598683251918349247633 6427199012438938761935725)
                    ·
                      refine ⟨2410199629664602035725897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427199012438938761935725 2410199629664602035725897)
                      ·
                        rfl

theorem cell23_4693847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_4693847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693847 prefixEnd_4693847 := by exact prefixLift 4693847
  have htrace : WordTrace (prefixWord ++ tailWord_4693847) baseStart_4693847 baseEnd_4693847 := by
    simpa [prefixWord, tailWord_4693847, baseEnd_4693847] using wordTrace_append hprefix tailTrace_4693847
  have hstable : (prefixWord ++ tailWord_4693847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693847).length < 2 ^ (prefixWord ++ tailWord_4693847).sum := by decide
  have hdescent : baseEnd_4693847 < baseStart_4693847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693860 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_4693860 : Nat := 118140960795 + 4693860 * 2 ^ 59
def prefixEnd_4693860 : Nat := 4983230072969 + 3 ^ 40 * 4693860 * 2
def baseEnd_4693860 : Nat := 2410206304913110484863337

theorem tailTrace_4693860 : CollatzResearch.WordTrace tailWord_4693860 prefixEnd_4693860 2410206304913110484863337 := by
  unfold tailWord_4693860
  simp only [CollatzResearch.WordTrace]
  refine ⟨85599569387477171155347517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114132759183302894873796689 85599569387477171155347517)
  ·
    refine ⟨32099838520303939183255319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85599569387477171155347517 32099838520303939183255319)
    ·
      refine ⟨48149757780455908774882979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32099838520303939183255319 48149757780455908774882979)
      ·
        refine ⟨72224636670683863162324469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48149757780455908774882979 72224636670683863162324469)
        ·
          refine ⟨6771059687876612171467919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72224636670683863162324469 6771059687876612171467919)
          ·
            refine ⟨10156589531814918257201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771059687876612171467919 10156589531814918257201879)
            ·
              refine ⟨15234884297722377385802819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156589531814918257201879 15234884297722377385802819)
              ·
                refine ⟨22852326446583566078704229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15234884297722377385802819 22852326446583566078704229)
                ·
                  refine ⟨4284811208734418639757043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22852326446583566078704229 4284811208734418639757043)
                  ·
                    refine ⟨6427216813101627959635565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4284811208734418639757043 6427216813101627959635565)
                    ·
                      refine ⟨2410206304913110484863337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427216813101627959635565 2410206304913110484863337)
                      ·
                        rfl

theorem cell23_4693860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_4693860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693860 prefixEnd_4693860 := by exact prefixLift 4693860
  have htrace : WordTrace (prefixWord ++ tailWord_4693860) baseStart_4693860 baseEnd_4693860 := by
    simpa [prefixWord, tailWord_4693860, baseEnd_4693860] using wordTrace_append hprefix tailTrace_4693860
  have hstable : (prefixWord ++ tailWord_4693860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693860).length < 2 ^ (prefixWord ++ tailWord_4693860).sum := by decide
  have hdescent : baseEnd_4693860 < baseStart_4693860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693877 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4693877 : Nat := 118140960795 + 4693877 * 2 ^ 59
def prefixEnd_4693877 : Nat := 4983230072969 + 3 ^ 40 * 4693877 * 2
def baseEnd_4693877 : Nat := 2410215034084236918350759

theorem tailTrace_4693877 : CollatzResearch.WordTrace tailWord_4693877 prefixEnd_4693877 2410215034084236918350759 := by
  unfold tailWord_4693877
  simp only [CollatzResearch.WordTrace]
  refine ⟨171199758815892754214063885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114133172543928502809375923 171199758815892754214063885)
  ·
    refine ⟨64199909555959782830273957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171199758815892754214063885 64199909555959782830273957)
    ·
      refine ⟨12037483041742459280676367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64199909555959782830273957 12037483041742459280676367)
      ·
        refine ⟨18056224562613688921014551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12037483041742459280676367 18056224562613688921014551)
        ·
          refine ⟨27084336843920533381521827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18056224562613688921014551 27084336843920533381521827)
          ·
            refine ⟨40626505265880800072282741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27084336843920533381521827 40626505265880800072282741)
            ·
              refine ⟨3808734868676325006776507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40626505265880800072282741 3808734868676325006776507)
              ·
                refine ⟨5713102303014487510164761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808734868676325006776507 5713102303014487510164761)
                ·
                  refine ⟨4284826727260865632623571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713102303014487510164761 4284826727260865632623571)
                  ·
                    refine ⟨6427240090891298448935357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4284826727260865632623571 6427240090891298448935357)
                    ·
                      refine ⟨2410215034084236918350759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427240090891298448935357 2410215034084236918350759)
                      ·
                        rfl

theorem cell23_4693877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4693877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693877 prefixEnd_4693877 := by exact prefixLift 4693877
  have htrace : WordTrace (prefixWord ++ tailWord_4693877) baseStart_4693877 baseEnd_4693877 := by
    simpa [prefixWord, tailWord_4693877, baseEnd_4693877] using wordTrace_append hprefix tailTrace_4693877
  have hstable : (prefixWord ++ tailWord_4693877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693877).length < 2 ^ (prefixWord ++ tailWord_4693877).sum := by decide
  have hdescent : baseEnd_4693877 < baseStart_4693877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693928 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4693928 : Nat := 118140960795 + 4693928 * 2 ^ 59
def prefixEnd_4693928 : Nat := 4983230072969 + 3 ^ 40 * 4693928 * 2
def baseEnd_4693928 : Nat := 2410241221597616218813025

theorem tailTrace_4693928 : CollatzResearch.WordTrace tailWord_4693928 prefixEnd_4693928 2410241221597616218813025 := by
  unfold tailWord_4693928
  simp only [CollatzResearch.WordTrace]
  refine ⟨85600809469353994962085219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114134412625805326616113625 85600809469353994962085219)
  ·
    refine ⟨128401214204030992443127829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85600809469353994962085219 128401214204030992443127829)
    ·
      refine ⟨6018806915813952770771617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128401214204030992443127829 6018806915813952770771617)
      ·
        refine ⟨4514105186860464578078713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6018806915813952770771617 4514105186860464578078713)
        ·
          refine ⟨3385578890145348433559035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514105186860464578078713 3385578890145348433559035)
          ·
            refine ⟨5078368335218022650338553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385578890145348433559035 5078368335218022650338553)
            ·
              refine ⟨3808776251413516987753915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078368335218022650338553 3808776251413516987753915)
              ·
                refine ⟨5713164377120275481630873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808776251413516987753915 5713164377120275481630873)
                ·
                  refine ⟨4284873282840206611223155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713164377120275481630873 4284873282840206611223155)
                  ·
                    refine ⟨6427309924260309916834733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4284873282840206611223155 6427309924260309916834733)
                    ·
                      refine ⟨2410241221597616218813025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427309924260309916834733 2410241221597616218813025)
                      ·
                        rfl

theorem cell23_4693928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4693928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693928 prefixEnd_4693928 := by exact prefixLift 4693928
  have htrace : WordTrace (prefixWord ++ tailWord_4693928) baseStart_4693928 baseEnd_4693928 := by
    simpa [prefixWord, tailWord_4693928, baseEnd_4693928] using wordTrace_append hprefix tailTrace_4693928
  have hstable : (prefixWord ++ tailWord_4693928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693928).length < 2 ^ (prefixWord ++ tailWord_4693928).sum := by decide
  have hdescent : baseEnd_4693928 < baseStart_4693928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4693976 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4693976 : Nat := 118140960795 + 4693976 * 2 ^ 59
def prefixEnd_4693976 : Nat := 4983230072969 + 3 ^ 40 * 4693976 * 2
def baseEnd_4693976 : Nat := 2410265868669032031012803

theorem tailTrace_4693976 : CollatzResearch.WordTrace tailWord_4693976 prefixEnd_4693976 2410265868669032031012803 := by
  unfold tailWord_4693976
  simp only [CollatzResearch.WordTrace]
  refine ⟨85601684821267047060958891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114135579761689396081278521 85601684821267047060958891)
  ·
    refine ⟨128402527231900570591438337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85601684821267047060958891 128402527231900570591438337)
    ·
      refine ⟨96301895423925427943578753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128402527231900570591438337 96301895423925427943578753)
      ·
        refine ⟨72226421567944070957684065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96301895423925427943578753 72226421567944070957684065)
        ·
          refine ⟨54169816175958053218263049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72226421567944070957684065 54169816175958053218263049)
          ·
            refine ⟨40627362131968539913697287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54169816175958053218263049 40627362131968539913697287)
            ·
              refine ⟨60941043197952809870545931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40627362131968539913697287 60941043197952809870545931)
              ·
                refine ⟨91411564796929214805818897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60941043197952809870545931 91411564796929214805818897)
                ·
                  refine ⟨68558673597696911104364173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91411564796929214805818897 68558673597696911104364173)
                  ·
                    refine ⟨25709502599136341664136565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68558673597696911104364173 25709502599136341664136565)
                    ·
                      refine ⟨2410265868669032031012803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25709502599136341664136565 2410265868669032031012803)
                      ·
                        rfl

theorem cell23_4693976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4693976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4693976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4693976 prefixEnd_4693976 := by exact prefixLift 4693976
  have htrace : WordTrace (prefixWord ++ tailWord_4693976) baseStart_4693976 baseEnd_4693976 := by
    simpa [prefixWord, tailWord_4693976, baseEnd_4693976] using wordTrace_append hprefix tailTrace_4693976
  have hstable : (prefixWord ++ tailWord_4693976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4693976).length < 2 ^ (prefixWord ++ tailWord_4693976).sum := by decide
  have hdescent : baseEnd_4693976 < baseStart_4693976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4693976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694017 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4694017 : Nat := 118140960795 + 4694017 * 2 ^ 59
def prefixEnd_4694017 : Nat := 4983230072969 + 3 ^ 40 * 4694017 * 2
def baseEnd_4694017 : Nat := 803428973791955456866705

theorem tailTrace_4694017 : CollatzResearch.WordTrace tailWord_4694017 prefixEnd_4694017 803428973791955456866705 := by
  unfold tailWord_4694017
  simp only [CollatzResearch.WordTrace]
  refine ⟨171204865035385558124160305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114136576690257038749440203 171204865035385558124160305)
  ·
    refine ⟨128403648776539168593120229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171204865035385558124160305 128403648776539168593120229)
    ·
      refine ⟨24075684145601094111210043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128403648776539168593120229 24075684145601094111210043)
      ·
        refine ⟨36113526218401641166815065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24075684145601094111210043 36113526218401641166815065)
        ·
          refine ⟨27085144663801230875111299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36113526218401641166815065 27085144663801230875111299)
          ·
            refine ⟨40627716995701846312666949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27085144663801230875111299 40627716995701846312666949)
            ·
              refine ⟨7617696936694096183625053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40627716995701846312666949 7617696936694096183625053)
              ·
                refine ⟨2856636351260286068859395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7617696936694096183625053 2856636351260286068859395)
                ·
                  refine ⟨4284954526890429103289093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856636351260286068859395 4284954526890429103289093)
                  ·
                    refine ⟨803428973791955456866705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284954526890429103289093 803428973791955456866705)
                    ·
                      rfl

theorem cell23_4694017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4694017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694017 prefixEnd_4694017 := by exact prefixLift 4694017
  have htrace : WordTrace (prefixWord ++ tailWord_4694017) baseStart_4694017 baseEnd_4694017 := by
    simpa [prefixWord, tailWord_4694017, baseEnd_4694017] using wordTrace_append hprefix tailTrace_4694017
  have hstable : (prefixWord ++ tailWord_4694017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694017).length < 2 ^ (prefixWord ++ tailWord_4694017).sum := by decide
  have hdescent : baseEnd_4694017 < baseStart_4694017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694050 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_4694050 : Nat := 118140960795 + 4694050 * 2 ^ 59
def prefixEnd_4694050 : Nat := 4983230072969 + 3 ^ 40 * 4694050 * 2
def baseEnd_4694050 : Nat := 2410303866237464741487463

theorem tailTrace_4694050 : CollatzResearch.WordTrace tailWord_4694050 prefixEnd_4694050 2410303866237464741487463 := by
  unfold tailWord_4694050
  simp only [CollatzResearch.WordTrace]
  refine ⟨42801517161066501190027901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114137379096177336506741069 42801517161066501190027901)
  ·
    refine ⟨16050568935399937946260463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42801517161066501190027901 16050568935399937946260463)
    ·
      refine ⟨24075853403099906919390695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16050568935399937946260463 24075853403099906919390695)
      ·
        refine ⟨36113780104649860379086043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24075853403099906919390695 36113780104649860379086043)
        ·
          refine ⟨54170670156974790568629065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36113780104649860379086043 54170670156974790568629065)
          ·
            refine ⟨40628002617731092926471799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54170670156974790568629065 40628002617731092926471799)
            ·
              refine ⟨60942003926596639389707699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40628002617731092926471799 60942003926596639389707699)
              ·
                refine ⟨91413005889894959084561549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60942003926596639389707699 91413005889894959084561549)
                ·
                  refine ⟨34279877208710609656710581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91413005889894959084561549 34279877208710609656710581)
                  ·
                    refine ⟨3213738488316619655316617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34279877208710609656710581 3213738488316619655316617)
                    ·
                      refine ⟨2410303866237464741487463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213738488316619655316617 2410303866237464741487463)
                      ·
                        rfl

theorem cell23_4694050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_4694050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694050 prefixEnd_4694050 := by exact prefixLift 4694050
  have htrace : WordTrace (prefixWord ++ tailWord_4694050) baseStart_4694050 baseEnd_4694050 := by
    simpa [prefixWord, tailWord_4694050, baseEnd_4694050] using wordTrace_append hprefix tailTrace_4694050
  have hstable : (prefixWord ++ tailWord_4694050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694050).length < 2 ^ (prefixWord ++ tailWord_4694050).sum := by decide
  have hdescent : baseEnd_4694050 < baseStart_4694050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694068 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_4694068 : Nat := 118140960795 + 4694068 * 2 ^ 59
def prefixEnd_4694068 : Nat := 4983230072969 + 3 ^ 40 * 4694068 * 2
def baseEnd_4694068 : Nat := 803437702963081890354127

theorem tailTrace_4694068 : CollatzResearch.WordTrace tailWord_4694068 prefixEnd_4694068 803437702963081890354127 := by
  unfold tailWord_4694068
  simp only [CollatzResearch.WordTrace]
  refine ⟨85603362579100396917133429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114137816772133862556177905 85603362579100396917133429)
  ·
    refine ⟨8025315241790662210981259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85603362579100396917133429 8025315241790662210981259)
    ·
      refine ⟨12037972862685993316471889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025315241790662210981259 12037972862685993316471889)
      ·
        refine ⟨9028479647014494987353917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12037972862685993316471889 9028479647014494987353917)
        ·
          refine ⟨3385679867630435620257719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9028479647014494987353917 3385679867630435620257719)
          ·
            refine ⟨5078519801445653430386579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385679867630435620257719 5078519801445653430386579)
            ·
              refine ⟨7617779702168480145579869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078519801445653430386579 7617779702168480145579869)
              ·
                refine ⟨2856667388313180054592451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7617779702168480145579869 2856667388313180054592451)
                ·
                  refine ⟨4285001082469770081888677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856667388313180054592451 4285001082469770081888677)
                  ·
                    refine ⟨803437702963081890354127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285001082469770081888677 803437702963081890354127)
                    ·
                      rfl

theorem cell23_4694068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_4694068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694068 prefixEnd_4694068 := by exact prefixLift 4694068
  have htrace : WordTrace (prefixWord ++ tailWord_4694068) baseStart_4694068 baseEnd_4694068 := by
    simpa [prefixWord, tailWord_4694068, baseEnd_4694068] using wordTrace_append hprefix tailTrace_4694068
  have hstable : (prefixWord ++ tailWord_4694068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694068).length < 2 ^ (prefixWord ++ tailWord_4694068).sum := by decide
  have hdescent : baseEnd_4694068 < baseStart_4694068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694080 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_4694080 : Nat := 118140960795 + 4694080 * 2 ^ 59
def prefixEnd_4694080 : Nat := 4983230072969 + 3 ^ 40 * 4694080 * 2
def baseEnd_4694080 : Nat := 2410319270657099624112325

theorem tailTrace_4694080 : CollatzResearch.WordTrace tailWord_4694080 prefixEnd_4694080 2410319270657099624112325 := by
  unfold tailWord_4694080
  simp only [CollatzResearch.WordTrace]
  refine ⟨85603581417078659941851847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114138108556104879922469129 85603581417078659941851847)
  ·
    refine ⟨128405372125617989912777771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85603581417078659941851847 128405372125617989912777771)
    ·
      refine ⟨192608058188426984869166657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128405372125617989912777771 192608058188426984869166657)
      ·
        refine ⟨144456043641320238651874993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192608058188426984869166657 144456043641320238651874993)
        ·
          refine ⟨108342032730990178988906245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144456043641320238651874993 108342032730990178988906245)
          ·
            refine ⟨20314131137060658560419921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108342032730990178988906245 20314131137060658560419921)
            ·
              refine ⟨15235598352795493920314941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20314131137060658560419921 15235598352795493920314941)
              ·
                refine ⟨5713349382298310220118103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15235598352795493920314941 5713349382298310220118103)
                ·
                  refine ⟨8570024073447465330177155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713349382298310220118103 8570024073447465330177155)
                  ·
                    refine ⟨12855036110171197995265733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8570024073447465330177155 12855036110171197995265733)
                    ·
                      refine ⟨2410319270657099624112325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12855036110171197995265733 2410319270657099624112325)
                      ·
                        rfl

theorem cell23_4694080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_4694080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694080 prefixEnd_4694080 := by exact prefixLift 4694080
  have htrace : WordTrace (prefixWord ++ tailWord_4694080) baseStart_4694080 baseEnd_4694080 := by
    simpa [prefixWord, tailWord_4694080, baseEnd_4694080] using wordTrace_append hprefix tailTrace_4694080
  have hstable : (prefixWord ++ tailWord_4694080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694080).length < 2 ^ (prefixWord ++ tailWord_4694080).sum := by decide
  have hdescent : baseEnd_4694080 < baseStart_4694080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694090 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_4694090 : Nat := 118140960795 + 4694090 * 2 ^ 59
def prefixEnd_4694090 : Nat := 4983230072969 + 3 ^ 40 * 4694090 * 2
def baseEnd_4694090 : Nat := 803441468487881528329093

theorem tailTrace_4694090 : CollatzResearch.WordTrace tailWord_4694090 prefixEnd_4694090 803441468487881528329093 := by
  unfold tailWord_4694090
  simp only [CollatzResearch.WordTrace]
  refine ⟨42801881891030272897891931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114138351709414061061045149 42801881891030272897891931)
  ·
    refine ⟨64202822836545409346837897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42801881891030272897891931 64202822836545409346837897)
    ·
      refine ⟨48152117127409057010128423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64202822836545409346837897 48152117127409057010128423)
      ·
        refine ⟨72228175691113585515192635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48152117127409057010128423 72228175691113585515192635)
        ·
          refine ⟨108342263536670378272788953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72228175691113585515192635 108342263536670378272788953)
          ·
            refine ⟨81256697652502783704591715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108342263536670378272788953 81256697652502783704591715)
            ·
              refine ⟨121885046478754175556887573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81256697652502783704591715 121885046478754175556887573)
              ·
                refine ⟨5713361553691601979229105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121885046478754175556887573 5713361553691601979229105)
                ·
                  refine ⟨4285021165268701484421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713361553691601979229105 4285021165268701484421829)
                  ·
                    refine ⟨803441468487881528329093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285021165268701484421829 803441468487881528329093)
                    ·
                      rfl

theorem cell23_4694090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_4694090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694090 prefixEnd_4694090 := by exact prefixLift 4694090
  have htrace : WordTrace (prefixWord ++ tailWord_4694090) baseStart_4694090 baseEnd_4694090 := by
    simpa [prefixWord, tailWord_4694090, baseEnd_4694090] using wordTrace_append hprefix tailTrace_4694090
  have hstable : (prefixWord ++ tailWord_4694090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694090).length < 2 ^ (prefixWord ++ tailWord_4694090).sum := by decide
  have hdescent : baseEnd_4694090 < baseStart_4694090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694100 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_4694100 : Nat := 118140960795 + 4694100 * 2 ^ 59
def prefixEnd_4694100 : Nat := 4983230072969 + 3 ^ 40 * 4694100 * 2
def baseEnd_4694100 : Nat := 2410329540270189545862233

theorem tailTrace_4694100 : CollatzResearch.WordTrace tailWord_4694100 prefixEnd_4694100 2410329540270189545862233 := by
  unfold tailWord_4694100
  simp only [CollatzResearch.WordTrace]
  refine ⟨85603946147042431649715877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114138594862723242199621169 85603946147042431649715877)
  ·
    refine ⟨16050739902570455934321727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85603946147042431649715877 16050739902570455934321727)
    ·
      refine ⟨24076109853855683901482591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16050739902570455934321727 24076109853855683901482591)
      ·
        refine ⟨36114164780783525852223887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24076109853855683901482591 36114164780783525852223887)
        ·
          refine ⟨54171247171175288778335831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36114164780783525852223887 54171247171175288778335831)
          ·
            refine ⟨81256870756762933167503747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54171247171175288778335831 81256870756762933167503747)
            ·
              refine ⟨121885306135144399751255621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81256870756762933167503747 121885306135144399751255621)
              ·
                refine ⟨22853494900339574953360429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121885306135144399751255621 22853494900339574953360429)
                ·
                  refine ⟨8570060587627340607510161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22853494900339574953360429 8570060587627340607510161)
                  ·
                    refine ⟨6427545440720505455632621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8570060587627340607510161 6427545440720505455632621)
                    ·
                      refine ⟨2410329540270189545862233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427545440720505455632621 2410329540270189545862233)
                      ·
                        rfl

theorem cell23_4694100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_4694100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694100 prefixEnd_4694100 := by exact prefixLift 4694100
  have htrace : WordTrace (prefixWord ++ tailWord_4694100) baseStart_4694100 baseEnd_4694100 := by
    simpa [prefixWord, tailWord_4694100, baseEnd_4694100] using wordTrace_append hprefix tailTrace_4694100
  have hstable : (prefixWord ++ tailWord_4694100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694100).length < 2 ^ (prefixWord ++ tailWord_4694100).sum := by decide
  have hdescent : baseEnd_4694100 < baseStart_4694100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694117 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_4694117 : Nat := 118140960795 + 4694117 * 2 ^ 59
def prefixEnd_4694117 : Nat := 4983230072969 + 3 ^ 40 * 4694117 * 2
def baseEnd_4694117 : Nat := 2410338269441315979349655

theorem tailTrace_4694117 : CollatzResearch.WordTrace tailWord_4694117 prefixEnd_4694117 2410338269441315979349655 := by
  unfold tailWord_4694117
  simp only [CollatzResearch.WordTrace]
  refine ⟨171208512335023275202800605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114139008223348850135200403 171208512335023275202800605)
  ·
    refine ⟨64203192125633728201050227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171208512335023275202800605 64203192125633728201050227)
    ·
      refine ⟨96304788188450592301575341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64203192125633728201050227 96304788188450592301575341)
      ·
        refine ⟨36114295570668972113090753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96304788188450592301575341 36114295570668972113090753)
        ·
          refine ⟨27085721678001729084818065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36114295570668972113090753 27085721678001729084818065)
          ·
            refine ⟨20314291258501296813613549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27085721678001729084818065 20314291258501296813613549)
            ·
              refine ⟨7617859221937986305105081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20314291258501296813613549 7617859221937986305105081)
              ·
                refine ⟨5713394416453489728828811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7617859221937986305105081 5713394416453489728828811)
                ·
                  refine ⟨8570091624680234593243217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713394416453489728828811 8570091624680234593243217)
                  ·
                    refine ⟨6427568718510175944932413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8570091624680234593243217 6427568718510175944932413)
                    ·
                      refine ⟨2410338269441315979349655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427568718510175944932413 2410338269441315979349655)
                      ·
                        rfl

theorem cell23_4694117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_4694117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694117 prefixEnd_4694117 := by exact prefixLift 4694117
  have htrace : WordTrace (prefixWord ++ tailWord_4694117) baseStart_4694117 baseEnd_4694117 := by
    simpa [prefixWord, tailWord_4694117, baseEnd_4694117] using wordTrace_append hprefix tailTrace_4694117
  have hstable : (prefixWord ++ tailWord_4694117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694117).length < 2 ^ (prefixWord ++ tailWord_4694117).sum := by decide
  have hdescent : baseEnd_4694117 < baseStart_4694117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694130 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_4694130 : Nat := 118140960795 + 4694130 * 2 ^ 59
def prefixEnd_4694130 : Nat := 4983230072969 + 3 ^ 40 * 4694130 * 2
def baseEnd_4694130 : Nat := 2410344944689824428487095

theorem tailTrace_4694130 : CollatzResearch.WordTrace tailWord_4694130 prefixEnd_4694130 2410344944689824428487095 := by
  unfold tailWord_4694130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802246620994044605755961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114139324322650785615349229 42802246620994044605755961)
  ·
    refine ⟨32101684965745533454316971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42802246620994044605755961 32101684965745533454316971)
    ·
      refine ⟨48152527448618300181475457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32101684965745533454316971 48152527448618300181475457)
      ·
        refine ⟨36114395586463725136106593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48152527448618300181475457 36114395586463725136106593)
        ·
          refine ⟨27085796689847793852079945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36114395586463725136106593 27085796689847793852079945)
          ·
            refine ⟨20314347517385845389059959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27085796689847793852079945 20314347517385845389059959)
            ·
              refine ⟨30471521276078768083589939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20314347517385845389059959 30471521276078768083589939)
              ·
                refine ⟨45707281914118152125384909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30471521276078768083589939 45707281914118152125384909)
                ·
                  refine ⟨17140230717794307047019341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45707281914118152125384909 17140230717794307047019341)
                  ·
                    refine ⟨6427586519172865142632253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17140230717794307047019341 6427586519172865142632253)
                    ·
                      refine ⟨2410344944689824428487095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427586519172865142632253 2410344944689824428487095)
                      ·
                        rfl

theorem cell23_4694130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_4694130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694130 prefixEnd_4694130 := by exact prefixLift 4694130
  have htrace : WordTrace (prefixWord ++ tailWord_4694130) baseStart_4694130 baseEnd_4694130 := by
    simpa [prefixWord, tailWord_4694130, baseEnd_4694130] using wordTrace_append hprefix tailTrace_4694130
  have hstable : (prefixWord ++ tailWord_4694130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694130).length < 2 ^ (prefixWord ++ tailWord_4694130).sum := by decide
  have hdescent : baseEnd_4694130 < baseStart_4694130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694147 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 3]
def baseStart_4694147 : Nat := 118140960795 + 4694147 * 2 ^ 59
def prefixEnd_4694147 : Nat := 4983230072969 + 3 ^ 40 * 4694147 * 2
def baseEnd_4694147 : Nat := 2410353673860950861974517

theorem tailTrace_4694147 : CollatzResearch.WordTrace tailWord_4694147 prefixEnd_4694147 2410353673860950861974517 := by
  unfold tailWord_4694147
  simp only [CollatzResearch.WordTrace]
  refine ⟨171209606524914590326392695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114139737683276393550928463 171209606524914590326392695)
  ·
    refine ⟨256814409787371885489589043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171209606524914590326392695 256814409787371885489589043)
    ·
      refine ⟨385221614681057828234383565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256814409787371885489589043 385221614681057828234383565)
      ·
        refine ⟨144458105505396685587893837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385221614681057828234383565 144458105505396685587893837)
        ·
          refine ⟨54171789564523757095460189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144458105505396685587893837 54171789564523757095460189)
          ·
            refine ⟨20314421086696408910797571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54171789564523757095460189 20314421086696408910797571)
            ·
              refine ⟨30471631630044613366196357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20314421086696408910797571 30471631630044613366196357)
              ·
                refine ⟨5713430930633365006161817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30471631630044613366196357 5713430930633365006161817)
                ·
                  refine ⟨4285073197975023754621363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713430930633365006161817 4285073197975023754621363)
                  ·
                    refine ⟨6427609796962535631932045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285073197975023754621363 6427609796962535631932045)
                    ·
                      refine ⟨2410353673860950861974517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427609796962535631932045 2410353673860950861974517)
                      ·
                        rfl

theorem cell23_4694147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_4694147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694147 prefixEnd_4694147 := by exact prefixLift 4694147
  have htrace : WordTrace (prefixWord ++ tailWord_4694147) baseStart_4694147 baseEnd_4694147 := by
    simpa [prefixWord, tailWord_4694147, baseEnd_4694147] using wordTrace_append hprefix tailTrace_4694147
  have hstable : (prefixWord ++ tailWord_4694147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694147).length < 2 ^ (prefixWord ++ tailWord_4694147).sum := by decide
  have hdescent : baseEnd_4694147 < baseStart_4694147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694153 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_4694153 : Nat := 118140960795 + 4694153 * 2 ^ 59
def prefixEnd_4694153 : Nat := 4983230072969 + 3 ^ 40 * 4694153 * 2
def baseEnd_4694153 : Nat := 2410356754744877838499489

theorem tailTrace_4694153 : CollatzResearch.WordTrace tailWord_4694153 prefixEnd_4694153 2410356754744877838499489 := by
  unfold tailWord_4694153
  simp only [CollatzResearch.WordTrace]
  refine ⟨171209825362892853351111113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114139883575261902234074075 171209825362892853351111113)
  ·
    refine ⟨128407369022169640013333335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171209825362892853351111113 128407369022169640013333335)
    ·
      refine ⟨192611053533254460020000003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128407369022169640013333335 192611053533254460020000003)
      ·
        refine ⟨288916580299881690030000005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192611053533254460020000003 288916580299881690030000005)
        ·
          refine ⟨54171858806227816880625001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288916580299881690030000005 54171858806227816880625001)
          ·
            refine ⟨40628894104670862660468751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54171858806227816880625001 40628894104670862660468751)
            ·
              refine ⟨60943341157006293990703127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40628894104670862660468751 60943341157006293990703127)
              ·
                refine ⟨91415011735509440986054691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60943341157006293990703127 91415011735509440986054691)
                ·
                  refine ⟨137122517603264161479082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91415011735509440986054691 137122517603264161479082037)
                  ·
                    refine ⟨12855236025306015138663941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137122517603264161479082037 12855236025306015138663941)
                    ·
                      refine ⟨2410356754744877838499489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12855236025306015138663941 2410356754744877838499489)
                      ·
                        rfl

theorem cell23_4694153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_4694153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694153 prefixEnd_4694153 := by exact prefixLift 4694153
  have htrace : WordTrace (prefixWord ++ tailWord_4694153) baseStart_4694153 baseEnd_4694153 := by
    simpa [prefixWord, tailWord_4694153, baseEnd_4694153] using wordTrace_append hprefix tailTrace_4694153
  have hstable : (prefixWord ++ tailWord_4694153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694153).length < 2 ^ (prefixWord ++ tailWord_4694153).sum := by decide
  have hdescent : baseEnd_4694153 < baseStart_4694153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694223 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 7]
def baseStart_4694223 : Nat := 118140960795 + 4694223 * 2 ^ 59
def prefixEnd_4694223 : Nat := 4983230072969 + 3 ^ 40 * 4694223 * 2
def baseEnd_4694223 : Nat := 803464232796897521541389

theorem tailTrace_4694223 : CollatzResearch.WordTrace tailWord_4694223 prefixEnd_4694223 803464232796897521541389 := by
  unfold tailWord_4694223
  simp only [CollatzResearch.WordTrace]
  refine ⟨171212378472639255306159323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114141585648426170204106215 171212378472639255306159323)
  ·
    refine ⟨256818567708958882959238985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171212378472639255306159323 256818567708958882959238985)
    ·
      refine ⟨192613925781719162219429239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256818567708958882959238985 192613925781719162219429239)
      ·
        refine ⟨288920888672578743329143859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192613925781719162219429239 288920888672578743329143859)
        ·
          refine ⟨433381333008868114993715789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288920888672578743329143859 433381333008868114993715789)
          ·
            refine ⟨162517999878325543122643421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433381333008868114993715789 162517999878325543122643421)
            ·
              refine ⟨60944249954372078670991283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162517999878325543122643421 60944249954372078670991283)
              ·
                refine ⟨91416374931558118006486925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60944249954372078670991283 91416374931558118006486925)
                ·
                  refine ⟨34281140599334294252432597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91416374931558118006486925 34281140599334294252432597)
                  ·
                    refine ⟨803464232796897521541389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34281140599334294252432597 803464232796897521541389)
                    ·
                      rfl

theorem cell23_4694223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_4694223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694223 prefixEnd_4694223 := by exact prefixLift 4694223
  have htrace : WordTrace (prefixWord ++ tailWord_4694223) baseStart_4694223 baseEnd_4694223 := by
    simpa [prefixWord, tailWord_4694223, baseEnd_4694223] using wordTrace_append hprefix tailTrace_4694223
  have hstable : (prefixWord ++ tailWord_4694223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694223).length < 2 ^ (prefixWord ++ tailWord_4694223).sum := by decide
  have hdescent : baseEnd_4694223 < baseStart_4694223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694240 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_4694240 : Nat := 118140960795 + 4694240 * 2 ^ 59
def prefixEnd_4694240 : Nat := 4983230072969 + 3 ^ 40 * 4694240 * 2
def baseEnd_4694240 : Nat := 803467142520606332703863

theorem tailTrace_4694240 : CollatzResearch.WordTrace tailWord_4694240 prefixEnd_4694240 803467142520606332703863 := by
  unfold tailWord_4694240
  simp only [CollatzResearch.WordTrace]
  refine ⟨85606499256788833604764087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114141999009051778139685449 85606499256788833604764087)
  ·
    refine ⟨128409748885183250407146131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85606499256788833604764087 128409748885183250407146131)
    ·
      refine ⟨192614623327774875610719197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128409748885183250407146131 192614623327774875610719197)
      ·
        refine ⟨72230483747915578354019699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192614623327774875610719197 72230483747915578354019699)
        ·
          refine ⟨108345725621873367531029549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72230483747915578354019699 108345725621873367531029549)
          ·
            refine ⟨40629647108202512824136081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108345725621873367531029549 40629647108202512824136081)
            ·
              refine ⟨30472235331151884618102061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40629647108202512824136081 30472235331151884618102061)
              ·
                refine ⟨11427088249181956731788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30472235331151884618102061 11427088249181956731788273)
                ·
                  refine ⟨8570316186886467548841205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11427088249181956731788273 8570316186886467548841205)
                  ·
                    refine ⟨803467142520606332703863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8570316186886467548841205 803467142520606332703863)
                    ·
                      rfl

theorem cell23_4694240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_4694240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694240 prefixEnd_4694240 := by exact prefixLift 4694240
  have htrace : WordTrace (prefixWord ++ tailWord_4694240) baseStart_4694240 baseEnd_4694240 := by
    simpa [prefixWord, tailWord_4694240, baseEnd_4694240] using wordTrace_append hprefix tailTrace_4694240
  have hstable : (prefixWord ++ tailWord_4694240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694240).length < 2 ^ (prefixWord ++ tailWord_4694240).sum := by decide
  have hdescent : baseEnd_4694240 < baseStart_4694240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694250 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_4694250 : Nat := 118140960795 + 4694250 * 2 ^ 59
def prefixEnd_4694250 : Nat := 4983230072969 + 3 ^ 40 * 4694250 * 2
def baseEnd_4694250 : Nat := 2410406562368363958986543

theorem tailTrace_4694250 : CollatzResearch.WordTrace tailWord_4694250 prefixEnd_4694250 2410406562368363958986543 := by
  unfold tailWord_4694250
  simp only [CollatzResearch.WordTrace]
  refine ⟨42803340810885359729348051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114142242162360959278261469 42803340810885359729348051)
  ·
    refine ⟨64205011216328039594022077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42803340810885359729348051 64205011216328039594022077)
    ·
      refine ⟨24076879206123014847758279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64205011216328039594022077 24076879206123014847758279)
      ·
        refine ⟨36115318809184522271637419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24076879206123014847758279 36115318809184522271637419)
        ·
          refine ⟨54172978213776783407456129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36115318809184522271637419 54172978213776783407456129)
          ·
            refine ⟨40629733660332587555592097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54172978213776783407456129 40629733660332587555592097)
            ·
              refine ⟨30472300245249440666694073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40629733660332587555592097 30472300245249440666694073)
              ·
                refine ⟨22854225183937080500020555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30472300245249440666694073 22854225183937080500020555)
                ·
                  refine ⟨34281337775905620750030833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22854225183937080500020555 34281337775905620750030833)
                  ·
                    refine ⟨25711003331929215562523125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34281337775905620750030833 25711003331929215562523125)
                    ·
                      refine ⟨2410406562368363958986543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25711003331929215562523125 2410406562368363958986543)
                      ·
                        rfl

theorem cell23_4694250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_4694250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694250 prefixEnd_4694250 := by exact prefixLift 4694250
  have htrace : WordTrace (prefixWord ++ tailWord_4694250) baseStart_4694250 baseEnd_4694250 := by
    simpa [prefixWord, tailWord_4694250, baseEnd_4694250] using wordTrace_append hprefix tailTrace_4694250
  have hstable : (prefixWord ++ tailWord_4694250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694250).length < 2 ^ (prefixWord ++ tailWord_4694250).sum := by decide
  have hdescent : baseEnd_4694250 < baseStart_4694250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694321 : List Nat := [1, 2, 2, 3, 4, 1, 1, 4, 1, 4]
def baseStart_4694321 : Nat := 118140960795 + 4694321 * 2 ^ 59
def prefixEnd_4694321 : Nat := 4983230072969 + 3 ^ 40 * 4694321 * 2
def baseEnd_4694321 : Nat := 803481006498277727066239

theorem tailTrace_4694321 : CollatzResearch.WordTrace tailWord_4694321 prefixEnd_4694321 803481006498277727066239 := by
  unfold tailWord_4694321
  simp only [CollatzResearch.WordTrace]
  refine ⟨171215952826284218043226817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114143968550856145362151211 171215952826284218043226817)
  ·
    refine ⟨128411964619713163532420113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171215952826284218043226817 128411964619713163532420113)
    ·
      refine ⟨96308973464784872649315085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128411964619713163532420113 96308973464784872649315085)
      ·
        refine ⟨36115865049294327243493157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96308973464784872649315085 36115865049294327243493157)
        ·
          refine ⟨6771724696742686358154967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36115865049294327243493157 6771724696742686358154967)
          ·
            refine ⟨10157587045114029537232451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771724696742686358154967 10157587045114029537232451)
            ·
              refine ⟨15236380567671044305848677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157587045114029537232451 15236380567671044305848677)
              ·
                refine ⟨2856821356438320807346627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15236380567671044305848677 2856821356438320807346627)
                ·
                  refine ⟨4285232034657481211019941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856821356438320807346627 4285232034657481211019941)
                  ·
                    refine ⟨803481006498277727066239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285232034657481211019941 803481006498277727066239)
                    ·
                      rfl

theorem cell23_4694321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_4694321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694321 prefixEnd_4694321 := by exact prefixLift 4694321
  have htrace : WordTrace (prefixWord ++ tailWord_4694321) baseStart_4694321 baseEnd_4694321 := by
    simpa [prefixWord, tailWord_4694321, baseEnd_4694321] using wordTrace_append hprefix tailTrace_4694321
  have hstable : (prefixWord ++ tailWord_4694321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694321).length < 2 ^ (prefixWord ++ tailWord_4694321).sum := by decide
  have hdescent : baseEnd_4694321 < baseStart_4694321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694327 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_4694327 : Nat := 118140960795 + 4694327 * 2 ^ 59
def prefixEnd_4694327 : Nat := 4983230072969 + 3 ^ 40 * 4694327 * 2
def baseEnd_4694327 : Nat := 2410446100378760157723689

theorem tailTrace_4694327 : CollatzResearch.WordTrace tailWord_4694327 prefixEnd_4694327 2410446100378760157723689 := by
  unfold tailWord_4694327
  simp only [CollatzResearch.WordTrace]
  refine ⟨171216171664262481067945235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114144114442841654045296823 171216171664262481067945235)
  ·
    refine ⟨256824257496393721601917853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171216171664262481067945235 256824257496393721601917853)
    ·
      refine ⟨96309096561147645600719195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256824257496393721601917853 96309096561147645600719195)
      ·
        refine ⟨144463644841721468401078793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96309096561147645600719195 144463644841721468401078793)
        ·
          refine ⟨108347733631291101300809095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144463644841721468401078793 108347733631291101300809095)
          ·
            refine ⟨162521600446936651951213643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108347733631291101300809095 162521600446936651951213643)
            ·
              refine ⟨243782400670404977926820465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162521600446936651951213643 243782400670404977926820465)
              ·
                refine ⟨182836800502803733445115349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243782400670404977926820465 182836800502803733445115349)
                ·
                  refine ⟨4285237511784462502619891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182836800502803733445115349 4285237511784462502619891)
                  ·
                    refine ⟨6427856267676693753929837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285237511784462502619891 6427856267676693753929837)
                    ·
                      refine ⟨2410446100378760157723689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427856267676693753929837 2410446100378760157723689)
                      ·
                        rfl

theorem cell23_4694327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_4694327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694327 prefixEnd_4694327 := by exact prefixLift 4694327
  have htrace : WordTrace (prefixWord ++ tailWord_4694327) baseStart_4694327 baseEnd_4694327 := by
    simpa [prefixWord, tailWord_4694327, baseEnd_4694327] using wordTrace_append hprefix tailTrace_4694327
  have hstable : (prefixWord ++ tailWord_4694327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694327).length < 2 ^ (prefixWord ++ tailWord_4694327).sum := by decide
  have hdescent : baseEnd_4694327 < baseStart_4694327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694360 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 6]
def baseStart_4694360 : Nat := 118140960795 + 4694360 * 2 ^ 59
def prefixEnd_4694360 : Nat := 4983230072969 + 3 ^ 40 * 4694360 * 2
def baseEnd_4694360 : Nat := 803487681746786176203679

theorem tailTrace_4694360 : CollatzResearch.WordTrace tailWord_4694360 prefixEnd_4694360 803487681746786176203679 := by
  unfold tailWord_4694360
  simp only [CollatzResearch.WordTrace]
  refine ⟨85608687636571463851948267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114144916848761951802597689 85608687636571463851948267)
  ·
    refine ⟨128413031454857195777922401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85608687636571463851948267 128413031454857195777922401)
    ·
      refine ⟨96309773591142896833441801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128413031454857195777922401 96309773591142896833441801)
      ·
        refine ⟨72232330193357172625081351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96309773591142896833441801 72232330193357172625081351)
        ·
          refine ⟨108348495290035758937622027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72232330193357172625081351 108348495290035758937622027)
          ·
            refine ⟨162522742935053638406433041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108348495290035758937622027 162522742935053638406433041)
            ·
              refine ⟨121892057201290228804824781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162522742935053638406433041 121892057201290228804824781)
              ·
                refine ⟨45709521450483835801809293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121892057201290228804824781 45709521450483835801809293)
                ·
                  refine ⟨17141070543931438425678485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45709521450483835801809293 17141070543931438425678485)
                  ·
                    refine ⟨803487681746786176203679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17141070543931438425678485 803487681746786176203679)
                    ·
                      rfl

theorem cell23_4694360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_4694360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694360 prefixEnd_4694360 := by exact prefixLift 4694360
  have htrace : WordTrace (prefixWord ++ tailWord_4694360) baseStart_4694360 baseEnd_4694360 := by
    simpa [prefixWord, tailWord_4694360, baseEnd_4694360] using wordTrace_append hprefix tailTrace_4694360
  have hstable : (prefixWord ++ tailWord_4694360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694360).length < 2 ^ (prefixWord ++ tailWord_4694360).sum := by decide
  have hdescent : baseEnd_4694360 < baseStart_4694360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694377 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_4694377 : Nat := 118140960795 + 4694377 * 2 ^ 59
def prefixEnd_4694377 : Nat := 4983230072969 + 3 ^ 40 * 4694377 * 2
def baseEnd_4694377 : Nat := 803490591470494987366153

theorem tailTrace_4694377 : CollatzResearch.WordTrace tailWord_4694377 prefixEnd_4694377 803490591470494987366153 := by
  unfold tailWord_4694377
  simp only [CollatzResearch.WordTrace]
  refine ⟨171217995314081339607265385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114145330209387559738176923 171217995314081339607265385)
  ·
    refine ⟨128413496485561004705449039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171217995314081339607265385 128413496485561004705449039)
    ·
      refine ⟨192620244728341507058173559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128413496485561004705449039 192620244728341507058173559)
      ·
        refine ⟨288930367092512260587260339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192620244728341507058173559 288930367092512260587260339)
        ·
          refine ⟨433395550638768390880890509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288930367092512260587260339 433395550638768390880890509)
          ·
            refine ⟨162523331489538146580333941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433395550638768390880890509 162523331489538146580333941)
            ·
              refine ⟨15236562327144201241906307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162523331489538146580333941 15236562327144201241906307)
              ·
                refine ⟨22854843490716301862859461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236562327144201241906307 22854843490716301862859461)
                ·
                  refine ⟨4285283154509306599286149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22854843490716301862859461 4285283154509306599286149)
                  ·
                    refine ⟨803490591470494987366153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285283154509306599286149 803490591470494987366153)
                    ·
                      rfl

theorem cell23_4694377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_4694377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694377 prefixEnd_4694377 := by exact prefixLift 4694377
  have htrace : WordTrace (prefixWord ++ tailWord_4694377) baseStart_4694377 baseEnd_4694377 := by
    simpa [prefixWord, tailWord_4694377, baseEnd_4694377] using wordTrace_append hprefix tailTrace_4694377
  have hstable : (prefixWord ++ tailWord_4694377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694377).length < 2 ^ (prefixWord ++ tailWord_4694377).sum := by decide
  have hdescent : baseEnd_4694377 < baseStart_4694377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694378 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_4694378 : Nat := 118140960795 + 4694378 * 2 ^ 59
def prefixEnd_4694378 : Nat := 4983230072969 + 3 ^ 40 * 4694378 * 2
def baseEnd_4694378 : Nat := 2410472287892139458185955

theorem tailTrace_4694378 : CollatzResearch.WordTrace tailWord_4694378 prefixEnd_4694378 2410472287892139458185955 := by
  unfold tailWord_4694378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42804507946769429194512947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114145354524718477852034525 42804507946769429194512947)
  ·
    refine ⟨64206761920154143791769421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42804507946769429194512947 64206761920154143791769421)
    ·
      refine ⟨24077535720057803921913533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64206761920154143791769421 24077535720057803921913533)
      ·
        refine ⟨9029075895021676470717575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24077535720057803921913533 9029075895021676470717575)
        ·
          refine ⟨13543613842532514706076363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029075895021676470717575 13543613842532514706076363)
          ·
            refine ⟨20315420763798772059114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543613842532514706076363 20315420763798772059114545)
            ·
              refine ⟨15236565572849079044335909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20315420763798772059114545 15236565572849079044335909)
              ·
                refine ⟨2856856044909202320812983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15236565572849079044335909 2856856044909202320812983)
                ·
                  refine ⟨4285284067363803481219475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856856044909202320812983 4285284067363803481219475)
                  ·
                    refine ⟨6427926101045705221829213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285284067363803481219475 6427926101045705221829213)
                    ·
                      refine ⟨2410472287892139458185955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6427926101045705221829213 2410472287892139458185955)
                      ·
                        rfl

theorem cell23_4694378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_4694378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694378 prefixEnd_4694378 := by exact prefixLift 4694378
  have htrace : WordTrace (prefixWord ++ tailWord_4694378) baseStart_4694378 baseEnd_4694378 := by
    simpa [prefixWord, tailWord_4694378, baseEnd_4694378] using wordTrace_append hprefix tailTrace_4694378
  have hstable : (prefixWord ++ tailWord_4694378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694378).length < 2 ^ (prefixWord ++ tailWord_4694378).sum := by decide
  have hdescent : baseEnd_4694378 < baseStart_4694378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694397 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4694397 : Nat := 118140960795 + 4694397 * 2 ^ 59
def prefixEnd_4694397 : Nat := 4983230072969 + 3 ^ 40 * 4694397 * 2
def baseEnd_4694397 : Nat := 2410482044024574883848367

theorem tailTrace_4694397 : CollatzResearch.WordTrace tailWord_4694397 prefixEnd_4694397 2410482044024574883848367 := by
  unfold tailWord_4694397
  simp only [CollatzResearch.WordTrace]
  refine ⟨171218724774008883022993445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114145816516005922015328963 171218724774008883022993445)
  ·
    refine ⟨32103510895126665566811271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171218724774008883022993445 32103510895126665566811271)
    ·
      refine ⟨48155266342689998350216907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32103510895126665566811271 48155266342689998350216907)
      ·
        refine ⟨72232899514034997525325361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48155266342689998350216907 72232899514034997525325361)
        ·
          refine ⟨54174674635526248143994021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72232899514034997525325361 54174674635526248143994021)
          ·
            refine ⟨10157751494161171526998879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54174674635526248143994021 10157751494161171526998879)
            ·
              refine ⟨15236627241241757290498319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157751494161171526998879 15236627241241757290498319)
              ·
                refine ⟨22854940861862635935747479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236627241241757290498319 22854940861862635935747479)
                ·
                  refine ⟨34282411292793953903621219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22854940861862635935747479 34282411292793953903621219)
                  ·
                    refine ⟨51423616939190930855431829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34282411292793953903621219 51423616939190930855431829)
                    ·
                      refine ⟨2410482044024574883848367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51423616939190930855431829 2410482044024574883848367)
                      ·
                        rfl

theorem cell23_4694397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4694397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694397 prefixEnd_4694397 := by exact prefixLift 4694397
  have htrace : WordTrace (prefixWord ++ tailWord_4694397) baseStart_4694397 baseEnd_4694397 := by
    simpa [prefixWord, tailWord_4694397, baseEnd_4694397] using wordTrace_append hprefix tailTrace_4694397
  have hstable : (prefixWord ++ tailWord_4694397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694397).length < 2 ^ (prefixWord ++ tailWord_4694397).sum := by decide
  have hdescent : baseEnd_4694397 < baseStart_4694397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694401 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4694401 : Nat := 118140960795 + 4694401 * 2 ^ 59
def prefixEnd_4694401 : Nat := 4983230072969 + 3 ^ 40 * 4694401 * 2
def baseEnd_4694401 : Nat := 2410484097947192868198349

theorem tailTrace_4694401 : CollatzResearch.WordTrace tailWord_4694401 prefixEnd_4694401 2410484097947192868198349 := by
  unfold tailWord_4694401
  simp only [CollatzResearch.WordTrace]
  refine ⟨171218870665994391706139057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114145913777329594470759371 171218870665994391706139057)
  ·
    refine ⟨128414152999495793779604293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171218870665994391706139057 128414152999495793779604293)
    ·
      refine ⟨24077653687405461333675805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128414152999495793779604293 24077653687405461333675805)
      ·
        refine ⟨9029120132777048000128427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24077653687405461333675805 9029120132777048000128427)
        ·
          refine ⟨13543680199165572000192641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029120132777048000128427 13543680199165572000192641)
          ·
            refine ⟨10157760149374179000144481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13543680199165572000192641 10157760149374179000144481)
            ·
              refine ⟨7618320112030634250108361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10157760149374179000144481 7618320112030634250108361)
              ·
                refine ⟨5713740084022975687581271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618320112030634250108361 5713740084022975687581271)
                ·
                  refine ⟨8570610126034463531371907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713740084022975687581271 8570610126034463531371907)
                  ·
                    refine ⟨12855915189051695297057861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8570610126034463531371907 12855915189051695297057861)
                    ·
                      refine ⟨2410484097947192868198349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12855915189051695297057861 2410484097947192868198349)
                      ·
                        rfl

theorem cell23_4694401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4694401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694401 prefixEnd_4694401 := by exact prefixLift 4694401
  have htrace : WordTrace (prefixWord ++ tailWord_4694401) baseStart_4694401 baseEnd_4694401 := by
    simpa [prefixWord, tailWord_4694401, baseEnd_4694401] using wordTrace_append hprefix tailTrace_4694401
  have hstable : (prefixWord ++ tailWord_4694401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694401).length < 2 ^ (prefixWord ++ tailWord_4694401).sum := by decide
  have hdescent : baseEnd_4694401 < baseStart_4694401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694422 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4694422 : Nat := 118140960795 + 4694422 * 2 ^ 59
def prefixEnd_4694422 : Nat := 4983230072969 + 3 ^ 40 * 4694422 * 2
def baseEnd_4694422 : Nat := 2410494881040937286035753

theorem tailTrace_4694422 : CollatzResearch.WordTrace tailWord_4694422 prefixEnd_4694422 2410494881040937286035753 := by
  unfold tailWord_4694422
  simp only [CollatzResearch.WordTrace]
  refine ⟨10701227287432394518290845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114146424399278874861769013 10701227287432394518290845)
  ·
    refine ⟨4012960232787147944359067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10701227287432394518290845 4012960232787147944359067)
    ·
      refine ⟨6019440349180721916538601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012960232787147944359067 6019440349180721916538601)
      ·
        refine ⟨4514580261885541437403951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019440349180721916538601 4514580261885541437403951)
        ·
          refine ⟨6771870392828312156105927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514580261885541437403951 6771870392828312156105927)
          ·
            refine ⟨10157805589242468234158891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6771870392828312156105927 10157805589242468234158891)
            ·
              refine ⟨15236708383863702351238337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157805589242468234158891 15236708383863702351238337)
              ·
                refine ⟨11427531287897776763428753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15236708383863702351238337 11427531287897776763428753)
                ·
                  refine ⟨8570648465923332572571565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11427531287897776763428753 8570648465923332572571565)
                  ·
                    refine ⟨3213993174721249714714337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8570648465923332572571565 3213993174721249714714337)
                    ·
                      refine ⟨2410494881040937286035753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3213993174721249714714337 2410494881040937286035753)
                      ·
                        rfl

theorem cell23_4694422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4694422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694422 prefixEnd_4694422 := by exact prefixLift 4694422
  have htrace : WordTrace (prefixWord ++ tailWord_4694422) baseStart_4694422 baseEnd_4694422 := by
    simpa [prefixWord, tailWord_4694422, baseEnd_4694422] using wordTrace_append hprefix tailTrace_4694422
  have hstable : (prefixWord ++ tailWord_4694422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694422).length < 2 ^ (prefixWord ++ tailWord_4694422).sum := by decide
  have hdescent : baseEnd_4694422 < baseStart_4694422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694435 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 1, 2, 2]
def baseStart_4694435 : Nat := 118140960795 + 4694435 * 2 ^ 59
def prefixEnd_4694435 : Nat := 4983230072969 + 3 ^ 40 * 4694435 * 2
def baseEnd_4694435 : Nat := 2410501556289445735173193

theorem tailTrace_4694435 : CollatzResearch.WordTrace tailWord_4694435 prefixEnd_4694435 2410501556289445735173193 := by
  unfold tailWord_4694435
  simp only [CollatzResearch.WordTrace]
  refine ⟨171220110747871215512876759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114146740498580810341917839 171220110747871215512876759)
  ·
    refine ⟨256830166121806823269315139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171220110747871215512876759 256830166121806823269315139)
    ·
      refine ⟨385245249182710234903972709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256830166121806823269315139 385245249182710234903972709)
      ·
        refine ⟨72233484221758169044494883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385245249182710234903972709 72233484221758169044494883)
        ·
          refine ⟨108350226332637253566742325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72233484221758169044494883 108350226332637253566742325)
          ·
            refine ⟨10157833718684742521882093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108350226332637253566742325 10157833718684742521882093)
            ·
              refine ⟨3809187644506778445705785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10157833718684742521882093 3809187644506778445705785)
              ·
                refine ⟨2856890733380083834279339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809187644506778445705785 2856890733380083834279339)
                ·
                  refine ⟨4285336100070125751419009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856890733380083834279339 4285336100070125751419009)
                  ·
                    refine ⟨3214002075052594313564257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285336100070125751419009 3214002075052594313564257)
                    ·
                      refine ⟨2410501556289445735173193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214002075052594313564257 2410501556289445735173193)
                      ·
                        rfl

theorem cell23_4694435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_4694435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694435 prefixEnd_4694435 := by exact prefixLift 4694435
  have htrace : WordTrace (prefixWord ++ tailWord_4694435) baseStart_4694435 baseEnd_4694435 := by
    simpa [prefixWord, tailWord_4694435, baseEnd_4694435] using wordTrace_append hprefix tailTrace_4694435
  have hstable : (prefixWord ++ tailWord_4694435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694435).length < 2 ^ (prefixWord ++ tailWord_4694435).sum := by decide
  have hdescent : baseEnd_4694435 < baseStart_4694435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694444 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_4694444 : Nat := 118140960795 + 4694444 * 2 ^ 59
def prefixEnd_4694444 : Nat := 4983230072969 + 3 ^ 40 * 4694444 * 2
def baseEnd_4694444 : Nat := 2410506177615336199960651

theorem tailTrace_4694444 : CollatzResearch.WordTrace tailWord_4694444 prefixEnd_4694444 2410506177615336199960651 := by
  unfold tailWord_4694444
  simp only [CollatzResearch.WordTrace]
  refine ⟨85610219502419305024977193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114146959336559073366636257 85610219502419305024977193)
  ·
    refine ⟨64207664626814478768732895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85610219502419305024977193 64207664626814478768732895)
    ·
      refine ⟨96311496940221718153099343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64207664626814478768732895 96311496940221718153099343)
      ·
        refine ⟨144467245410332577229649015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96311496940221718153099343 144467245410332577229649015)
        ·
          refine ⟨216700868115498865844473523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144467245410332577229649015 216700868115498865844473523)
          ·
            refine ⟨325051302173248298766710285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216700868115498865844473523 325051302173248298766710285)
            ·
              refine ⟨121894238314968112037516357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325051302173248298766710285 121894238314968112037516357)
              ·
                refine ⟨22855169684056521007034317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121894238314968112037516357 22855169684056521007034317)
                ·
                  refine ⟨8570688631521195377637869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22855169684056521007034317 8570688631521195377637869)
                  ·
                    refine ⟨3214008236820448266614201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8570688631521195377637869 3214008236820448266614201)
                    ·
                      refine ⟨2410506177615336199960651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214008236820448266614201 2410506177615336199960651)
                      ·
                        rfl

theorem cell23_4694444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_4694444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694444 prefixEnd_4694444 := by exact prefixLift 4694444
  have htrace : WordTrace (prefixWord ++ tailWord_4694444) baseStart_4694444 baseEnd_4694444 := by
    simpa [prefixWord, tailWord_4694444, baseEnd_4694444] using wordTrace_append hprefix tailTrace_4694444
  have hstable : (prefixWord ++ tailWord_4694444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694444).length < 2 ^ (prefixWord ++ tailWord_4694444).sum := by decide
  have hdescent : baseEnd_4694444 < baseStart_4694444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694445 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4694445 : Nat := 118140960795 + 4694445 * 2 ^ 59
def prefixEnd_4694445 : Nat := 4983230072969 + 3 ^ 40 * 4694445 * 2
def baseEnd_4694445 : Nat := 803502230365330232016049

theorem tailTrace_4694445 : CollatzResearch.WordTrace tailWord_4694445 prefixEnd_4694445 803502230365330232016049 := by
  unfold tailWord_4694445
  simp only [CollatzResearch.WordTrace]
  refine ⟨171220475477834987220740789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114146983651889991480493859 171220475477834987220740789)
  ·
    refine ⟨16051919576047030051944449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171220475477834987220740789 16051919576047030051944449)
    ·
      refine ⟨12038939682035272538958337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16051919576047030051944449 12038939682035272538958337)
      ·
        refine ⟨9029204761526454404218753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12038939682035272538958337 9029204761526454404218753)
        ·
          refine ⟨6771903571144840803164065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9029204761526454404218753 6771903571144840803164065)
          ·
            refine ⟨5078927678358630602373049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6771903571144840803164065 5078927678358630602373049)
            ·
              refine ⟨3809195758768972951779787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078927678358630602373049 3809195758768972951779787)
              ·
                refine ⟨5713793638153459427669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809195758768972951779787 5713793638153459427669681)
                ·
                  refine ⟨4285345228615094570752261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713793638153459427669681 4285345228615094570752261)
                  ·
                    refine ⟨803502230365330232016049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285345228615094570752261 803502230365330232016049)
                    ·
                      rfl

theorem cell23_4694445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4694445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694445 prefixEnd_4694445 := by exact prefixLift 4694445
  have htrace : WordTrace (prefixWord ++ tailWord_4694445) baseStart_4694445 baseEnd_4694445 := by
    simpa [prefixWord, tailWord_4694445, baseEnd_4694445] using wordTrace_append hprefix tailTrace_4694445
  have hstable : (prefixWord ++ tailWord_4694445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694445).length < 2 ^ (prefixWord ++ tailWord_4694445).sum := by decide
  have hdescent : baseEnd_4694445 < baseStart_4694445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694452 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4694452 : Nat := 118140960795 + 4694452 * 2 ^ 59
def prefixEnd_4694452 : Nat := 4983230072969 + 3 ^ 40 * 4694452 * 2
def baseEnd_4694452 : Nat := 2410510285460572168660615

theorem tailTrace_4694452 : CollatzResearch.WordTrace tailWord_4694452 prefixEnd_4694452 2410510285460572168660615 := by
  unfold tailWord_4694452
  simp only [CollatzResearch.WordTrace]
  refine ⟨85610365394404813708122805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114147153859206418277497073 85610365394404813708122805)
  ·
    refine ⟨8025971755725451285136513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85610365394404813708122805 8025971755725451285136513)
    ·
      refine ⟨6019478816794088463852385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8025971755725451285136513 6019478816794088463852385)
      ·
        refine ⟨4514609112595566347889289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6019478816794088463852385 4514609112595566347889289)
        ·
          refine ⟨3385956834446674760916967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514609112595566347889289 3385956834446674760916967)
          ·
            refine ⟨5078935251670012141375451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385956834446674760916967 5078935251670012141375451)
            ·
              refine ⟨7618402877505018212063177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078935251670012141375451 7618402877505018212063177)
              ·
                refine ⟨5713802158128763659047383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618402877505018212063177 5713802158128763659047383)
                ·
                  refine ⟨8570703237193145488571075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713802158128763659047383 8570703237193145488571075)
                  ·
                    refine ⟨12856054855789718232856613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8570703237193145488571075 12856054855789718232856613)
                    ·
                      refine ⟨2410510285460572168660615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12856054855789718232856613 2410510285460572168660615)
                      ·
                        rfl

theorem cell23_4694452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4694452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694452 prefixEnd_4694452 := by exact prefixLift 4694452
  have htrace : WordTrace (prefixWord ++ tailWord_4694452) baseStart_4694452 baseEnd_4694452 := by
    simpa [prefixWord, tailWord_4694452, baseEnd_4694452] using wordTrace_append hprefix tailTrace_4694452
  have hstable : (prefixWord ++ tailWord_4694452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694452).length < 2 ^ (prefixWord ++ tailWord_4694452).sum := by decide
  have hdescent : baseEnd_4694452 < baseStart_4694452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694461 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4694461 : Nat := 118140960795 + 4694461 * 2 ^ 59
def prefixEnd_4694461 : Nat := 4983230072969 + 3 ^ 40 * 4694461 * 2
def baseEnd_4694461 : Nat := 2410514906786462633448073

theorem tailTrace_4694461 : CollatzResearch.WordTrace tailWord_4694461 prefixEnd_4694461 2410514906786462633448073 := by
  unfold tailWord_4694461
  simp only [CollatzResearch.WordTrace]
  refine ⟨171221059045777021953323237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114147372697184681302215491 171221059045777021953323237)
  ·
    refine ⟨32103948571083191616248107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171221059045777021953323237 32103948571083191616248107)
    ·
      refine ⟨48155922856624787424372161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32103948571083191616248107 48155922856624787424372161)
      ·
        refine ⟨36116942142468590568279121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48155922856624787424372161 36116942142468590568279121)
        ·
          refine ⟨27087706606851442926209341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36116942142468590568279121 27087706606851442926209341)
          ·
            refine ⟨10157889977569291097328503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27087706606851442926209341 10157889977569291097328503)
            ·
              refine ⟨15236834966353936645992755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157889977569291097328503 15236834966353936645992755)
              ·
                refine ⟨22855252449530904968989133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236834966353936645992755 22855252449530904968989133)
                ·
                  refine ⟨8570719668574089363370925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22855252449530904968989133 8570719668574089363370925)
                  ·
                    refine ⟨3214019875715283511264097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8570719668574089363370925 3214019875715283511264097)
                    ·
                      refine ⟨2410514906786462633448073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214019875715283511264097 2410514906786462633448073)
                      ·
                        rfl

theorem cell23_4694461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4694461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694461 prefixEnd_4694461 := by exact prefixLift 4694461
  have htrace : WordTrace (prefixWord ++ tailWord_4694461) baseStart_4694461 baseEnd_4694461 := by
    simpa [prefixWord, tailWord_4694461, baseEnd_4694461] using wordTrace_append hprefix tailTrace_4694461
  have hstable : (prefixWord ++ tailWord_4694461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694461).length < 2 ^ (prefixWord ++ tailWord_4694461).sum := by decide
  have hdescent : baseEnd_4694461 < baseStart_4694461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694497 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 7]
def baseStart_4694497 : Nat := 118140960795 + 4694497 * 2 ^ 59
def prefixEnd_4694497 : Nat := 4983230072969 + 3 ^ 40 * 4694497 * 2
def baseEnd_4694497 : Nat := 267837043565558276955323

theorem tailTrace_4694497 : CollatzResearch.WordTrace tailWord_4694497 prefixEnd_4694497 267837043565558276955323 := by
  unfold tailWord_4694497
  simp only [CollatzResearch.WordTrace]
  refine ⟨171222372073646600101633745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114148248049097733401089163 171222372073646600101633745)
  ·
    refine ⟨128416779055234950076225309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171222372073646600101633745 128416779055234950076225309)
    ·
      refine ⟨48156292145713106278584491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128416779055234950076225309 48156292145713106278584491)
      ·
        refine ⟨72234438218569659417876737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48156292145713106278584491 72234438218569659417876737)
        ·
          refine ⟨54175828663927244563407553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72234438218569659417876737 54175828663927244563407553)
          ·
            refine ⟨40631871497945433422555665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54175828663927244563407553 40631871497945433422555665)
            ·
              refine ⟨30473903623459075066916749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40631871497945433422555665 30473903623459075066916749)
              ·
                refine ⟨11427713858797153150093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30473903623459075066916749 11427713858797153150093781)
                ·
                  refine ⟨267837043565558276955323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11427713858797153150093781 267837043565558276955323)
                  ·
                    rfl

theorem cell23_4694497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_4694497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694497 prefixEnd_4694497 := by exact prefixLift 4694497
  have htrace : WordTrace (prefixWord ++ tailWord_4694497) baseStart_4694497 baseEnd_4694497 := by
    simpa [prefixWord, tailWord_4694497, baseEnd_4694497] using wordTrace_append hprefix tailTrace_4694497
  have hstable : (prefixWord ++ tailWord_4694497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694497).length < 2 ^ (prefixWord ++ tailWord_4694497).sum := by decide
  have hdescent : baseEnd_4694497 < baseStart_4694497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694504 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4694504 : Nat := 118140960795 + 4694504 * 2 ^ 59
def prefixEnd_4694504 : Nat := 4983230072969 + 3 ^ 40 * 4694504 * 2
def baseEnd_4694504 : Nat := 2410536986454605965210375

theorem tailTrace_4694504 : CollatzResearch.WordTrace tailWord_4694504 prefixEnd_4694504 2410536986454605965210375 := by
  unfold tailWord_4694504
  simp only [CollatzResearch.WordTrace]
  refine ⟨85611313692310620148569283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114148418256414160198092377 85611313692310620148569283)
  ·
    refine ⟨128416970538465930222853925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85611313692310620148569283 128416970538465930222853925)
    ·
      refine ⟨24078181975962361916785111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128416970538465930222853925 24078181975962361916785111)
      ·
        refine ⟨36117272963943542875177667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24078181975962361916785111 36117272963943542875177667)
        ·
          refine ⟨54175909445915314312766501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36117272963943542875177667 54175909445915314312766501)
          ·
            refine ⟨10157983021109121433643719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54175909445915314312766501 10157983021109121433643719)
            ·
              refine ⟨15236974531663682150465579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157983021109121433643719 15236974531663682150465579)
              ·
                refine ⟨22855461797495523225698369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15236974531663682150465579 22855461797495523225698369)
                ·
                  refine ⟨17141596348121642419273777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22855461797495523225698369 17141596348121642419273777)
                  ·
                    refine ⟨12856197261091231814455333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17141596348121642419273777 12856197261091231814455333)
                    ·
                      refine ⟨2410536986454605965210375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12856197261091231814455333 2410536986454605965210375)
                      ·
                        rfl

theorem cell23_4694504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4694504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694504 prefixEnd_4694504 := by exact prefixLift 4694504
  have htrace : WordTrace (prefixWord ++ tailWord_4694504) baseStart_4694504 baseEnd_4694504 := by
    simpa [prefixWord, tailWord_4694504, baseEnd_4694504] using wordTrace_append hprefix tailTrace_4694504
  have hstable : (prefixWord ++ tailWord_4694504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694504).length < 2 ^ (prefixWord ++ tailWord_4694504).sum := by decide
  have hdescent : baseEnd_4694504 < baseStart_4694504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694527 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 7]
def baseStart_4694527 : Nat := 118140960795 + 4694527 * 2 ^ 59
def prefixEnd_4694527 : Nat := 4983230072969 + 3 ^ 40 * 4694527 * 2
def baseEnd_4694527 : Nat := 803516265503219791740923

theorem tailTrace_4694527 : CollatzResearch.WordTrace tailWord_4694527 prefixEnd_4694527 803516265503219791740923 := by
  unfold tailWord_4694527
  simp only [CollatzResearch.WordTrace]
  refine ⟨171223466263537915225225835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114148977509025276816817223 171223466263537915225225835)
  ·
    refine ⟨256835199395306872837838753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171223466263537915225225835 256835199395306872837838753)
    ·
      refine ⟨192626399546480154628379065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256835199395306872837838753 192626399546480154628379065)
      ·
        refine ⟨144469799659860115971284299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192626399546480154628379065 144469799659860115971284299)
        ·
          refine ⟨216704699489790173956926449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144469799659860115971284299 216704699489790173956926449)
          ·
            refine ⟨162528524617342630467694837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216704699489790173956926449 162528524617342630467694837)
            ·
              refine ⟨15237049182875871606346391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162528524617342630467694837 15237049182875871606346391)
              ·
                refine ⟨22855573774313807409519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15237049182875871606346391 22855573774313807409519587)
                ·
                  refine ⟨34283360661470711114279381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22855573774313807409519587 34283360661470711114279381)
                  ·
                    refine ⟨803516265503219791740923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34283360661470711114279381 803516265503219791740923)
                    ·
                      rfl

theorem cell23_4694527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_4694527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694527 prefixEnd_4694527 := by exact prefixLift 4694527
  have htrace : WordTrace (prefixWord ++ tailWord_4694527) baseStart_4694527 baseEnd_4694527 := by
    simpa [prefixWord, tailWord_4694527, baseEnd_4694527] using wordTrace_append hprefix tailTrace_4694527
  have hstable : (prefixWord ++ tailWord_4694527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694527).length < 2 ^ (prefixWord ++ tailWord_4694527).sum := by decide
  have hdescent : baseEnd_4694527 < baseStart_4694527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694537 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_4694537 : Nat := 118140960795 + 4694537 * 2 ^ 59
def prefixEnd_4694537 : Nat := 4983230072969 + 3 ^ 40 * 4694537 * 2
def baseEnd_4694537 : Nat := 2410553931316204336097723

theorem tailTrace_4694537 : CollatzResearch.WordTrace tailWord_4694537 prefixEnd_4694537 2410553931316204336097723 := by
  unfold tailWord_4694537
  simp only [CollatzResearch.WordTrace]
  refine ⟨171223830993501686933089865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114149220662334457955393243 171223830993501686933089865)
  ·
    refine ⟨128417873245126265199817399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171223830993501686933089865 128417873245126265199817399)
    ·
      refine ⟨192626809867689397799726099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128417873245126265199817399 192626809867689397799726099)
      ·
        refine ⟨288940214801534096699589149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192626809867689397799726099 288940214801534096699589149)
        ·
          refine ⟨108352580550575286262345931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288940214801534096699589149 108352580550575286262345931)
          ·
            refine ⟨162528870825862929393518897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108352580550575286262345931 162528870825862929393518897)
            ·
              refine ⟨121896653119397197045139173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162528870825862929393518897 121896653119397197045139173)
              ·
                refine ⟨22855622459886974445963595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121896653119397197045139173 22855622459886974445963595)
                ·
                  refine ⟨34283433689830461668945393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22855622459886974445963595 34283433689830461668945393)
                  ·
                    refine ⟨25712575267372846251709045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34283433689830461668945393 25712575267372846251709045)
                    ·
                      refine ⟨2410553931316204336097723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25712575267372846251709045 2410553931316204336097723)
                      ·
                        rfl

theorem cell23_4694537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_4694537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694537 prefixEnd_4694537 := by exact prefixLift 4694537
  have htrace : WordTrace (prefixWord ++ tailWord_4694537) baseStart_4694537 baseEnd_4694537 := by
    simpa [prefixWord, tailWord_4694537, baseEnd_4694537] using wordTrace_append hprefix tailTrace_4694537
  have hstable : (prefixWord ++ tailWord_4694537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694537).length < 2 ^ (prefixWord ++ tailWord_4694537).sum := by decide
  have hdescent : baseEnd_4694537 < baseStart_4694537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694548 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 5]
def baseStart_4694548 : Nat := 118140960795 + 4694548 * 2 ^ 59
def prefixEnd_4694548 : Nat := 4983230072969 + 3 ^ 40 * 4694548 * 2
def baseEnd_4694548 : Nat := 267839953289267088117797

theorem tailTrace_4694548 : CollatzResearch.WordTrace tailWord_4694548 prefixEnd_4694548 267839953289267088117797 := by
  unfold tailWord_4694548
  simp only [CollatzResearch.WordTrace]
  refine ⟨85612116098230917905870149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114149488130974557207826865 85612116098230917905870149)
  ·
    refine ⟨16052271768418297107350653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85612116098230917905870149 16052271768418297107350653)
    ·
      refine ⟨6019601913156861415256495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16052271768418297107350653 6019601913156861415256495)
      ·
        refine ⟨9029402869735292122884743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019601913156861415256495 9029402869735292122884743)
        ·
          refine ⟨13544104304602938184327115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029402869735292122884743 13544104304602938184327115)
          ·
            refine ⟨20316156456904407276490673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544104304602938184327115 20316156456904407276490673)
            ·
              refine ⟨15237117342678305457368005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20316156456904407276490673 15237117342678305457368005)
              ·
                refine ⟨2856959501752182273256501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15237117342678305457368005 2856959501752182273256501)
                ·
                  refine ⟨267839953289267088117797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856959501752182273256501 267839953289267088117797)
                  ·
                    rfl

theorem cell23_4694548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_4694548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694548 prefixEnd_4694548 := by exact prefixLift 4694548
  have htrace : WordTrace (prefixWord ++ tailWord_4694548) baseStart_4694548 baseEnd_4694548 := by
    simpa [prefixWord, tailWord_4694548, baseEnd_4694548] using wordTrace_append hprefix tailTrace_4694548
  have hstable : (prefixWord ++ tailWord_4694548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694548).length < 2 ^ (prefixWord ++ tailWord_4694548).sum := by decide
  have hdescent : baseEnd_4694548 < baseStart_4694548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694584 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_4694584 : Nat := 118140960795 + 4694584 * 2 ^ 59
def prefixEnd_4694584 : Nat := 4983230072969 + 3 ^ 40 * 4694584 * 2
def baseEnd_4694584 : Nat := 2410578064906965652210007

theorem tailTrace_4694584 : CollatzResearch.WordTrace tailWord_4694584 prefixEnd_4694584 2410578064906965652210007 := by
  unfold tailWord_4694584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85612772612165706980025403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114150363482887609306700537 85612772612165706980025403)
  ·
    refine ⟨128419158918248560470038105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85612772612165706980025403 128419158918248560470038105)
    ·
      refine ⟨96314369188686420352528579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128419158918248560470038105 96314369188686420352528579)
      ·
        refine ⟨144471553783029630528792869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96314369188686420352528579 144471553783029630528792869)
        ·
          refine ⟨27088416334318055724148663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144471553783029630528792869 27088416334318055724148663)
          ·
            refine ⟨40632624501477083586222995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27088416334318055724148663 40632624501477083586222995)
            ·
              refine ⟨60948936752215625379334493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40632624501477083586222995 60948936752215625379334493)
              ·
                refine ⟨22855851282080859517250435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60948936752215625379334493 22855851282080859517250435)
                ·
                  refine ⟨34283776923121289275875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22855851282080859517250435 34283776923121289275875653)
                  ·
                    refine ⟨6428208173085241739226685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34283776923121289275875653 6428208173085241739226685)
                    ·
                      refine ⟨2410578064906965652210007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428208173085241739226685 2410578064906965652210007)
                      ·
                        rfl

theorem cell23_4694584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_4694584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694584 prefixEnd_4694584 := by exact prefixLift 4694584
  have htrace : WordTrace (prefixWord ++ tailWord_4694584) baseStart_4694584 baseEnd_4694584 := by
    simpa [prefixWord, tailWord_4694584, baseEnd_4694584] using wordTrace_append hprefix tailTrace_4694584
  have hstable : (prefixWord ++ tailWord_4694584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694584).length < 2 ^ (prefixWord ++ tailWord_4694584).sum := by decide
  have hdescent : baseEnd_4694584 < baseStart_4694584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694598 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4694598 : Nat := 118140960795 + 4694598 * 2 ^ 59
def prefixEnd_4694598 : Nat := 4983230072969 + 3 ^ 40 * 4694598 * 2
def baseEnd_4694598 : Nat := 2410585253636128597434943

theorem tailTrace_4694598 : CollatzResearch.WordTrace tailWord_4694598 prefixEnd_4694598 2410585253636128597434943 := by
  unfold tailWord_4694598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350814245196271698470639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114150703897520462900706965 5350814245196271698470639)
  ·
    refine ⟨8026221367794407547705959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350814245196271698470639 8026221367794407547705959)
    ·
      refine ⟨12039332051691611321558939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026221367794407547705959 12039332051691611321558939)
      ·
        refine ⟨18058998077537416982338409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12039332051691611321558939 18058998077537416982338409)
        ·
          refine ⟨13544248558153062736753807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18058998077537416982338409 13544248558153062736753807)
          ·
            refine ⟨20316372837229594105130711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544248558153062736753807 20316372837229594105130711)
            ·
              refine ⟨30474559255844391157696067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20316372837229594105130711 30474559255844391157696067)
              ·
                refine ⟨45711838883766586736544101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30474559255844391157696067 45711838883766586736544101)
                ·
                  refine ⟨8570969790706235013102019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45711838883766586736544101 8570969790706235013102019)
                  ·
                    refine ⟨12856454686059352519653029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8570969790706235013102019 12856454686059352519653029)
                    ·
                      refine ⟨2410585253636128597434943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12856454686059352519653029 2410585253636128597434943)
                      ·
                        rfl

theorem cell23_4694598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4694598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694598 prefixEnd_4694598 := by exact prefixLift 4694598
  have htrace : WordTrace (prefixWord ++ tailWord_4694598) baseStart_4694598 baseEnd_4694598 := by
    simpa [prefixWord, tailWord_4694598, baseEnd_4694598] using wordTrace_append hprefix tailTrace_4694598
  have hstable : (prefixWord ++ tailWord_4694598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694598).length < 2 ^ (prefixWord ++ tailWord_4694598).sum := by decide
  have hdescent : baseEnd_4694598 < baseStart_4694598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694604 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 6]
def baseStart_4694604 : Nat := 118140960795 + 4694604 * 2 ^ 59
def prefixEnd_4694604 : Nat := 4983230072969 + 3 ^ 40 * 4694604 * 2
def baseEnd_4694604 : Nat := 267843148280006174884435

theorem tailTrace_4694604 : CollatzResearch.WordTrace tailWord_4694604 prefixEnd_4694604 267843148280006174884435 := by
  unfold tailWord_4694604
  simp only [CollatzResearch.WordTrace]
  refine ⟨85613137342129478687889433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114150849789505971583852577 85613137342129478687889433)
  ·
    refine ⟨64209853006597109015917075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85613137342129478687889433 64209853006597109015917075)
    ·
      refine ⟨96314779509895663523875613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64209853006597109015917075 96314779509895663523875613)
      ·
        refine ⟨36118042316210873821453355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96314779509895663523875613 36118042316210873821453355)
        ·
          refine ⟨54177063474316310732180033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36118042316210873821453355 54177063474316310732180033)
          ·
            refine ⟨40632797605737233049135025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54177063474316310732180033 40632797605737233049135025)
            ·
              refine ⟨30474598204302924786851269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40632797605737233049135025 30474598204302924786851269)
              ·
                refine ⟨5713987163306798397534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30474598204302924786851269 5713987163306798397534613)
                ·
                  refine ⟨267843148280006174884435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5713987163306798397534613 267843148280006174884435)
                  ·
                    rfl

theorem cell23_4694604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_4694604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694604 prefixEnd_4694604 := by exact prefixLift 4694604
  have htrace : WordTrace (prefixWord ++ tailWord_4694604) baseStart_4694604 baseEnd_4694604 := by
    simpa [prefixWord, tailWord_4694604, baseEnd_4694604] using wordTrace_append hprefix tailTrace_4694604
  have hstable : (prefixWord ++ tailWord_4694604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694604).length < 2 ^ (prefixWord ++ tailWord_4694604).sum := by decide
  have hdescent : baseEnd_4694604 < baseStart_4694604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694607 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_4694607 : Nat := 118140960795 + 4694607 * 2 ^ 59
def prefixEnd_4694607 : Nat := 4983230072969 + 3 ^ 40 * 4694607 * 2
def baseEnd_4694607 : Nat := 2410589874962019062222401

theorem tailTrace_4694607 : CollatzResearch.WordTrace tailWord_4694607 prefixEnd_4694607 2410589874962019062222401 := by
  unfold tailWord_4694607
  simp only [CollatzResearch.WordTrace]
  refine ⟨171226384103248088888138075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114150922735498725925425383 171226384103248088888138075)
  ·
    refine ⟨256839576154872133332207113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171226384103248088888138075 256839576154872133332207113)
    ·
      refine ⟨192629682116154099999155335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256839576154872133332207113 192629682116154099999155335)
      ·
        refine ⟨288944523174231149998733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192629682116154099999155335 288944523174231149998733003)
        ·
          refine ⟨433416784761346724998099505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288944523174231149998733003 433416784761346724998099505)
          ·
            refine ⟨325062588571010043748574629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433416784761346724998099505 325062588571010043748574629)
            ·
              refine ⟨60949235357064383202857743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325062588571010043748574629 60949235357064383202857743)
              ·
                refine ⟨91423853035596574804286615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60949235357064383202857743 91423853035596574804286615)
                ·
                  refine ⟨137135779553394862206429923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91423853035596574804286615 137135779553394862206429923)
                  ·
                    refine ⟨205703669330092293309644885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137135779553394862206429923 205703669330092293309644885)
                    ·
                      refine ⟨2410589874962019062222401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 205703669330092293309644885 2410589874962019062222401)
                      ·
                        rfl

theorem cell23_4694607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_4694607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694607 prefixEnd_4694607 := by exact prefixLift 4694607
  have htrace : WordTrace (prefixWord ++ tailWord_4694607) baseStart_4694607 baseEnd_4694607 := by
    simpa [prefixWord, tailWord_4694607, baseEnd_4694607] using wordTrace_append hprefix tailTrace_4694607
  have hstable : (prefixWord ++ tailWord_4694607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694607).length < 2 ^ (prefixWord ++ tailWord_4694607).sum := by decide
  have hdescent : baseEnd_4694607 < baseStart_4694607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694617 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_4694617 : Nat := 118140960795 + 4694617 * 2 ^ 59
def prefixEnd_4694617 : Nat := 4983230072969 + 3 ^ 40 * 4694617 * 2
def baseEnd_4694617 : Nat := 803531669922854674365785

theorem tailTrace_4694617 : CollatzResearch.WordTrace tailWord_4694617 prefixEnd_4694617 803531669922854674365785 := by
  unfold tailWord_4694617
  simp only [CollatzResearch.WordTrace]
  refine ⟨171226748833211860596002105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114151165888807907064001403 171226748833211860596002105)
  ·
    refine ⟨128420061624908895447001579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171226748833211860596002105 128420061624908895447001579)
    ·
      refine ⟨192630092437363343170502369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128420061624908895447001579 192630092437363343170502369)
      ·
        refine ⟨144472569328022507377876777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192630092437363343170502369 144472569328022507377876777)
        ·
          refine ⟨108354426996016880533407583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144472569328022507377876777 108354426996016880533407583)
          ·
            refine ⟨162531640494025320800111375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108354426996016880533407583 162531640494025320800111375)
            ·
              refine ⟨243797460741037981200167063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162531640494025320800111375 243797460741037981200167063)
              ·
                refine ⟨365696191111556971800250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243797460741037981200167063 365696191111556971800250595)
                ·
                  refine ⟨548544286667335457700375893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365696191111556971800250595 548544286667335457700375893)
                  ·
                    refine ⟨803531669922854674365785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 548544286667335457700375893 803531669922854674365785)
                    ·
                      rfl

theorem cell23_4694617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_4694617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694617 prefixEnd_4694617 := by exact prefixLift 4694617
  have htrace : WordTrace (prefixWord ++ tailWord_4694617) baseStart_4694617 baseEnd_4694617 := by
    simpa [prefixWord, tailWord_4694617, baseEnd_4694617] using wordTrace_append hprefix tailTrace_4694617
  have hstable : (prefixWord ++ tailWord_4694617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694617).length < 2 ^ (prefixWord ++ tailWord_4694617).sum := by decide
  have hdescent : baseEnd_4694617 < baseStart_4694617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694631 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_4694631 : Nat := 118140960795 + 4694631 * 2 ^ 59
def prefixEnd_4694631 : Nat := 4983230072969 + 3 ^ 40 * 4694631 * 2
def baseEnd_4694631 : Nat := 2410602198497726968322291

theorem tailTrace_4694631 : CollatzResearch.WordTrace tailWord_4694631 prefixEnd_4694631 2410602198497726968322291 := by
  unfold tailWord_4694631
  simp only [CollatzResearch.WordTrace]
  refine ⟨171227259455161140987011747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114151506303440760658007831 171227259455161140987011747)
  ·
    refine ⟨256840889182741711480517621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171227259455161140987011747 256840889182741711480517621)
    ·
      refine ⟨24078833360882035451298527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256840889182741711480517621 24078833360882035451298527)
      ·
        refine ⟨36118250041323053176947791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24078833360882035451298527 36118250041323053176947791)
        ·
          refine ⟨54177375061984579765421687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36118250041323053176947791 54177375061984579765421687)
          ·
            refine ⟨81266062592976869648132531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54177375061984579765421687 81266062592976869648132531)
            ·
              refine ⟨121899093889465304472198797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81266062592976869648132531 121899093889465304472198797)
              ·
                refine ⟨45712160208549489177074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121899093889465304472198797 45712160208549489177074549)
                ·
                  refine ⟨4285515019551514610350739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45712160208549489177074549 4285515019551514610350739)
                  ·
                    refine ⟨6428272529327271915526109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285515019551514610350739 6428272529327271915526109)
                    ·
                      refine ⟨2410602198497726968322291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428272529327271915526109 2410602198497726968322291)
                      ·
                        rfl

theorem cell23_4694631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_4694631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694631 prefixEnd_4694631 := by exact prefixLift 4694631
  have htrace : WordTrace (prefixWord ++ tailWord_4694631) baseStart_4694631 baseEnd_4694631 := by
    simpa [prefixWord, tailWord_4694631, baseEnd_4694631] using wordTrace_append hprefix tailTrace_4694631
  have hstable : (prefixWord ++ tailWord_4694631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694631).length < 2 ^ (prefixWord ++ tailWord_4694631).sum := by decide
  have hdescent : baseEnd_4694631 < baseStart_4694631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694681 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_4694681 : Nat := 118140960795 + 4694681 * 2 ^ 59
def prefixEnd_4694681 : Nat := 4983230072969 + 3 ^ 40 * 4694681 * 2
def baseEnd_4694681 : Nat := 803542624176817257565687

theorem tailTrace_4694681 : CollatzResearch.WordTrace tailWord_4694681 prefixEnd_4694681 803542624176817257565687 := by
  unfold tailWord_4694681
  simp only [CollatzResearch.WordTrace]
  refine ⟨171229083104979999526331897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114152722069986666350887931 171229083104979999526331897)
  ·
    refine ⟨128421812328734999644748923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171229083104979999526331897 128421812328734999644748923)
    ·
      refine ⟨192632718493102499467123385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128421812328734999644748923 192632718493102499467123385)
      ·
        refine ⟨144474538869826874600342539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192632718493102499467123385 144474538869826874600342539)
        ·
          refine ⟨216711808304740311900513809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144474538869826874600342539 216711808304740311900513809)
          ·
            refine ⟨162533856228555233925385357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216711808304740311900513809 162533856228555233925385357)
            ·
              refine ⟨60950196085708212722019509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162533856228555233925385357 60950196085708212722019509)
              ·
                refine ⟨5714080883035144942689329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60950196085708212722019509 5714080883035144942689329)
                ·
                  refine ⟨4285560662276358707016997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714080883035144942689329 4285560662276358707016997)
                  ·
                    refine ⟨803542624176817257565687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285560662276358707016997 803542624176817257565687)
                    ·
                      rfl

theorem cell23_4694681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_4694681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694681 prefixEnd_4694681 := by exact prefixLift 4694681
  have htrace : WordTrace (prefixWord ++ tailWord_4694681) baseStart_4694681 baseEnd_4694681 := by
    simpa [prefixWord, tailWord_4694681, baseEnd_4694681] using wordTrace_append hprefix tailTrace_4694681
  have hstable : (prefixWord ++ tailWord_4694681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694681).length < 2 ^ (prefixWord ++ tailWord_4694681).sum := by decide
  have hdescent : baseEnd_4694681 < baseStart_4694681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694702 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4694702 : Nat := 118140960795 + 4694702 * 2 ^ 59
def prefixEnd_4694702 : Nat := 4983230072969 + 3 ^ 40 * 4694702 * 2
def baseEnd_4694702 : Nat := 803546218541398730178155

theorem tailTrace_4694702 : CollatzResearch.WordTrace tailWord_4694702 prefixEnd_4694702 803546218541398730178155 := by
  unfold tailWord_4694702
  simp only [CollatzResearch.WordTrace]
  refine ⟨21403731129737990014105795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114153232691935946741897573 21403731129737990014105795)
  ·
    refine ⟨32105596694606985021158693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21403731129737990014105795 32105596694606985021158693)
    ·
      refine ⟨6019799380238809691467255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32105596694606985021158693 6019799380238809691467255)
      ·
        refine ⟨9029699070358214537200883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019799380238809691467255 9029699070358214537200883)
        ·
          refine ⟨13544548605537321805801325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9029699070358214537200883 13544548605537321805801325)
          ·
            refine ⟨5079205727076495677175497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13544548605537321805801325 5079205727076495677175497)
            ·
              refine ⟨3809404295307371757881623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5079205727076495677175497 3809404295307371757881623)
              ·
                refine ⟨5714106442961057636822435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809404295307371757881623 5714106442961057636822435)
                ·
                  refine ⟨8571159664441586455233653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714106442961057636822435 8571159664441586455233653)
                  ·
                    refine ⟨803546218541398730178155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8571159664441586455233653 803546218541398730178155)
                    ·
                      rfl

theorem cell23_4694702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4694702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694702 prefixEnd_4694702 := by exact prefixLift 4694702
  have htrace : WordTrace (prefixWord ++ tailWord_4694702) baseStart_4694702 baseEnd_4694702 := by
    simpa [prefixWord, tailWord_4694702, baseEnd_4694702] using wordTrace_append hprefix tailTrace_4694702
  have hstable : (prefixWord ++ tailWord_4694702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694702).length < 2 ^ (prefixWord ++ tailWord_4694702).sum := by decide
  have hdescent : baseEnd_4694702 < baseStart_4694702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694705 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4694705 : Nat := 118140960795 + 4694705 * 2 ^ 59
def prefixEnd_4694705 : Nat := 4983230072969 + 3 ^ 40 * 4694705 * 2
def baseEnd_4694705 : Nat := 2410640196066159678796951

theorem tailTrace_4694705 : CollatzResearch.WordTrace tailWord_4694705 prefixEnd_4694705 2410640196066159678796951 := by
  unfold tailWord_4694705
  simp only [CollatzResearch.WordTrace]
  refine ⟨171229958456893051625205569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114153305637928701083470379 171229958456893051625205569)
  ·
    refine ⟨128422468842669788718904177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171229958456893051625205569 128422468842669788718904177)
    ·
      refine ⟨96316851632002341539178133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128422468842669788718904177 96316851632002341539178133)
      ·
        refine ⟨4514852420250109759648975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96316851632002341539178133 4514852420250109759648975)
        ·
          refine ⟨6772278630375164639473463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4514852420250109759648975 6772278630375164639473463)
          ·
            refine ⟨10158417945562746959210195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772278630375164639473463 10158417945562746959210195)
            ·
              refine ⟨15237626918344120438815293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10158417945562746959210195 15237626918344120438815293)
              ·
                refine ⟨5714110094379045164555735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15237626918344120438815293 5714110094379045164555735)
                ·
                  refine ⟨8571165141568567746833603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714110094379045164555735 8571165141568567746833603)
                  ·
                    refine ⟨12856747712352851620250405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8571165141568567746833603 12856747712352851620250405)
                    ·
                      refine ⟨2410640196066159678796951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12856747712352851620250405 2410640196066159678796951)
                      ·
                        rfl

theorem cell23_4694705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4694705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694705 prefixEnd_4694705 := by exact prefixLift 4694705
  have htrace : WordTrace (prefixWord ++ tailWord_4694705) baseStart_4694705 baseEnd_4694705 := by
    simpa [prefixWord, tailWord_4694705, baseEnd_4694705] using wordTrace_append hprefix tailTrace_4694705
  have hstable : (prefixWord ++ tailWord_4694705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694705).length < 2 ^ (prefixWord ++ tailWord_4694705).sum := by decide
  have hdescent : baseEnd_4694705 < baseStart_4694705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694765 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_4694765 : Nat := 118140960795 + 4694765 * 2 ^ 59
def prefixEnd_4694765 : Nat := 4983230072969 + 3 ^ 40 * 4694765 * 2
def baseEnd_4694765 : Nat := 2410671004905429444046675

theorem tailTrace_4694765 : CollatzResearch.WordTrace tailWord_4694765 prefixEnd_4694765 2410671004905429444046675 := by
  unfold tailWord_4694765
  simp only [CollatzResearch.WordTrace]
  refine ⟨171232146836675681872389749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114154764557783787914926499 171232146836675681872389749)
  ·
    refine ⟨16053013765938345175536539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171232146836675681872389749 16053013765938345175536539)
    ·
      refine ⟨24079520648907517763304809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053013765938345175536539 24079520648907517763304809)
      ·
        refine ⟨18059640486680638322478607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24079520648907517763304809 18059640486680638322478607)
        ·
          refine ⟨27089460730020957483717911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18059640486680638322478607 27089460730020957483717911)
          ·
            refine ⟨40634191095031436225576867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27089460730020957483717911 40634191095031436225576867)
            ·
              refine ⟨60951286642547154338365301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40634191095031436225576867 60951286642547154338365301)
              ·
                refine ⟨5714183122738795719221747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60951286642547154338365301 5714183122738795719221747)
                ·
                  refine ⟨8571274684108193578832621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5714183122738795719221747 8571274684108193578832621)
                  ·
                    refine ⟨3214228006540572592062233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8571274684108193578832621 3214228006540572592062233)
                    ·
                      refine ⟨2410671004905429444046675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214228006540572592062233 2410671004905429444046675)
                      ·
                        rfl

theorem cell23_4694765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_4694765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694765 prefixEnd_4694765 := by exact prefixLift 4694765
  have htrace : WordTrace (prefixWord ++ tailWord_4694765) baseStart_4694765 baseEnd_4694765 := by
    simpa [prefixWord, tailWord_4694765, baseEnd_4694765] using wordTrace_append hprefix tailTrace_4694765
  have hstable : (prefixWord ++ tailWord_4694765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694765).length < 2 ^ (prefixWord ++ tailWord_4694765).sum := by decide
  have hdescent : baseEnd_4694765 < baseStart_4694765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694773 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4694773 : Nat := 118140960795 + 4694773 * 2 ^ 59
def prefixEnd_4694773 : Nat := 4983230072969 + 3 ^ 40 * 4694773 * 2
def baseEnd_4694773 : Nat := 2410675112750665412746639

theorem tailTrace_4694773 : CollatzResearch.WordTrace tailWord_4694773 prefixEnd_4694773 2410675112750665412746639 := by
  unfold tailWord_4694773
  simp only [CollatzResearch.WordTrace]
  refine ⟨171232438620646699238680973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114154959080431132825787315 171232438620646699238680973)
  ·
    refine ⟨64212164482742512214505365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171232438620646699238680973 64212164482742512214505365)
    ·
      refine ⟨3009945210128555260054939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64212164482742512214505365 3009945210128555260054939)
      ·
        refine ⟨4514917815192832890082409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3009945210128555260054939 4514917815192832890082409)
        ·
          refine ⟨3386188361394624667561807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514917815192832890082409 3386188361394624667561807)
          ·
            refine ⟨5079282542091937001342711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386188361394624667561807 5079282542091937001342711)
            ·
              refine ⟨7618923813137905502014067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079282542091937001342711 7618923813137905502014067)
              ·
                refine ⟨11428385719706858253021101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618923813137905502014067 11428385719706858253021101)
                ·
                  refine ⟨4285644644890071844882913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11428385719706858253021101 4285644644890071844882913)
                  ·
                    refine ⟨3214233483667553883662185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285644644890071844882913 3214233483667553883662185)
                    ·
                      refine ⟨2410675112750665412746639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214233483667553883662185 2410675112750665412746639)
                      ·
                        rfl

theorem cell23_4694773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4694773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694773 prefixEnd_4694773 := by exact prefixLift 4694773
  have htrace : WordTrace (prefixWord ++ tailWord_4694773) baseStart_4694773 baseEnd_4694773 := by
    simpa [prefixWord, tailWord_4694773, baseEnd_4694773] using wordTrace_append hprefix tailTrace_4694773
  have hstable : (prefixWord ++ tailWord_4694773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694773).length < 2 ^ (prefixWord ++ tailWord_4694773).sum := by decide
  have hdescent : baseEnd_4694773 < baseStart_4694773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694781 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_4694781 : Nat := 118140960795 + 4694781 * 2 ^ 59
def prefixEnd_4694781 : Nat := 4983230072969 + 3 ^ 40 * 4694781 * 2
def baseEnd_4694781 : Nat := 2410679220595901381446601

theorem tailTrace_4694781 : CollatzResearch.WordTrace tailWord_4694781 prefixEnd_4694781 2410679220595901381446601 := by
  unfold tailWord_4694781
  simp only [CollatzResearch.WordTrace]
  refine ⟨171232730404617716604972197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114155153603078477736648131 171232730404617716604972197)
  ·
    refine ⟨32106136950865821863432287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171232730404617716604972197 32106136950865821863432287)
    ·
      refine ⟨48159205426298732795148431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32106136950865821863432287 48159205426298732795148431)
      ·
        refine ⟨72238808139448099192722647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48159205426298732795148431 72238808139448099192722647)
        ·
          refine ⟨108358212209172148789083971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72238808139448099192722647 108358212209172148789083971)
          ·
            refine ⟨162537318313758223183625957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108358212209172148789083971 162537318313758223183625957)
            ·
              refine ⟨30475747183829666846929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162537318313758223183625957 30475747183829666846929867)
              ·
                refine ⟨45713620775744500270394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30475747183829666846929867 45713620775744500270394801)
                ·
                  refine ⟨34285215581808375202796101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45713620775744500270394801 34285215581808375202796101)
                  ·
                    refine ⟨6428477921589070350524269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34285215581808375202796101 6428477921589070350524269)
                    ·
                      refine ⟨2410679220595901381446601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428477921589070350524269 2410679220595901381446601)
                      ·
                        rfl

theorem cell23_4694781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_4694781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694781 prefixEnd_4694781 := by exact prefixLift 4694781
  have htrace : WordTrace (prefixWord ++ tailWord_4694781) baseStart_4694781 baseEnd_4694781 := by
    simpa [prefixWord, tailWord_4694781, baseEnd_4694781] using wordTrace_append hprefix tailTrace_4694781
  have hstable : (prefixWord ++ tailWord_4694781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694781).length < 2 ^ (prefixWord ++ tailWord_4694781).sum := by decide
  have hdescent : baseEnd_4694781 < baseStart_4694781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694835 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 5]
def baseStart_4694835 : Nat := 118140960795 + 4694835 * 2 ^ 59
def prefixEnd_4694835 : Nat := 4983230072969 + 3 ^ 40 * 4694835 * 2
def baseEnd_4694835 : Nat := 267856327616804907796817

theorem tailTrace_4694835 : CollatzResearch.WordTrace tailWord_4694835 prefixEnd_4694835 267856327616804907796817 := by
  unfold tailWord_4694835
  simp only [CollatzResearch.WordTrace]
  refine ⟨171234699946422083827437959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114156466630948055884958639 171234699946422083827437959)
  ·
    refine ⟨256852049919633125741156939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171234699946422083827437959 256852049919633125741156939)
    ·
      refine ⟨385278074879449688611735409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256852049919633125741156939 385278074879449688611735409)
      ·
        refine ⟨288958556159587266458801557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385278074879449688611735409 288958556159587266458801557)
        ·
          refine ⟨13544932319980653115256323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 288958556159587266458801557 13544932319980653115256323)
          ·
            refine ⟨20317398479970979672884485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544932319980653115256323 20317398479970979672884485)
            ·
              refine ⟨3809512214994558688665841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20317398479970979672884485 3809512214994558688665841)
              ·
                refine ⟨2857134161245919016499381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809512214994558688665841 2857134161245919016499381)
                ·
                  refine ⟨267856327616804907796817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857134161245919016499381 267856327616804907796817)
                  ·
                    rfl

theorem cell23_4694835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 5].length) (baseStart_4694835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694835 prefixEnd_4694835 := by exact prefixLift 4694835
  have htrace : WordTrace (prefixWord ++ tailWord_4694835) baseStart_4694835 baseEnd_4694835 := by
    simpa [prefixWord, tailWord_4694835, baseEnd_4694835] using wordTrace_append hprefix tailTrace_4694835
  have hstable : (prefixWord ++ tailWord_4694835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694835).length < 2 ^ (prefixWord ++ tailWord_4694835).sum := by decide
  have hdescent : baseEnd_4694835 < baseStart_4694835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694845 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4694845 : Nat := 118140960795 + 4694845 * 2 ^ 59
def prefixEnd_4694845 : Nat := 4983230072969 + 3 ^ 40 * 4694845 * 2
def baseEnd_4694845 : Nat := 2410712083357789131046307

theorem tailTrace_4694845 : CollatzResearch.WordTrace tailWord_4694845 prefixEnd_4694845 2410712083357789131046307 := by
  unfold tailWord_4694845
  simp only [CollatzResearch.WordTrace]
  refine ⟨171235064676385855535301989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114156709784257237023534659 171235064676385855535301989)
  ·
    refine ⟨32106574626822347912869123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171235064676385855535301989 32106574626822347912869123)
    ·
      refine ⟨48159861940233521869303685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32106574626822347912869123 48159861940233521869303685)
      ·
        refine ⟨9029974113793785350494441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48159861940233521869303685 9029974113793785350494441)
        ·
          refine ⟨6772480585345339012870831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9029974113793785350494441 6772480585345339012870831)
          ·
            refine ⟨10158720878018008519306247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772480585345339012870831 10158720878018008519306247)
            ·
              refine ⟨15238081317027012778959371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10158720878018008519306247 15238081317027012778959371)
              ·
                refine ⟨22857121975540519168439057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15238081317027012778959371 22857121975540519168439057)
                ·
                  refine ⟨17142841481655389376329293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22857121975540519168439057 17142841481655389376329293)
                  ·
                    refine ⟨6428565555620771016123485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17142841481655389376329293 6428565555620771016123485)
                    ·
                      refine ⟨2410712083357789131046307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428565555620771016123485 2410712083357789131046307)
                      ·
                        rfl

theorem cell23_4694845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4694845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694845 prefixEnd_4694845 := by exact prefixLift 4694845
  have htrace : WordTrace (prefixWord ++ tailWord_4694845) baseStart_4694845 baseEnd_4694845 := by
    simpa [prefixWord, tailWord_4694845, baseEnd_4694845] using wordTrace_append hprefix tailTrace_4694845
  have hstable : (prefixWord ++ tailWord_4694845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694845).length < 2 ^ (prefixWord ++ tailWord_4694845).sum := by decide
  have hdescent : baseEnd_4694845 < baseStart_4694845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694851 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_4694851 : Nat := 118140960795 + 4694851 * 2 ^ 59
def prefixEnd_4694851 : Nat := 4983230072969 + 3 ^ 40 * 4694851 * 2
def baseEnd_4694851 : Nat := 2410715164241716107571279

theorem tailTrace_4694851 : CollatzResearch.WordTrace tailWord_4694851 prefixEnd_4694851 2410715164241716107571279 := by
  unfold tailWord_4694851
  simp only [CollatzResearch.WordTrace]
  refine ⟨171235283514364118560020407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114156855676242745706680271 171235283514364118560020407)
  ·
    refine ⟨256852925271546177840030611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171235283514364118560020407 256852925271546177840030611)
    ·
      refine ⟨385279387907319266760045917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256852925271546177840030611 385279387907319266760045917)
      ·
        refine ⟨144479770465244725035017219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 385279387907319266760045917 144479770465244725035017219)
        ·
          refine ⟨216719655697867087552525829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144479770465244725035017219 216719655697867087552525829)
          ·
            refine ⟨40634935443350078916098593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216719655697867087552525829 40634935443350078916098593)
            ·
              refine ⟨30476201582512559187073945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40634935443350078916098593 30476201582512559187073945)
              ·
                refine ⟨22857151186884419390305459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30476201582512559187073945 22857151186884419390305459)
                ·
                  refine ⟨34285726780326629085458189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22857151186884419390305459 34285726780326629085458189)
                  ·
                    refine ⟨12857147542622485907046821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34285726780326629085458189 12857147542622485907046821)
                    ·
                      refine ⟨2410715164241716107571279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12857147542622485907046821 2410715164241716107571279)
                      ·
                        rfl

theorem cell23_4694851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_4694851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694851 prefixEnd_4694851 := by exact prefixLift 4694851
  have htrace : WordTrace (prefixWord ++ tailWord_4694851) baseStart_4694851 baseEnd_4694851 := by
    simpa [prefixWord, tailWord_4694851, baseEnd_4694851] using wordTrace_append hprefix tailTrace_4694851
  have hstable : (prefixWord ++ tailWord_4694851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694851).length < 2 ^ (prefixWord ++ tailWord_4694851).sum := by decide
  have hdescent : baseEnd_4694851 < baseStart_4694851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694865 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_4694865 : Nat := 118140960795 + 4694865 * 2 ^ 59
def prefixEnd_4694865 : Nat := 4983230072969 + 3 ^ 40 * 4694865 * 2
def baseEnd_4694865 : Nat := 803574117656959684265405

theorem tailTrace_4694865 : CollatzResearch.WordTrace tailWord_4694865 prefixEnd_4694865 803574117656959684265405 := by
  unfold tailWord_4694865
  simp only [CollatzResearch.WordTrace]
  refine ⟨171235794136313398951030049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114157196090875599300686699 171235794136313398951030049)
  ·
    refine ⟨128426845602235049213272537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171235794136313398951030049 128426845602235049213272537)
    ·
      refine ⟨96320134201676286909954403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128426845602235049213272537 96320134201676286909954403)
      ·
        refine ⟨144480201302514430364931605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96320134201676286909954403 144480201302514430364931605)
        ·
          refine ⟨6772509436055363923356169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144480201302514430364931605 6772509436055363923356169)
          ·
            refine ⟨5079382077041522942517127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6772509436055363923356169 5079382077041522942517127)
            ·
              refine ⟨7619073115562284413775691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079382077041522942517127 7619073115562284413775691)
              ·
                refine ⟨11428609673343426620663537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619073115562284413775691 11428609673343426620663537)
                ·
                  refine ⟨8571457255007569965497653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11428609673343426620663537 8571457255007569965497653)
                  ·
                    refine ⟨803574117656959684265405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8571457255007569965497653 803574117656959684265405)
                    ·
                      rfl

theorem cell23_4694865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_4694865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694865 prefixEnd_4694865 := by exact prefixLift 4694865
  have htrace : WordTrace (prefixWord ++ tailWord_4694865) baseStart_4694865 baseEnd_4694865 := by
    simpa [prefixWord, tailWord_4694865, baseEnd_4694865] using wordTrace_append hprefix tailTrace_4694865
  have hstable : (prefixWord ++ tailWord_4694865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694865).length < 2 ^ (prefixWord ++ tailWord_4694865).sum := by decide
  have hdescent : baseEnd_4694865 < baseStart_4694865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694902 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4694902 : Nat := 118140960795 + 4694902 * 2 ^ 59
def prefixEnd_4694902 : Nat := 4983230072969 + 3 ^ 40 * 4694902 * 2
def baseEnd_4694902 : Nat := 2410741351755095408033545

theorem tailTrace_4694902 : CollatzResearch.WordTrace tailWord_4694902 prefixEnd_4694902 2410741351755095408033545 := by
  unfold tailWord_4694902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702321477323709641882935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114158095758119569513417973 10702321477323709641882935)
  ·
    refine ⟨16053482215985564462824403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10702321477323709641882935 16053482215985564462824403)
    ·
      refine ⟨24080223323978346694236605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16053482215985564462824403 24080223323978346694236605)
      ·
        refine ⟨9030083746491880010338727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24080223323978346694236605 9030083746491880010338727)
        ·
          refine ⟨13545125619737820015508091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030083746491880010338727 13545125619737820015508091)
          ·
            refine ⟨20317688429606730023262137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13545125619737820015508091 20317688429606730023262137)
            ·
              refine ⟨15238266322205047517446603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20317688429606730023262137 15238266322205047517446603)
              ·
                refine ⟨22857399483307571276169905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15238266322205047517446603 22857399483307571276169905)
                ·
                  refine ⟨17143049612480678457127429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22857399483307571276169905 17143049612480678457127429)
                  ·
                    refine ⟨3214321802340127210711393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17143049612480678457127429 3214321802340127210711393)
                    ·
                      refine ⟨2410741351755095408033545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214321802340127210711393 2410741351755095408033545)
                      ·
                        rfl

theorem cell23_4694902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4694902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694902 prefixEnd_4694902 := by exact prefixLift 4694902
  have htrace : WordTrace (prefixWord ++ tailWord_4694902) baseStart_4694902 baseEnd_4694902 := by
    simpa [prefixWord, tailWord_4694902, baseEnd_4694902] using wordTrace_append hprefix tailTrace_4694902
  have hstable : (prefixWord ++ tailWord_4694902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694902).length < 2 ^ (prefixWord ++ tailWord_4694902).sum := by decide
  have hdescent : baseEnd_4694902 < baseStart_4694902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694928 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2]
def baseStart_4694928 : Nat := 118140960795 + 4694928 * 2 ^ 59
def prefixEnd_4694928 : Nat := 4983230072969 + 3 ^ 40 * 4694928 * 2
def baseEnd_4694928 : Nat := 2410754702252112306308425

theorem tailTrace_4694928 : CollatzResearch.WordTrace tailWord_4694928 prefixEnd_4694928 2410754702252112306308425 := by
  unfold tailWord_4694928
  simp only [CollatzResearch.WordTrace]
  refine ⟨85619045967542580355286719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114158727956723440473715625 85619045967542580355286719)
  ·
    refine ⟨128428568951313870532930079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85619045967542580355286719 128428568951313870532930079)
    ·
      refine ⟨192642853426970805799395119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128428568951313870532930079 192642853426970805799395119)
      ·
        refine ⟨288964280140456208699092679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192642853426970805799395119 288964280140456208699092679)
        ·
          refine ⟨433446420210684313048639019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288964280140456208699092679 433446420210684313048639019)
          ·
            refine ⟨650169630316026469572958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433446420210684313048639019 650169630316026469572958529)
            ·
              refine ⟨487627222737019852179718897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650169630316026469572958529 487627222737019852179718897)
              ·
                refine ⟨365720417052764889134789173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487627222737019852179718897 365720417052764889134789173)
                ·
                  refine ⟨34286289098696708356386485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 365720417052764889134789173 34286289098696708356386485)
                  ·
                    refine ⟨3214339603002816408411233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34286289098696708356386485 3214339603002816408411233)
                    ·
                      refine ⟨2410754702252112306308425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214339603002816408411233 2410754702252112306308425)
                      ·
                        rfl

theorem cell23_4694928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 5, 2].length) (baseStart_4694928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694928 prefixEnd_4694928 := by exact prefixLift 4694928
  have htrace : WordTrace (prefixWord ++ tailWord_4694928) baseStart_4694928 baseEnd_4694928 := by
    simpa [prefixWord, tailWord_4694928, baseEnd_4694928] using wordTrace_append hprefix tailTrace_4694928
  have hstable : (prefixWord ++ tailWord_4694928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694928).length < 2 ^ (prefixWord ++ tailWord_4694928).sum := by decide
  have hdescent : baseEnd_4694928 < baseStart_4694928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4694971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_4694971 : Nat := 118140960795 + 4694971 * 2 ^ 59
def prefixEnd_4694971 : Nat := 4983230072969 + 3 ^ 40 * 4694971 * 2
def baseEnd_4694971 : Nat := 2410776781920255638070727

theorem tailTrace_4694971 : CollatzResearch.WordTrace tailWord_4694971 prefixEnd_4694971 2410776781920255638070727 := by
  unfold tailWord_4694971
  simp only [CollatzResearch.WordTrace]
  refine ⟨171239660273929379054388767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114159773515952919369592511 171239660273929379054388767)
  ·
    refine ⟨256859490410894068581583151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171239660273929379054388767 256859490410894068581583151)
    ·
      refine ⟨385289235616341102872374727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256859490410894068581583151 385289235616341102872374727)
      ·
        refine ⟨577933853424511654308562091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385289235616341102872374727 577933853424511654308562091)
        ·
          refine ⟨866900780136767481462843137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577933853424511654308562091 866900780136767481462843137)
          ·
            refine ⟨650175585102575611097132353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866900780136767481462843137 650175585102575611097132353)
            ·
              refine ⟨487631688826931708322849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650175585102575611097132353 487631688826931708322849265)
              ·
                refine ⟨365723766620198781242136949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487631688826931708322849265 365723766620198781242136949)
                ·
                  refine ⟨34286603120643635741450339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 365723766620198781242136949 34286603120643635741450339)
                  ·
                    refine ⟨51429904680965453612175509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34286603120643635741450339 51429904680965453612175509)
                    ·
                      refine ⟨2410776781920255638070727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51429904680965453612175509 2410776781920255638070727)
                      ·
                        rfl

theorem cell23_4694971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_4694971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4694971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4694971 prefixEnd_4694971 := by exact prefixLift 4694971
  have htrace : WordTrace (prefixWord ++ tailWord_4694971) baseStart_4694971 baseEnd_4694971 := by
    simpa [prefixWord, tailWord_4694971, baseEnd_4694971] using wordTrace_append hprefix tailTrace_4694971
  have hstable : (prefixWord ++ tailWord_4694971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4694971).length < 2 ^ (prefixWord ++ tailWord_4694971).sum := by decide
  have hdescent : baseEnd_4694971 < baseStart_4694971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4694971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695002 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_4695002 : Nat := 118140960795 + 4695002 * 2 ^ 59
def prefixEnd_4695002 : Nat := 4983230072969 + 3 ^ 40 * 4695002 * 2
def baseEnd_4695002 : Nat := 803597566606848338927695

theorem tailTrace_4695002 : CollatzResearch.WordTrace tailWord_4695002 prefixEnd_4695002 803597566606848338927695 := by
  unfold tailWord_4695002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42810197734204267837191815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114160527291211380899178173 42810197734204267837191815)
  ·
    refine ⟨64215296601306401755787723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42810197734204267837191815 64215296601306401755787723)
    ·
      refine ⟨96322944901959602633681585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64215296601306401755787723 96322944901959602633681585)
      ·
        refine ⟨72242208676469701975261189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96322944901959602633681585 72242208676469701975261189)
        ·
          refine ⟨13545414126838069120361473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72242208676469701975261189 13545414126838069120361473)
          ·
            refine ⟨10159060595128551840271105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13545414126838069120361473 10159060595128551840271105)
            ·
              refine ⟨7619295446346413880203329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10159060595128551840271105 7619295446346413880203329)
              ·
                refine ⟨5714471584759810410152497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7619295446346413880203329 5714471584759810410152497)
                ·
                  refine ⟨4285853688569857807614373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714471584759810410152497 4285853688569857807614373)
                  ·
                    refine ⟨803597566606848338927695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285853688569857807614373 803597566606848338927695)
                    ·
                      rfl

theorem cell23_4695002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_4695002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695002 prefixEnd_4695002 := by exact prefixLift 4695002
  have htrace : WordTrace (prefixWord ++ tailWord_4695002) baseStart_4695002 baseEnd_4695002 := by
    simpa [prefixWord, tailWord_4695002, baseEnd_4695002] using wordTrace_append hprefix tailTrace_4695002
  have hstable : (prefixWord ++ tailWord_4695002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695002).length < 2 ^ (prefixWord ++ tailWord_4695002).sum := by decide
  have hdescent : baseEnd_4695002 < baseStart_4695002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695015 : List Nat := [1, 1, 5, 2, 2, 3, 1, 8]
def baseStart_4695015 : Nat := 118140960795 + 4695015 * 2 ^ 59
def prefixEnd_4695015 : Nat := 4983230072969 + 3 ^ 40 * 4695015 * 2
def baseEnd_4695015 : Nat := 89288865743298276515575

theorem tailTrace_4695015 : CollatzResearch.WordTrace tailWord_4695015 prefixEnd_4695015 89288865743298276515575 := by
  unfold tailWord_4695015
  simp only [CollatzResearch.WordTrace]
  refine ⟨171241265085769974568990499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114160843390513316379326999 171241265085769974568990499)
  ·
    refine ⟨256861897628654961853485749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171241265085769974568990499 256861897628654961853485749)
    ·
      refine ⟨24080802902686402673764289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 256861897628654961853485749 24080802902686402673764289)
      ·
        refine ⟨18060602177014802005323217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24080802902686402673764289 18060602177014802005323217)
        ·
          refine ⟨13545451632761101503992413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18060602177014802005323217 13545451632761101503992413)
          ·
            refine ⟨5079544362285413063997155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13545451632761101503992413 5079544362285413063997155)
            ·
              refine ⟨7619316543428119595995733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079544362285413063997155 7619316543428119595995733)
              ·
                refine ⟨89288865743298276515575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7619316543428119595995733 89288865743298276515575)
                ·
                  rfl

theorem cell23_4695015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 8].length) (baseStart_4695015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695015 prefixEnd_4695015 := by exact prefixLift 4695015
  have htrace : WordTrace (prefixWord ++ tailWord_4695015) baseStart_4695015 baseEnd_4695015 := by
    simpa [prefixWord, tailWord_4695015, baseEnd_4695015] using wordTrace_append hprefix tailTrace_4695015
  have hstable : (prefixWord ++ tailWord_4695015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695015).length < 2 ^ (prefixWord ++ tailWord_4695015).sum := by decide
  have hdescent : baseEnd_4695015 < baseStart_4695015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695022 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4695022 : Nat := 118140960795 + 4695022 * 2 ^ 59
def prefixEnd_4695022 : Nat := 4983230072969 + 3 ^ 40 * 4695022 * 2
def baseEnd_4695022 : Nat := 2410802969433634938532993

theorem tailTrace_4695022 : CollatzResearch.WordTrace tailWord_4695022 prefixEnd_4695022 2410802969433634938532993 := by
  unfold tailWord_4695022
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405190049593076845561915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114161013597829743176330213 21405190049593076845561915)
  ·
    refine ⟨32107785074389615268342873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21405190049593076845561915 32107785074389615268342873)
    ·
      refine ⟨24080838805792211451257155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32107785074389615268342873 24080838805792211451257155)
      ·
        refine ⟨36121258208688317176885733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24080838805792211451257155 36121258208688317176885733)
        ·
          refine ⟨6772735914129059470666075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36121258208688317176885733 6772735914129059470666075)
          ·
            refine ⟨10159103871193589205999113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772735914129059470666075 10159103871193589205999113)
            ·
              refine ⟨7619327903395191904499335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10159103871193589205999113 7619327903395191904499335)
              ·
                refine ⟨11428991855092787856749003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619327903395191904499335 11428991855092787856749003)
                ·
                  refine ⟨17143487782639181785123505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11428991855092787856749003 17143487782639181785123505)
                  ·
                    refine ⟨12857615836979386338842629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17143487782639181785123505 12857615836979386338842629)
                    ·
                      refine ⟨2410802969433634938532993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12857615836979386338842629 2410802969433634938532993)
                      ·
                        rfl

theorem cell23_4695022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4695022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695022 prefixEnd_4695022 := by exact prefixLift 4695022
  have htrace : WordTrace (prefixWord ++ tailWord_4695022) baseStart_4695022 baseEnd_4695022 := by
    simpa [prefixWord, tailWord_4695022, baseEnd_4695022] using wordTrace_append hprefix tailTrace_4695022
  have hstable : (prefixWord ++ tailWord_4695022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695022).length < 2 ^ (prefixWord ++ tailWord_4695022).sum := by decide
  have hdescent : baseEnd_4695022 < baseStart_4695022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695025 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_4695025 : Nat := 118140960795 + 4695025 * 2 ^ 59
def prefixEnd_4695025 : Nat := 4983230072969 + 3 ^ 40 * 4695025 * 2
def baseEnd_4695025 : Nat := 2410804509875598426795479

theorem tailTrace_4695025 : CollatzResearch.WordTrace tailWord_4695025 prefixEnd_4695025 2410804509875598426795479 := by
  unfold tailWord_4695025
  simp only [CollatzResearch.WordTrace]
  refine ⟨171241629815733746276854529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114161086543822497517903019 171241629815733746276854529)
  ·
    refine ⟨128431222361800309707640897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171241629815733746276854529 128431222361800309707640897)
    ·
      refine ⟨96323416771350232280730673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128431222361800309707640897 96323416771350232280730673)
      ·
        refine ⟨72242562578512674210548005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96323416771350232280730673 72242562578512674210548005)
        ·
          refine ⟨13545480483471126414477751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72242562578512674210548005 13545480483471126414477751)
          ·
            refine ⟨20318220725206689621716627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13545480483471126414477751 20318220725206689621716627)
            ·
              refine ⟨30477331087810034432574941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20318220725206689621716627 30477331087810034432574941)
              ·
                refine ⟨11428999157928762912215603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30477331087810034432574941 11428999157928762912215603)
                ·
                  refine ⟨17143498736893144368323405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11428999157928762912215603 17143498736893144368323405)
                  ·
                    refine ⟨6428812026334929138121277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17143498736893144368323405 6428812026334929138121277)
                    ·
                      refine ⟨2410804509875598426795479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428812026334929138121277 2410804509875598426795479)
                      ·
                        rfl

theorem cell23_4695025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_4695025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695025 prefixEnd_4695025 := by exact prefixLift 4695025
  have htrace : WordTrace (prefixWord ++ tailWord_4695025) baseStart_4695025 baseEnd_4695025 := by
    simpa [prefixWord, tailWord_4695025, baseEnd_4695025] using wordTrace_append hprefix tailTrace_4695025
  have hstable : (prefixWord ++ tailWord_4695025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695025).length < 2 ^ (prefixWord ++ tailWord_4695025).sum := by decide
  have hdescent : baseEnd_4695025 < baseStart_4695025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695026 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4695026 : Nat := 118140960795 + 4695026 * 2 ^ 59
def prefixEnd_4695026 : Nat := 4983230072969 + 3 ^ 40 * 4695026 * 2
def baseEnd_4695026 : Nat := 2410805023356252922882975

theorem tailTrace_4695026 : CollatzResearch.WordTrace tailWord_4695026 prefixEnd_4695026 2410805023356252922882975 := by
  unfold tailWord_4695026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42810416572182530861910233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114161110859153415631760621 42810416572182530861910233)
  ·
    refine ⟨32107812429136898146432675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42810416572182530861910233 32107812429136898146432675)
    ·
      refine ⟨48161718643705347219649013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32107812429136898146432675 48161718643705347219649013)
      ·
        refine ⟨4515161122847376301842095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48161718643705347219649013 4515161122847376301842095)
        ·
          refine ⟨6772741684271064452763143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515161122847376301842095 6772741684271064452763143)
          ·
            refine ⟨10159112526406596679144715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772741684271064452763143 10159112526406596679144715)
            ·
              refine ⟨15238668789609895018717073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159112526406596679144715 15238668789609895018717073)
              ·
                refine ⟨11429001592207421264037805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15238668789609895018717073 11429001592207421264037805)
                ·
                  refine ⟨4285875597077782974014177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11429001592207421264037805 4285875597077782974014177)
                  ·
                    refine ⟨3214406697808337230510633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285875597077782974014177 3214406697808337230510633)
                    ·
                      refine ⟨2410805023356252922882975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214406697808337230510633 2410805023356252922882975)
                      ·
                        rfl

theorem cell23_4695026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4695026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695026 prefixEnd_4695026 := by exact prefixLift 4695026
  have htrace : WordTrace (prefixWord ++ tailWord_4695026) baseStart_4695026 baseEnd_4695026 := by
    simpa [prefixWord, tailWord_4695026, baseEnd_4695026] using wordTrace_append hprefix tailTrace_4695026
  have hstable : (prefixWord ++ tailWord_4695026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695026).length < 2 ^ (prefixWord ++ tailWord_4695026).sum := by decide
  have hdescent : baseEnd_4695026 < baseStart_4695026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695065 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 4, 2]
def baseStart_4695065 : Nat := 118140960795 + 4695065 * 2 ^ 59
def prefixEnd_4695065 : Nat := 4983230072969 + 3 ^ 40 * 4695065 * 2
def baseEnd_4695065 : Nat := 2410825049101778270295295

theorem tailTrace_4695065 : CollatzResearch.WordTrace tailWord_4695065 prefixEnd_4695065 2410825049101778270295295 := by
  unfold tailWord_4695065
  simp only [CollatzResearch.WordTrace]
  refine ⟨171243088735588833108310649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114162059157059222072207099 171243088735588833108310649)
  ·
    refine ⟨128432316551691624831232987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171243088735588833108310649 128432316551691624831232987)
    ·
      refine ⟨192648474827537437246849481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128432316551691624831232987 192648474827537437246849481)
      ·
        refine ⟨144486356120653077935137111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192648474827537437246849481 144486356120653077935137111)
        ·
          refine ⟨216729534180979616902705667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144486356120653077935137111 216729534180979616902705667)
          ·
            refine ⟨325094301271469425354058501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216729534180979616902705667 325094301271469425354058501)
            ·
              refine ⟨60955181488400517253885969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325094301271469425354058501 60955181488400517253885969)
              ·
                refine ⟨45716386116300387940414477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60955181488400517253885969 45716386116300387940414477)
                ·
                  refine ⟨17143644793612645477655429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45716386116300387940414477 17143644793612645477655429)
                  ·
                    refine ⟨3214433398802371027060393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17143644793612645477655429 3214433398802371027060393)
                    ·
                      refine ⟨2410825049101778270295295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214433398802371027060393 2410825049101778270295295)
                      ·
                        rfl

theorem cell23_4695065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_4695065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695065 prefixEnd_4695065 := by exact prefixLift 4695065
  have htrace : WordTrace (prefixWord ++ tailWord_4695065) baseStart_4695065 baseEnd_4695065 := by
    simpa [prefixWord, tailWord_4695065, baseEnd_4695065] using wordTrace_append hprefix tailTrace_4695065
  have hstable : (prefixWord ++ tailWord_4695065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695065).length < 2 ^ (prefixWord ++ tailWord_4695065).sum := by decide
  have hdescent : baseEnd_4695065 < baseStart_4695065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695076 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_4695076 : Nat := 118140960795 + 4695076 * 2 ^ 59
def prefixEnd_4695076 : Nat := 4983230072969 + 3 ^ 40 * 4695076 * 2
def baseEnd_4695076 : Nat := 2410830697388977727257745

theorem tailTrace_4695076 : CollatzResearch.WordTrace tailWord_4695076 prefixEnd_4695076 2410830697388977727257745 := by
  unfold tailWord_4695076
  simp only [CollatzResearch.WordTrace]
  refine ⟨85621744969274490993480541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114162326625699321324640721 85621744969274490993480541)
  ·
    refine ⟨32108154363477934122555203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85621744969274490993480541 32108154363477934122555203)
    ·
      refine ⟨48162231545216901183832805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32108154363477934122555203 48162231545216901183832805)
      ·
        refine ⟨9030418414728168971968651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48162231545216901183832805 9030418414728168971968651)
        ·
          refine ⟨13545627622092253457952977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030418414728168971968651 13545627622092253457952977)
          ·
            refine ⟨10159220716569190093464733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13545627622092253457952977 10159220716569190093464733)
            ·
              refine ⟨3809707768713446285049275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10159220716569190093464733 3809707768713446285049275)
              ·
                refine ⟨5714561653070169427573913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809707768713446285049275 5714561653070169427573913)
                ·
                  refine ⟨4285921239802627070680435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714561653070169427573913 4285921239802627070680435)
                  ·
                    refine ⟨6428881859703940606020653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4285921239802627070680435 6428881859703940606020653)
                    ·
                      refine ⟨2410830697388977727257745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6428881859703940606020653 2410830697388977727257745)
                      ·
                        rfl

theorem cell23_4695076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_4695076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695076 prefixEnd_4695076 := by exact prefixLift 4695076
  have htrace : WordTrace (prefixWord ++ tailWord_4695076) baseStart_4695076 baseEnd_4695076 := by
    simpa [prefixWord, tailWord_4695076, baseEnd_4695076] using wordTrace_append hprefix tailTrace_4695076
  have hstable : (prefixWord ++ tailWord_4695076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695076).length < 2 ^ (prefixWord ++ tailWord_4695076).sum := by decide
  have hdescent : baseEnd_4695076 < baseStart_4695076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695088 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 7]
def baseStart_4695088 : Nat := 118140960795 + 4695088 * 2 ^ 59
def prefixEnd_4695088 : Nat := 4983230072969 + 3 ^ 40 * 4695088 * 2
def baseEnd_4695088 : Nat := 267870762128536853367521

theorem tailTrace_4695088 : CollatzResearch.WordTrace tailWord_4695088 prefixEnd_4695088 267870762128536853367521 := by
  unfold tailWord_4695088
  simp only [CollatzResearch.WordTrace]
  refine ⟨85621963807252754018198959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114162618409670338690931945 85621963807252754018198959)
  ·
    refine ⟨128432945710879131027298439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85621963807252754018198959 128432945710879131027298439)
    ·
      refine ⟨192649418566318696540947659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128432945710879131027298439 192649418566318696540947659)
      ·
        refine ⟨288974127849478044811421489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192649418566318696540947659 288974127849478044811421489)
        ·
          refine ⟨216730595887108533608566117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288974127849478044811421489 216730595887108533608566117)
          ·
            refine ⟨40636986728832850051606147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216730595887108533608566117 40636986728832850051606147)
            ·
              refine ⟨60955480093249275077409221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40636986728832850051606147 60955480093249275077409221)
              ·
                refine ⟨11429152517484239077014229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60955480093249275077409221 11429152517484239077014229)
                ·
                  refine ⟨267870762128536853367521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11429152517484239077014229 267870762128536853367521)
                  ·
                    rfl

theorem cell23_4695088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_4695088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695088 prefixEnd_4695088 := by exact prefixLift 4695088
  have htrace : WordTrace (prefixWord ++ tailWord_4695088) baseStart_4695088 baseEnd_4695088 := by
    simpa [prefixWord, tailWord_4695088, baseEnd_4695088] using wordTrace_append hprefix tailTrace_4695088
  have hstable : (prefixWord ++ tailWord_4695088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695088).length < 2 ^ (prefixWord ++ tailWord_4695088).sum := by decide
  have hdescent : baseEnd_4695088 < baseStart_4695088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695102 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4695102 : Nat := 118140960795 + 4695102 * 2 ^ 59
def prefixEnd_4695102 : Nat := 4983230072969 + 3 ^ 40 * 4695102 * 2
def baseEnd_4695102 : Nat := 2410844047885994625532625

theorem tailTrace_4695102 : CollatzResearch.WordTrace tailWord_4695102 prefixEnd_4695102 2410844047885994625532625 := by
  unfold tailWord_4695102
  simp only [CollatzResearch.WordTrace]
  refine ⟨21405554779556848553425945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114162958824303192284938373 21405554779556848553425945)
  ·
    refine ⟨16054166084667636415069459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21405554779556848553425945 16054166084667636415069459)
    ·
      refine ⟨24081249127001454622604189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16054166084667636415069459 24081249127001454622604189)
      ·
        refine ⟨9030468422625545483476571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24081249127001454622604189 9030468422625545483476571)
        ·
          refine ⟨13545702633938318225214857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9030468422625545483476571 13545702633938318225214857)
          ·
            refine ⟨10159276975453738668911143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13545702633938318225214857 10159276975453738668911143)
            ·
              refine ⟨15238915463180608003366715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159276975453738668911143 15238915463180608003366715)
              ·
                refine ⟨22858373194770912005050073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15238915463180608003366715 22858373194770912005050073)
                ·
                  refine ⟨17143779896078184003787555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22858373194770912005050073 17143779896078184003787555)
                  ·
                    refine ⟨25715669844117276005681333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17143779896078184003787555 25715669844117276005681333)
                    ·
                      refine ⟨2410844047885994625532625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25715669844117276005681333 2410844047885994625532625)
                      ·
                        rfl

theorem cell23_4695102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4695102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695102 prefixEnd_4695102 := by exact prefixLift 4695102
  have htrace : WordTrace (prefixWord ++ tailWord_4695102) baseStart_4695102 baseEnd_4695102 := by
    simpa [prefixWord, tailWord_4695102, baseEnd_4695102] using wordTrace_append hprefix tailTrace_4695102
  have hstable : (prefixWord ++ tailWord_4695102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695102).length < 2 ^ (prefixWord ++ tailWord_4695102).sum := by decide
  have hdescent : baseEnd_4695102 < baseStart_4695102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695122 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_4695122 : Nat := 118140960795 + 4695122 * 2 ^ 59
def prefixEnd_4695122 : Nat := 4983230072969 + 3 ^ 40 * 4695122 * 2
def baseEnd_4695122 : Nat := 267872701944342727475837

theorem tailTrace_4695122 : CollatzResearch.WordTrace tailWord_4695122 prefixEnd_4695122 267872701944342727475837 := by
  unfold tailWord_4695122
  simp only [CollatzResearch.WordTrace]
  refine ⟨42811291924095582960783905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114163445130921554562090413 42811291924095582960783905)
  ·
    refine ⟨32108468943071687220587929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42811291924095582960783905 32108468943071687220587929)
    ·
      refine ⟨24081351707303765415440947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32108468943071687220587929 24081351707303765415440947)
      ·
        refine ⟨36122027560955648123161421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24081351707303765415440947 36122027560955648123161421)
        ·
          refine ⟨13545760335358368046185533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36122027560955648123161421 13545760335358368046185533)
          ·
            refine ⟨5079660125759388017319575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13545760335358368046185533 5079660125759388017319575)
            ·
              refine ⟨7619490188639082025979363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079660125759388017319575 7619490188639082025979363)
              ·
                refine ⟨11429235282958623038969045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619490188639082025979363 11429235282958623038969045)
                ·
                  refine ⟨267872701944342727475837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11429235282958623038969045 267872701944342727475837)
                  ·
                    rfl

theorem cell23_4695122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_4695122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695122 prefixEnd_4695122 := by exact prefixLift 4695122
  have htrace : WordTrace (prefixWord ++ tailWord_4695122) baseStart_4695122 baseEnd_4695122 := by
    simpa [prefixWord, tailWord_4695122, baseEnd_4695122] using wordTrace_append hprefix tailTrace_4695122
  have hstable : (prefixWord ++ tailWord_4695122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695122).length < 2 ^ (prefixWord ++ tailWord_4695122).sum := by decide
  have hdescent : baseEnd_4695122 < baseStart_4695122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695133 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4695133 : Nat := 118140960795 + 4695133 * 2 ^ 59
def prefixEnd_4695133 : Nat := 4983230072969 + 3 ^ 40 * 4695133 * 2
def baseEnd_4695133 : Nat := 2410859965786284004244983

theorem tailTrace_4695133 : CollatzResearch.WordTrace tailWord_4695133 prefixEnd_4695133 2410859965786284004244983 := by
  unfold tailWord_4695133
  simp only [CollatzResearch.WordTrace]
  refine ⟨171245568899342480721786053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114163712599561653814524035 171245568899342480721786053)
  ·
    refine ⟨32108544168626715135334885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171245568899342480721786053 32108544168626715135334885)
    ·
      refine ⟨6020352031617509087875291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32108544168626715135334885 6020352031617509087875291)
      ·
        refine ⟨9030528047426263631812937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6020352031617509087875291 9030528047426263631812937)
        ·
          refine ⟨6772896035569697723859703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9030528047426263631812937 6772896035569697723859703)
          ·
            refine ⟨10159344053354546585789555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772896035569697723859703 10159344053354546585789555)
            ·
              refine ⟨15239016080031819878684333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159344053354546585789555 15239016080031819878684333)
              ·
                refine ⟨5714631030011932454506625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15239016080031819878684333 5714631030011932454506625)
                ·
                  refine ⟨4285973272508949340879969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714631030011932454506625 4285973272508949340879969)
                  ·
                    refine ⟨3214479954381712005659977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4285973272508949340879969 3214479954381712005659977)
                    ·
                      refine ⟨2410859965786284004244983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214479954381712005659977 2410859965786284004244983)
                      ·
                        rfl

theorem cell23_4695133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4695133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695133 prefixEnd_4695133 := by exact prefixLift 4695133
  have htrace : WordTrace (prefixWord ++ tailWord_4695133) baseStart_4695133 baseEnd_4695133 := by
    simpa [prefixWord, tailWord_4695133, baseEnd_4695133] using wordTrace_append hprefix tailTrace_4695133
  have hstable : (prefixWord ++ tailWord_4695133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695133).length < 2 ^ (prefixWord ++ tailWord_4695133).sum := by decide
  have hdescent : baseEnd_4695133 < baseStart_4695133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695172 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4695172 : Nat := 118140960795 + 4695172 * 2 ^ 59
def prefixEnd_4695172 : Nat := 4983230072969 + 3 ^ 40 * 4695172 * 2
def baseEnd_4695172 : Nat := 2410879991531809351657303

theorem tailTrace_4695172 : CollatzResearch.WordTrace tailWord_4695172 prefixEnd_4695172 2410879991531809351657303 := by
  unfold tailWord_4695172
  simp only [CollatzResearch.WordTrace]
  refine ⟨85623495673100595191227885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114164660897467460254970513 85623495673100595191227885)
  ·
    refine ⟨32108810877412723196710457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85623495673100595191227885 32108810877412723196710457)
    ·
      refine ⟨24081608158059542397532843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32108810877412723196710457 24081608158059542397532843)
      ·
        refine ⟨36122412237089313596299265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24081608158059542397532843 36122412237089313596299265)
        ·
          refine ⟨27091809177816985197224449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36122412237089313596299265 27091809177816985197224449)
          ·
            refine ⟨20318856883362738897918337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27091809177816985197224449 20318856883362738897918337)
            ·
              refine ⟨15239142662522054173438753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20318856883362738897918337 15239142662522054173438753)
              ·
                refine ⟨11429356996891540630079065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15239142662522054173438753 11429356996891540630079065)
                ·
                  refine ⟨8572017747668655472559299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11429356996891540630079065 8572017747668655472559299)
                  ·
                    refine ⟨12858026621502983208838949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8572017747668655472559299 12858026621502983208838949)
                    ·
                      refine ⟨2410879991531809351657303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12858026621502983208838949 2410879991531809351657303)
                      ·
                        rfl

theorem cell23_4695172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4695172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695172 prefixEnd_4695172 := by exact prefixLift 4695172
  have htrace : WordTrace (prefixWord ++ tailWord_4695172) baseStart_4695172 baseEnd_4695172 := by
    simpa [prefixWord, tailWord_4695172, baseEnd_4695172] using wordTrace_append hprefix tailTrace_4695172
  have hstable : (prefixWord ++ tailWord_4695172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695172).length < 2 ^ (prefixWord ++ tailWord_4695172).sum := by decide
  have hdescent : baseEnd_4695172 < baseStart_4695172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695175 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_4695175 : Nat := 118140960795 + 4695175 * 2 ^ 59
def prefixEnd_4695175 : Nat := 4983230072969 + 3 ^ 40 * 4695175 * 2
def baseEnd_4695175 : Nat := 2410881531973772839919789

theorem tailTrace_4695175 : CollatzResearch.WordTrace tailWord_4695175 prefixEnd_4695175 2410881531973772839919789 := by
  unfold tailWord_4695175
  simp only [CollatzResearch.WordTrace]
  refine ⟨171247100765190321894814979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114164733843460214596543319 171247100765190321894814979)
  ·
    refine ⟨256870651147785482842222469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171247100765190321894814979 256870651147785482842222469)
    ·
      refine ⟨48163247090209778032916713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 256870651147785482842222469 48163247090209778032916713)
      ·
        refine ⟨36122435317657333524687535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48163247090209778032916713 36122435317657333524687535)
        ·
          refine ⟨54183652976486000287031303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36122435317657333524687535 54183652976486000287031303)
          ·
            refine ⟨81275479464729000430546955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54183652976486000287031303 81275479464729000430546955)
            ·
              refine ⟨121913219197093500645820433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81275479464729000430546955 121913219197093500645820433)
              ·
                refine ⟨91434914397820125484365325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121913219197093500645820433 91434914397820125484365325)
                ·
                  refine ⟨34288092899182547056636997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91434914397820125484365325 34288092899182547056636997)
                  ·
                    refine ⟨6429017418596727573119437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34288092899182547056636997 6429017418596727573119437)
                    ·
                      refine ⟨2410881531973772839919789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429017418596727573119437 2410881531973772839919789)
                      ·
                        rfl

theorem cell23_4695175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_4695175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695175 prefixEnd_4695175 := by exact prefixLift 4695175
  have htrace : WordTrace (prefixWord ++ tailWord_4695175) baseStart_4695175 baseEnd_4695175 := by
    simpa [prefixWord, tailWord_4695175, baseEnd_4695175] using wordTrace_append hprefix tailTrace_4695175
  have hstable : (prefixWord ++ tailWord_4695175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695175).length < 2 ^ (prefixWord ++ tailWord_4695175).sum := by decide
  have hdescent : baseEnd_4695175 < baseStart_4695175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695199 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 3, 4]
def baseStart_4695199 : Nat := 118140960795 + 4695199 * 2 ^ 59
def prefixEnd_4695199 : Nat := 4983230072969 + 3 ^ 40 * 4695199 * 2
def baseEnd_4695199 : Nat := 803631285169826915339893

theorem tailTrace_4695199 : CollatzResearch.WordTrace tailWord_4695199 prefixEnd_4695199 803631285169826915339893 := by
  unfold tailWord_4695199
  simp only [CollatzResearch.WordTrace]
  refine ⟨171247976117103373993688651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114165317411402249329125767 171247976117103373993688651)
  ·
    refine ⟨256871964175655060990532977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171247976117103373993688651 256871964175655060990532977)
    ·
      refine ⟨192653973131741295742899733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256871964175655060990532977 192653973131741295742899733)
      ·
        refine ⟨9030654990550373237948425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192653973131741295742899733 9030654990550373237948425)
        ·
          refine ⟨6772991242912779928461319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9030654990550373237948425 6772991242912779928461319)
          ·
            refine ⟨10159486864369169892691979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772991242912779928461319 10159486864369169892691979)
            ·
              refine ⟨15239230296553754839037969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159486864369169892691979 15239230296553754839037969)
              ·
                refine ⟨11429422722415316129278477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15239230296553754839037969 11429422722415316129278477)
                ·
                  refine ⟨4286033520905743548479429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11429422722415316129278477 4286033520905743548479429)
                  ·
                    refine ⟨803631285169826915339893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4286033520905743548479429 803631285169826915339893)
                    ·
                      rfl

theorem cell23_4695199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_4695199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695199 prefixEnd_4695199 := by exact prefixLift 4695199
  have htrace : WordTrace (prefixWord ++ tailWord_4695199) baseStart_4695199 baseEnd_4695199 := by
    simpa [prefixWord, tailWord_4695199, baseEnd_4695199] using wordTrace_append hprefix tailTrace_4695199
  have hstable : (prefixWord ++ tailWord_4695199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695199).length < 2 ^ (prefixWord ++ tailWord_4695199).sum := by decide
  have hdescent : baseEnd_4695199 < baseStart_4695199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695272 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 6, 4]
def baseStart_4695272 : Nat := 118140960795 + 4695272 * 2 ^ 59
def prefixEnd_4695272 : Nat := 4983230072969 + 3 ^ 40 * 4695272 * 2
def baseEnd_4695272 : Nat := 803643779865752986802281

theorem tailTrace_4695272 : CollatzResearch.WordTrace tailWord_4695272 prefixEnd_4695272 803643779865752986802281 := by
  unfold tailWord_4695272
  simp only [CollatzResearch.WordTrace]
  refine ⟨85625319322919453730548035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114167092430559271640730713 85625319322919453730548035)
  ·
    refine ⟨128437978984379180595822053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85625319322919453730548035 128437978984379180595822053)
    ·
      refine ⟨24082121059571096361716635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128437978984379180595822053 24082121059571096361716635)
      ·
        refine ⟨36123181589356644542574953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24082121059571096361716635 36123181589356644542574953)
        ·
          refine ⟨27092386192017483406931215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36123181589356644542574953 27092386192017483406931215)
          ·
            refine ⟨40638579288026225110396823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27092386192017483406931215 40638579288026225110396823)
            ·
              refine ⟨60957868932039337665595235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40638579288026225110396823 60957868932039337665595235)
              ·
                refine ⟨91436803398059006498392853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60957868932039337665595235 91436803398059006498392853)
                ·
                  refine ⟨4286100159284015929612165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91436803398059006498392853 4286100159284015929612165)
                  ·
                    refine ⟨803643779865752986802281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4286100159284015929612165 803643779865752986802281)
                    ·
                      rfl

theorem cell23_4695272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_4695272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695272 prefixEnd_4695272 := by exact prefixLift 4695272
  have htrace : WordTrace (prefixWord ++ tailWord_4695272) baseStart_4695272 baseEnd_4695272 := by
    simpa [prefixWord, tailWord_4695272, baseEnd_4695272] using wordTrace_append hprefix tailTrace_4695272
  have hstable : (prefixWord ++ tailWord_4695272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695272).length < 2 ^ (prefixWord ++ tailWord_4695272).sum := by decide
  have hdescent : baseEnd_4695272 < baseStart_4695272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695305 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_4695305 : Nat := 118140960795 + 4695305 * 2 ^ 59
def prefixEnd_4695305 : Nat := 4983230072969 + 3 ^ 40 * 4695305 * 2
def baseEnd_4695305 : Nat := 2410948284458857331294191

theorem tailTrace_4695305 : CollatzResearch.WordTrace tailWord_4695305 prefixEnd_4695305 2410948284458857331294191 := by
  unfold tailWord_4695305
  simp only [CollatzResearch.WordTrace]
  refine ⟨171251842254719354097047369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114167894836479569398031579 171251842254719354097047369)
  ·
    refine ⟨128438881691039515572785527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171251842254719354097047369 128438881691039515572785527)
    ·
      refine ⟨192658322536559273359178291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128438881691039515572785527 192658322536559273359178291)
      ·
        refine ⟨288987483804838910038767437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192658322536559273359178291 288987483804838910038767437)
        ·
          refine ⟨108370306426814591264537789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 288987483804838910038767437 108370306426814591264537789)
          ·
            refine ⟨40638864910055471724201671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108370306426814591264537789 40638864910055471724201671)
            ·
              refine ⟨60958297365083207586302507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40638864910055471724201671 60958297365083207586302507)
              ·
                refine ⟨91437446047624811379453761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60958297365083207586302507 91437446047624811379453761)
                ·
                  refine ⟨68578084535718608534590321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91437446047624811379453761 68578084535718608534590321)
                  ·
                    refine ⟨51433563401788956400942741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68578084535718608534590321 51433563401788956400942741)
                    ·
                      refine ⟨2410948284458857331294191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51433563401788956400942741 2410948284458857331294191)
                      ·
                        rfl

theorem cell23_4695305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_4695305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695305 prefixEnd_4695305 := by exact prefixLift 4695305
  have htrace : WordTrace (prefixWord ++ tailWord_4695305) baseStart_4695305 baseEnd_4695305 := by
    simpa [prefixWord, tailWord_4695305, baseEnd_4695305] using wordTrace_append hprefix tailTrace_4695305
  have hstable : (prefixWord ++ tailWord_4695305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695305).length < 2 ^ (prefixWord ++ tailWord_4695305).sum := by decide
  have hdescent : baseEnd_4695305 < baseStart_4695305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695346 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_4695346 : Nat := 118140960795 + 4695346 * 2 ^ 59
def prefixEnd_4695346 : Nat := 4983230072969 + 3 ^ 40 * 4695346 * 2
def baseEnd_4695346 : Nat := 2410969337165691670881503

theorem tailTrace_4695346 : CollatzResearch.WordTrace tailWord_4695346 prefixEnd_4695346 2410969337165691670881503 := by
  unfold tailWord_4695346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42813334411892704524822473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114168891765047212066193261 42813334411892704524822473)
  ·
    refine ⟨32110000808919528393616855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42813334411892704524822473 32110000808919528393616855)
    ·
      refine ⟨48165001213379292590425283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32110000808919528393616855 48165001213379292590425283)
      ·
        refine ⟨72247501820068938885637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48165001213379292590425283 72247501820068938885637925)
        ·
          refine ⟨13546406591262926041057111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72247501820068938885637925 13546406591262926041057111)
          ·
            refine ⟨20319609886894389061585667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13546406591262926041057111 20319609886894389061585667)
            ·
              refine ⟨30479414830341583592378501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20319609886894389061585667 30479414830341583592378501)
              ·
                refine ⟨5714890280689046923570969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30479414830341583592378501 5714890280689046923570969)
                ·
                  refine ⟨4286167710516785192678227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5714890280689046923570969 4286167710516785192678227)
                  ·
                    refine ⟨6429251565775177789017341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4286167710516785192678227 6429251565775177789017341)
                    ·
                      refine ⟨2410969337165691670881503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429251565775177789017341 2410969337165691670881503)
                      ·
                        rfl

theorem cell23_4695346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_4695346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695346 prefixEnd_4695346 := by exact prefixLift 4695346
  have htrace : WordTrace (prefixWord ++ tailWord_4695346) baseStart_4695346 baseEnd_4695346 := by
    simpa [prefixWord, tailWord_4695346, baseEnd_4695346] using wordTrace_append hprefix tailTrace_4695346
  have hstable : (prefixWord ++ tailWord_4695346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695346).length < 2 ^ (prefixWord ++ tailWord_4695346).sum := by decide
  have hdescent : baseEnd_4695346 < baseStart_4695346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695369 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 4, 2]
def baseStart_4695369 : Nat := 118140960795 + 4695369 * 2 ^ 59
def prefixEnd_4695369 : Nat := 4983230072969 + 3 ^ 40 * 4695369 * 2
def baseEnd_4695369 : Nat := 2410981147220745080893897

theorem tailTrace_4695369 : CollatzResearch.WordTrace tailWord_4695369 prefixEnd_4695369 2410981147220745080893897 := by
  unfold tailWord_4695369
  simp only [CollatzResearch.WordTrace]
  refine ⟨171254176526487493027377161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114169451017658328684918107 171254176526487493027377161)
  ·
    refine ⟨128440632394865619770532871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171254176526487493027377161 128440632394865619770532871)
    ·
      refine ⟨192660948592298429655799307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128440632394865619770532871 192660948592298429655799307)
      ·
        refine ⟨288991422888447644483698961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192660948592298429655799307 288991422888447644483698961)
        ·
          refine ⟨216743567166335733362774221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288991422888447644483698961 216743567166335733362774221)
          ·
            refine ⟨81278837687375900011040333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216743567166335733362774221 81278837687375900011040333)
            ·
              refine ⟨30479564132765962504140125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81278837687375900011040333 30479564132765962504140125)
              ·
                refine ⟨11429836549787235939052547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30479564132765962504140125 11429836549787235939052547)
                ·
                  refine ⟨17144754824680853908578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11429836549787235939052547 17144754824680853908578821)
                  ·
                    refine ⟨3214641529627660107858529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17144754824680853908578821 3214641529627660107858529)
                    ·
                      refine ⟨2410981147220745080893897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214641529627660107858529 2410981147220745080893897)
                      ·
                        rfl

theorem cell23_4695369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 4, 2].length) (baseStart_4695369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695369 prefixEnd_4695369 := by exact prefixLift 4695369
  have htrace : WordTrace (prefixWord ++ tailWord_4695369) baseStart_4695369 baseEnd_4695369 := by
    simpa [prefixWord, tailWord_4695369, baseEnd_4695369] using wordTrace_append hprefix tailTrace_4695369
  have hstable : (prefixWord ++ tailWord_4695369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695369).length < 2 ^ (prefixWord ++ tailWord_4695369).sum := by decide
  have hdescent : baseEnd_4695369 < baseStart_4695369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695409 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 5]
def baseStart_4695409 : Nat := 118140960795 + 4695409 * 2 ^ 59
def prefixEnd_4695409 : Nat := 4983230072969 + 3 ^ 40 * 4695409 * 2
def baseEnd_4695409 : Nat := 267889076271880547154857

theorem tailTrace_4695409 : CollatzResearch.WordTrace tailWord_4695409 prefixEnd_4695409 267889076271880547154857 := by
  unfold tailWord_4695409
  simp only [CollatzResearch.WordTrace]
  refine ⟨171255635446342579858833281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114170423630895053239222187 171255635446342579858833281)
  ·
    refine ⟨128441726584756934894124961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171255635446342579858833281 128441726584756934894124961)
    ·
      refine ⟨96331294938567701170593721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128441726584756934894124961 96331294938567701170593721)
      ·
        refine ⟨72248471203925775877945291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96331294938567701170593721 72248471203925775877945291)
        ·
          refine ⟨108372706805888663816917937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72248471203925775877945291 108372706805888663816917937)
          ·
            refine ⟨81279530104416497862688453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108372706805888663816917937 81279530104416497862688453)
            ·
              refine ⟨15239911894578093349254085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81279530104416497862688453 15239911894578093349254085)
              ·
                refine ⟨2857483480233392502985141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15239911894578093349254085 2857483480233392502985141)
                ·
                  refine ⟨267889076271880547154857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857483480233392502985141 267889076271880547154857)
                  ·
                    rfl

theorem cell23_4695409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 5].length) (baseStart_4695409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695409 prefixEnd_4695409 := by exact prefixLift 4695409
  have htrace : WordTrace (prefixWord ++ tailWord_4695409) baseStart_4695409 baseEnd_4695409 := by
    simpa [prefixWord, tailWord_4695409, baseEnd_4695409] using wordTrace_append hprefix tailTrace_4695409
  have hstable : (prefixWord ++ tailWord_4695409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695409).length < 2 ^ (prefixWord ++ tailWord_4695409).sum := by decide
  have hdescent : baseEnd_4695409 < baseStart_4695409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695426 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_4695426 : Nat := 118140960795 + 4695426 * 2 ^ 59
def prefixEnd_4695426 : Nat := 4983230072969 + 3 ^ 40 * 4695426 * 2
def baseEnd_4695426 : Nat := 267890046179783484209015

theorem tailTrace_4695426 : CollatzResearch.WordTrace tailWord_4695426 prefixEnd_4695426 267890046179783484209015 := by
  unfold tailWord_4695426
  simp only [CollatzResearch.WordTrace]
  refine ⟨42814063871820247940550533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114170836991520661174801421 42814063871820247940550533)
  ·
    refine ⟨8027636975966296488853225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42814063871820247940550533 8027636975966296488853225)
    ·
      refine ⟨6020727731974722366639919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8027636975966296488853225 6020727731974722366639919)
      ·
        refine ⟨9031091597962083549959879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6020727731974722366639919 9031091597962083549959879)
        ·
          refine ⟨13546637396943125324939819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031091597962083549959879 13546637396943125324939819)
          ·
            refine ⟨20319956095414687987409729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13546637396943125324939819 20319956095414687987409729)
            ·
              refine ⟨15239967071561015990557297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20319956095414687987409729 15239967071561015990557297)
              ·
                refine ⟨11429975303670761992917973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15239967071561015990557297 11429975303670761992917973)
                ·
                  refine ⟨267890046179783484209015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11429975303670761992917973 267890046179783484209015)
                  ·
                    rfl

theorem cell23_4695426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_4695426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695426 prefixEnd_4695426 := by exact prefixLift 4695426
  have htrace : WordTrace (prefixWord ++ tailWord_4695426) baseStart_4695426 baseEnd_4695426 := by
    simpa [prefixWord, tailWord_4695426, baseEnd_4695426] using wordTrace_append hprefix tailTrace_4695426
  have hstable : (prefixWord ++ tailWord_4695426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695426).length < 2 ^ (prefixWord ++ tailWord_4695426).sum := by decide
  have hdescent : baseEnd_4695426 < baseStart_4695426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695429 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_4695429 : Nat := 118140960795 + 4695429 * 2 ^ 59
def prefixEnd_4695429 : Nat := 4983230072969 + 3 ^ 40 * 4695429 * 2
def baseEnd_4695429 : Nat := 2411011956060014846143621

theorem tailTrace_4695429 : CollatzResearch.WordTrace tailWord_4695429 prefixEnd_4695429 2411011956060014846143621 := by
  unfold tailWord_4695429
  simp only [CollatzResearch.WordTrace]
  refine ⟨171256364906270123274561341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114170909937513415516374227 171256364906270123274561341)
  ·
    refine ⟨64221136839851296227960503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171256364906270123274561341 64221136839851296227960503)
    ·
      refine ⟨96331705259776944341940755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64221136839851296227960503 96331705259776944341940755)
      ·
        refine ⟨144497557889665416512911133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96331705259776944341940755 144497557889665416512911133)
        ·
          refine ⟨54186584208624531192341675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144497557889665416512911133 54186584208624531192341675)
          ·
            refine ⟨81279876312936796788512513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54186584208624531192341675 81279876312936796788512513)
            ·
              refine ⟨60959907234702597591384385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81279876312936796788512513 60959907234702597591384385)
              ·
                refine ⟨45719930426026948193538289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60959907234702597591384385 45719930426026948193538289)
                ·
                  refine ⟨34289947819520211145153717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45719930426026948193538289 34289947819520211145153717)
                  ·
                    refine ⟨3214682608080019794858161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34289947819520211145153717 3214682608080019794858161)
                    ·
                      refine ⟨2411011956060014846143621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214682608080019794858161 2411011956060014846143621)
                      ·
                        rfl

theorem cell23_4695429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_4695429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695429 prefixEnd_4695429 := by exact prefixLift 4695429
  have htrace : WordTrace (prefixWord ++ tailWord_4695429) baseStart_4695429 baseEnd_4695429 := by
    simpa [prefixWord, tailWord_4695429, baseEnd_4695429] using wordTrace_append hprefix tailTrace_4695429
  have hstable : (prefixWord ++ tailWord_4695429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695429).length < 2 ^ (prefixWord ++ tailWord_4695429).sum := by decide
  have hdescent : baseEnd_4695429 < baseStart_4695429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695459 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4]
def baseStart_4695459 : Nat := 118140960795 + 4695459 * 2 ^ 59
def prefixEnd_4695459 : Nat := 4983230072969 + 3 ^ 40 * 4695459 * 2
def baseEnd_4695459 : Nat := 2411027360479649728768483

theorem tailTrace_4695459 : CollatzResearch.WordTrace tailWord_4695459 prefixEnd_4695459 2411027360479649728768483 := by
  unfold tailWord_4695459
  simp only [CollatzResearch.WordTrace]
  refine ⟨171257459096161438398153431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114171639397440958932102287 171257459096161438398153431)
  ·
    refine ⟨256886188644242157597230147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171257459096161438398153431 256886188644242157597230147)
    ·
      refine ⟨385329282966363236395845221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256886188644242157597230147 385329282966363236395845221)
      ·
        refine ⟨72249240556193106824220979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385329282966363236395845221 72249240556193106824220979)
        ·
          refine ⟨108373860834289660236331469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72249240556193106824220979 108373860834289660236331469)
          ·
            refine ⟨40640197812858622588624301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108373860834289660236331469 40640197812858622588624301)
            ·
              refine ⟨15240074179821983470734113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40640197812858622588624301 15240074179821983470734113)
              ·
                refine ⟨11430055634866487603050585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15240074179821983470734113 11430055634866487603050585)
                ·
                  refine ⟨8572541726149865702287939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11430055634866487603050585 8572541726149865702287939)
                  ·
                    refine ⟨12858812589224798553431909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8572541726149865702287939 12858812589224798553431909)
                    ·
                      refine ⟨2411027360479649728768483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12858812589224798553431909 2411027360479649728768483)
                      ·
                        rfl

theorem cell23_4695459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_4695459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695459 prefixEnd_4695459 := by exact prefixLift 4695459
  have htrace : WordTrace (prefixWord ++ tailWord_4695459) baseStart_4695459 baseEnd_4695459 := by
    simpa [prefixWord, tailWord_4695459, baseEnd_4695459] using wordTrace_append hprefix tailTrace_4695459
  have hstable : (prefixWord ++ tailWord_4695459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695459).length < 2 ^ (prefixWord ++ tailWord_4695459).sum := by decide
  have hdescent : baseEnd_4695459 < baseStart_4695459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695472 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_4695472 : Nat := 118140960795 + 4695472 * 2 ^ 59
def prefixEnd_4695472 : Nat := 4983230072969 + 3 ^ 40 * 4695472 * 2
def baseEnd_4695472 : Nat := 2411034035728158177905923

theorem tailTrace_4695472 : CollatzResearch.WordTrace tailWord_4695472 prefixEnd_4695472 2411034035728158177905923 := by
  unfold tailWord_4695472
  simp only [CollatzResearch.WordTrace]
  refine ⟨85628966622557170809188335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114171955496742894412251113 85628966622557170809188335)
  ·
    refine ⟨128443449933835756213782503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85628966622557170809188335 128443449933835756213782503)
    ·
      refine ⟨192665174900753634320673755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128443449933835756213782503 192665174900753634320673755)
      ·
        refine ⟨288997762351130451481010633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192665174900753634320673755 288997762351130451481010633)
        ·
          refine ⟨216748321763347838610757975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288997762351130451481010633 216748321763347838610757975)
          ·
            refine ⟨325122482645021757916136963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216748321763347838610757975 325122482645021757916136963)
            ·
              refine ⟨487683723967532636874205445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325122482645021757916136963 487683723967532636874205445)
              ·
                refine ⟨91440698243912369413913521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487683723967532636874205445 91440698243912369413913521)
                ·
                  refine ⟨68580523682934277060435141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91440698243912369413913521 68580523682934277060435141)
                  ·
                    refine ⟨12858848190550176948831589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68580523682934277060435141 12858848190550176948831589)
                    ·
                      refine ⟨2411034035728158177905923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12858848190550176948831589 2411034035728158177905923)
                      ·
                        rfl

theorem cell23_4695472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_4695472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695472 prefixEnd_4695472 := by exact prefixLift 4695472
  have htrace : WordTrace (prefixWord ++ tailWord_4695472) baseStart_4695472 baseEnd_4695472 := by
    simpa [prefixWord, tailWord_4695472, baseEnd_4695472] using wordTrace_append hprefix tailTrace_4695472
  have hstable : (prefixWord ++ tailWord_4695472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695472).length < 2 ^ (prefixWord ++ tailWord_4695472).sum := by decide
  have hdescent : baseEnd_4695472 < baseStart_4695472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695479 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_4695479 : Nat := 118140960795 + 4695479 * 2 ^ 59
def prefixEnd_4695479 : Nat := 4983230072969 + 3 ^ 40 * 4695479 * 2
def baseEnd_4695479 : Nat := 2411037630092739650518391

theorem tailTrace_4695479 : CollatzResearch.WordTrace tailWord_4695479 prefixEnd_4695479 2411037630092739650518391 := by
  unfold tailWord_4695479
  simp only [CollatzResearch.WordTrace]
  refine ⟨171258188556088981813881491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114172125704059321209254327 171258188556088981813881491)
  ·
    refine ⟨256887282834133472720822237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171258188556088981813881491 256887282834133472720822237)
    ·
      refine ⟨96332731062800052270308339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 256887282834133472720822237 96332731062800052270308339)
      ·
        refine ⟨144499096594200078405462509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96332731062800052270308339 144499096594200078405462509)
        ·
          refine ⟨54187161222825029402048441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144499096594200078405462509 54187161222825029402048441)
          ·
            refine ⟨40640370917118772051536331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54187161222825029402048441 40640370917118772051536331)
            ·
              refine ⟨60960556375678158077304497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40640370917118772051536331 60960556375678158077304497)
              ·
                refine ⟨45720417281758618557978373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60960556375678158077304497 45720417281758618557978373)
                ·
                  refine ⟨8572578240329740979620945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45720417281758618557978373 8572578240329740979620945)
                  ·
                    refine ⟨6429433680247305734715709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8572578240329740979620945 6429433680247305734715709)
                    ·
                      refine ⟨2411037630092739650518391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429433680247305734715709 2411037630092739650518391)
                      ·
                        rfl

theorem cell23_4695479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_4695479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695479 prefixEnd_4695479 := by exact prefixLift 4695479
  have htrace : WordTrace (prefixWord ++ tailWord_4695479) baseStart_4695479 baseEnd_4695479 := by
    simpa [prefixWord, tailWord_4695479, baseEnd_4695479] using wordTrace_append hprefix tailTrace_4695479
  have hstable : (prefixWord ++ tailWord_4695479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695479).length < 2 ^ (prefixWord ++ tailWord_4695479).sum := by decide
  have hdescent : baseEnd_4695479 < baseStart_4695479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695496 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_4695496 : Nat := 118140960795 + 4695496 * 2 ^ 59
def prefixEnd_4695496 : Nat := 4983230072969 + 3 ^ 40 * 4695496 * 2
def baseEnd_4695496 : Nat := 2411046359263866084005813

theorem tailTrace_4695496 : CollatzResearch.WordTrace tailWord_4695496 prefixEnd_4695496 2411046359263866084005813 := by
  unfold tailWord_4695496
  simp only [CollatzResearch.WordTrace]
  refine ⟨85629404298513696858625171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114172539064684929144833561 85629404298513696858625171)
  ·
    refine ⟨128444106447770545287937757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85629404298513696858625171 128444106447770545287937757)
    ·
      refine ⟨48166539917913954482976659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128444106447770545287937757 48166539917913954482976659)
      ·
        refine ⟨72249809876870931724464989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48166539917913954482976659 72249809876870931724464989)
        ·
          refine ⟨27093678703826599396674371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72249809876870931724464989 27093678703826599396674371)
          ·
            refine ⟨40640518055739899095011557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27093678703826599396674371 40640518055739899095011557)
            ·
              refine ⟨7620097135451231080314667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40640518055739899095011557 7620097135451231080314667)
              ·
                refine ⟨11430145703176846620472001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7620097135451231080314667 11430145703176846620472001)
                ·
                  refine ⟨8572609277382634965354001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11430145703176846620472001 8572609277382634965354001)
                  ·
                    refine ⟨6429456958036976224015501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8572609277382634965354001 6429456958036976224015501)
                    ·
                      refine ⟨2411046359263866084005813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429456958036976224015501 2411046359263866084005813)
                      ·
                        rfl

theorem cell23_4695496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_4695496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695496 prefixEnd_4695496 := by exact prefixLift 4695496
  have htrace : WordTrace (prefixWord ++ tailWord_4695496) baseStart_4695496 baseEnd_4695496 := by
    simpa [prefixWord, tailWord_4695496, baseEnd_4695496] using wordTrace_append hprefix tailTrace_4695496
  have hstable : (prefixWord ++ tailWord_4695496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695496).length < 2 ^ (prefixWord ++ tailWord_4695496).sum := by decide
  have hdescent : baseEnd_4695496 < baseStart_4695496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695553 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_4695553 : Nat := 118140960795 + 4695553 * 2 ^ 59
def prefixEnd_4695553 : Nat := 4983230072969 + 3 ^ 40 * 4695553 * 2
def baseEnd_4695553 : Nat := 2411075627661172360993051

theorem tailTrace_4695553 : CollatzResearch.WordTrace tailWord_4695553 prefixEnd_4695553 2411075627661172360993051 := by
  unfold tailWord_4695553
  simp only [CollatzResearch.WordTrace]
  refine ⟨171260887557820892452075313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114173925038547261634716875 171260887557820892452075313)
  ·
    refine ⟨128445665668365669339056485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171260887557820892452075313 128445665668365669339056485)
    ·
      refine ⟨24083562312818563001073091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128445665668365669339056485 24083562312818563001073091)
      ·
        refine ⟨36125343469227844501609637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24083562312818563001073091 36125343469227844501609637)
        ·
          refine ⟨6773501900480220844051807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36125343469227844501609637 6773501900480220844051807)
          ·
            refine ⟨10160252850720331266077711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6773501900480220844051807 10160252850720331266077711)
            ·
              refine ⟨15240379276080496899116567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10160252850720331266077711 15240379276080496899116567)
              ·
                refine ⟨22860568914120745348674851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15240379276080496899116567 22860568914120745348674851)
                ·
                  refine ⟨34290853371181118023012277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22860568914120745348674851 34290853371181118023012277)
                  ·
                    refine ⟨3214767503548229814657401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34290853371181118023012277 3214767503548229814657401)
                    ·
                      refine ⟨2411075627661172360993051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214767503548229814657401 2411075627661172360993051)
                      ·
                        rfl

theorem cell23_4695553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_4695553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695553 prefixEnd_4695553 := by exact prefixLift 4695553
  have htrace : WordTrace (prefixWord ++ tailWord_4695553) baseStart_4695553 baseEnd_4695553 := by
    simpa [prefixWord, tailWord_4695553, baseEnd_4695553] using wordTrace_append hprefix tailTrace_4695553
  have hstable : (prefixWord ++ tailWord_4695553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695553).length < 2 ^ (prefixWord ++ tailWord_4695553).sum := by decide
  have hdescent : baseEnd_4695553 < baseStart_4695553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695569 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_4695569 : Nat := 118140960795 + 4695569 * 2 ^ 59
def prefixEnd_4695569 : Nat := 4983230072969 + 3 ^ 40 * 4695569 * 2
def baseEnd_4695569 : Nat := 2411083843351644298392977

theorem tailTrace_4695569 : CollatzResearch.WordTrace tailWord_4695569 prefixEnd_4695569 2411083843351644298392977 := by
  unfold tailWord_4695569
  simp only [CollatzResearch.WordTrace]
  refine ⟨171261471125762927184657761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114174314083841951456438507 171261471125762927184657761)
  ·
    refine ⟨128446103344322195388493321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171261471125762927184657761 128446103344322195388493321)
    ·
      refine ⟨96334577508241646541369991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128446103344322195388493321 96334577508241646541369991)
      ·
        refine ⟨144501866262362469812054987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96334577508241646541369991 144501866262362469812054987)
        ·
          refine ⟨216752799393543704718082481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144501866262362469812054987 216752799393543704718082481)
          ·
            refine ⟨162564599545157778538561861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216752799393543704718082481 162564599545157778538561861)
            ·
              refine ⟨30480862414717083475980349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162564599545157778538561861 30480862414717083475980349)
              ·
                refine ⟨11430323405518906303492631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30480862414717083475980349 11430323405518906303492631)
                ·
                  refine ⟨17145485108278359455238947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11430323405518906303492631 17145485108278359455238947)
                  ·
                    refine ⟨25718227662417539182858421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17145485108278359455238947 25718227662417539182858421)
                    ·
                      refine ⟨2411083843351644298392977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25718227662417539182858421 2411083843351644298392977)
                      ·
                        rfl

theorem cell23_4695569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_4695569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695569 prefixEnd_4695569 := by exact prefixLift 4695569
  have htrace : WordTrace (prefixWord ++ tailWord_4695569) baseStart_4695569 baseEnd_4695569 := by
    simpa [prefixWord, tailWord_4695569, baseEnd_4695569] using wordTrace_append hprefix tailTrace_4695569
  have hstable : (prefixWord ++ tailWord_4695569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695569).length < 2 ^ (prefixWord ++ tailWord_4695569).sum := by decide
  have hdescent : baseEnd_4695569 < baseStart_4695569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695583 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 3, 2, 2]
def baseStart_4695583 : Nat := 118140960795 + 4695583 * 2 ^ 59
def prefixEnd_4695583 : Nat := 4983230072969 + 3 ^ 40 * 4695583 * 2
def baseEnd_4695583 : Nat := 2411091032080807243617913

theorem tailTrace_4695583 : CollatzResearch.WordTrace tailWord_4695583 prefixEnd_4695583 2411091032080807243617913 := by
  unfold tailWord_4695583
  simp only [CollatzResearch.WordTrace]
  refine ⟨171261981747712207575667403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114174654498474805050444935 171261981747712207575667403)
  ·
    refine ⟨256892972621568311363501105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171261981747712207575667403 256892972621568311363501105)
    ·
      refine ⟨192669729466176233522625829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256892972621568311363501105 192669729466176233522625829)
      ·
        refine ⟨36125574274908043785492343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192669729466176233522625829 36125574274908043785492343)
        ·
          refine ⟨54188361412362065678238515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36125574274908043785492343 54188361412362065678238515)
          ·
            refine ⟨81282542118543098517357773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54188361412362065678238515 81282542118543098517357773)
            ·
              refine ⟨30480953294453661944009165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81282542118543098517357773 30480953294453661944009165)
              ·
                refine ⟨11430357485420123229003437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30480953294453661944009165 11430357485420123229003437)
                ·
                  refine ⟨4286384057032546210876289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11430357485420123229003437 4286384057032546210876289)
                  ·
                    refine ⟨3214788042774409658157217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4286384057032546210876289 3214788042774409658157217)
                    ·
                      refine ⟨2411091032080807243617913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214788042774409658157217 2411091032080807243617913)
                      ·
                        rfl

theorem cell23_4695583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_4695583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695583 prefixEnd_4695583 := by exact prefixLift 4695583
  have htrace : WordTrace (prefixWord ++ tailWord_4695583) baseStart_4695583 baseEnd_4695583 := by
    simpa [prefixWord, tailWord_4695583, baseEnd_4695583] using wordTrace_append hprefix tailTrace_4695583
  have hstable : (prefixWord ++ tailWord_4695583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695583).length < 2 ^ (prefixWord ++ tailWord_4695583).sum := by decide
  have hdescent : baseEnd_4695583 < baseStart_4695583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695586 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4695586 : Nat := 118140960795 + 4695586 * 2 ^ 59
def prefixEnd_4695586 : Nat := 4983230072969 + 3 ^ 40 * 4695586 * 2
def baseEnd_4695586 : Nat := 2411092572522770731880399

theorem tailTrace_4695586 : CollatzResearch.WordTrace tailWord_4695586 prefixEnd_4695586 2411092572522770731880399 := by
  unfold tailWord_4695586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42815522791675334772006653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114174727444467559392017741 42815522791675334772006653)
  ·
    refine ⟨16055821046878250539502495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42815522791675334772006653 16055821046878250539502495)
    ·
      refine ⟨24083731570317375809253743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16055821046878250539502495 24083731570317375809253743)
      ·
        refine ⟨36125597355476063713880615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24083731570317375809253743 36125597355476063713880615)
        ·
          refine ⟨54188396033214095570820923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36125597355476063713880615 54188396033214095570820923)
          ·
            refine ⟨81282594049821143356231385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54188396033214095570820923 81282594049821143356231385)
            ·
              refine ⟨60961945537365857517173539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81282594049821143356231385 60961945537365857517173539)
              ·
                refine ⟨91442918306048786275760309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60961945537365857517173539 91442918306048786275760309)
                ·
                  refine ⟨8572773591192073713352529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91442918306048786275760309 8572773591192073713352529)
                  ·
                    refine ⟨6429580193394055285014397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8572773591192073713352529 6429580193394055285014397)
                    ·
                      refine ⟨2411092572522770731880399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429580193394055285014397 2411092572522770731880399)
                      ·
                        rfl

theorem cell23_4695586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4695586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695586 prefixEnd_4695586 := by exact prefixLift 4695586
  have htrace : WordTrace (prefixWord ++ tailWord_4695586) baseStart_4695586 baseEnd_4695586 := by
    simpa [prefixWord, tailWord_4695586, baseEnd_4695586] using wordTrace_append hprefix tailTrace_4695586
  have hstable : (prefixWord ++ tailWord_4695586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695586).length < 2 ^ (prefixWord ++ tailWord_4695586).sum := by decide
  have hdescent : baseEnd_4695586 < baseStart_4695586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695603 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 3]
def baseStart_4695603 : Nat := 118140960795 + 4695603 * 2 ^ 59
def prefixEnd_4695603 : Nat := 4983230072969 + 3 ^ 40 * 4695603 * 2
def baseEnd_4695603 : Nat := 2411101301693897165367821

theorem tailTrace_4695603 : CollatzResearch.WordTrace tailWord_4695603 prefixEnd_4695603 2411101301693897165367821 := by
  unfold tailWord_4695603
  simp only [CollatzResearch.WordTrace]
  refine ⟨171262711207639750991395463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114175140805093167327596975 171262711207639750991395463)
  ·
    refine ⟨256894066811459626487093195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171262711207639750991395463 256894066811459626487093195)
    ·
      refine ⟨385341100217189439730639793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256894066811459626487093195 385341100217189439730639793)
      ·
        refine ⟨289005825162892079797979845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385341100217189439730639793 289005825162892079797979845)
        ·
          refine ⟨54188592218042264962121221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289005825162892079797979845 54188592218042264962121221)
          ·
            refine ⟨10160361040882924680397729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54188592218042264962121221 10160361040882924680397729)
            ·
              refine ⟨7620270780662193510298297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10160361040882924680397729 7620270780662193510298297)
              ·
                refine ⟨5715203085496645132723723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7620270780662193510298297 5715203085496645132723723)
                ·
                  refine ⟨8572804628244967699085585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715203085496645132723723 8572804628244967699085585)
                  ·
                    refine ⟨6429603471183725774314189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8572804628244967699085585 6429603471183725774314189)
                    ·
                      refine ⟨2411101301693897165367821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429603471183725774314189 2411101301693897165367821)
                      ·
                        rfl

theorem cell23_4695603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_4695603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695603 prefixEnd_4695603 := by exact prefixLift 4695603
  have htrace : WordTrace (prefixWord ++ tailWord_4695603) baseStart_4695603 baseEnd_4695603 := by
    simpa [prefixWord, tailWord_4695603, baseEnd_4695603] using wordTrace_append hprefix tailTrace_4695603
  have hstable : (prefixWord ++ tailWord_4695603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695603).length < 2 ^ (prefixWord ++ tailWord_4695603).sum := by decide
  have hdescent : baseEnd_4695603 < baseStart_4695603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695633 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_4695633 : Nat := 118140960795 + 4695633 * 2 ^ 59
def prefixEnd_4695633 : Nat := 4983230072969 + 3 ^ 40 * 4695633 * 2
def baseEnd_4695633 : Nat := 2411116706113532047992683

theorem tailTrace_4695633 : CollatzResearch.WordTrace tailWord_4695633 prefixEnd_4695633 2411116706113532047992683 := by
  unfold tailWord_4695633
  simp only [CollatzResearch.WordTrace]
  refine ⟨171263805397531066114987553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114175870265020710743325035 171263805397531066114987553)
  ·
    refine ⟨128447854048148299586240665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171263805397531066114987553 128447854048148299586240665)
    ·
      refine ⟨96335890536111224689680499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128447854048148299586240665 96335890536111224689680499)
      ·
        refine ⟨144503835804166837034520749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96335890536111224689680499 144503835804166837034520749)
        ·
          refine ⟨54188938426562563887945281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144503835804166837034520749 54188938426562563887945281)
          ·
            refine ⟨40641703819921922915958961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54188938426562563887945281 40641703819921922915958961)
            ·
              refine ⟨30481277864941442186969221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40641703819921922915958961 30481277864941442186969221)
              ·
                refine ⟨5715239599676520410056729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30481277864941442186969221 5715239599676520410056729)
                ·
                  refine ⟨4286429699757390307542547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715239599676520410056729 4286429699757390307542547)
                  ·
                    refine ⟨6429644549636085461313821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4286429699757390307542547 6429644549636085461313821)
                    ·
                      refine ⟨2411116706113532047992683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429644549636085461313821 2411116706113532047992683)
                      ·
                        rfl

theorem cell23_4695633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_4695633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695633 prefixEnd_4695633 := by exact prefixLift 4695633
  have htrace : WordTrace (prefixWord ++ tailWord_4695633) baseStart_4695633 baseEnd_4695633 := by
    simpa [prefixWord, tailWord_4695633, baseEnd_4695633] using wordTrace_append hprefix tailTrace_4695633
  have hstable : (prefixWord ++ tailWord_4695633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695633).length < 2 ^ (prefixWord ++ tailWord_4695633).sum := by decide
  have hdescent : baseEnd_4695633 < baseStart_4695633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695634 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_4695634 : Nat := 118140960795 + 4695634 * 2 ^ 59
def prefixEnd_4695634 : Nat := 4983230072969 + 3 ^ 40 * 4695634 * 2
def baseEnd_4695634 : Nat := 2411117219594186544080179

theorem tailTrace_4695634 : CollatzResearch.WordTrace tailWord_4695634 prefixEnd_4695634 2411117219594186544080179 := by
  unfold tailWord_4695634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42815960467631860821443489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114175894580351628857182637 42815960467631860821443489)
  ·
    refine ⟨32111970350723895616082617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42815960467631860821443489 32111970350723895616082617)
    ·
      refine ⟨24083977763042921712061963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32111970350723895616082617 24083977763042921712061963)
      ·
        refine ⟨36125966644564382568092945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24083977763042921712061963 36125966644564382568092945)
        ·
          refine ⟨27094474983423286926069709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36125966644564382568092945 27094474983423286926069709)
          ·
            refine ⟨10160428118783732597276141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27094474983423286926069709 10160428118783732597276141)
            ·
              refine ⟨3810160544543899723978553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10160428118783732597276141 3810160544543899723978553)
              ·
                refine ⟨2857620408407924792983915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810160544543899723978553 2857620408407924792983915)
                ·
                  refine ⟨4286430612611887189475873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857620408407924792983915 4286430612611887189475873)
                  ·
                    refine ⟨3214822959458915392106905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4286430612611887189475873 3214822959458915392106905)
                    ·
                      refine ⟨2411117219594186544080179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214822959458915392106905 2411117219594186544080179)
                      ·
                        rfl

theorem cell23_4695634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_4695634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695634 prefixEnd_4695634 := by exact prefixLift 4695634
  have htrace : WordTrace (prefixWord ++ tailWord_4695634) baseStart_4695634 baseEnd_4695634 := by
    simpa [prefixWord, tailWord_4695634, baseEnd_4695634] using wordTrace_append hprefix tailTrace_4695634
  have hstable : (prefixWord ++ tailWord_4695634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695634).length < 2 ^ (prefixWord ++ tailWord_4695634).sum := by decide
  have hdescent : baseEnd_4695634 < baseStart_4695634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695649 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_4695649 : Nat := 118140960795 + 4695649 * 2 ^ 59
def prefixEnd_4695649 : Nat := 4983230072969 + 3 ^ 40 * 4695649 * 2
def baseEnd_4695649 : Nat := 803708307268001328464203

theorem tailTrace_4695649 : CollatzResearch.WordTrace tailWord_4695649 prefixEnd_4695649 803708307268001328464203 := by
  unfold tailWord_4695649
  simp only [CollatzResearch.WordTrace]
  refine ⟨171264388965473100847570001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114176259310315400565046667 171264388965473100847570001)
  ·
    refine ⟨128448291724104825635677501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171264388965473100847570001 128448291724104825635677501)
    ·
      refine ⟨48168109396539309613379063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128448291724104825635677501 48168109396539309613379063)
      ·
        refine ⟨72252164094808964420068595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48168109396539309613379063 72252164094808964420068595)
        ·
          refine ⟨108378246142213446630102893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72252164094808964420068595 108378246142213446630102893)
          ·
            refine ⟨40641842303330042486288585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108378246142213446630102893 40641842303330042486288585)
            ·
              refine ⟨30481381727497531864716439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40641842303330042486288585 30481381727497531864716439)
              ·
                refine ⟨45722072591246297797074659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30481381727497531864716439 45722072591246297797074659)
                ·
                  refine ⟨68583108886869446695611989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45722072591246297797074659 68583108886869446695611989)
                  ·
                    refine ⟨803708307268001328464203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68583108886869446695611989 803708307268001328464203)
                    ·
                      rfl

theorem cell23_4695649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_4695649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695649 prefixEnd_4695649 := by exact prefixLift 4695649
  have htrace : WordTrace (prefixWord ++ tailWord_4695649) baseStart_4695649 baseEnd_4695649 := by
    simpa [prefixWord, tailWord_4695649, baseEnd_4695649] using wordTrace_append hprefix tailTrace_4695649
  have hstable : (prefixWord ++ tailWord_4695649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695649).length < 2 ^ (prefixWord ++ tailWord_4695649).sum := by decide
  have hdescent : baseEnd_4695649 < baseStart_4695649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695673 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 4, 2]
def baseStart_4695673 : Nat := 118140960795 + 4695673 * 2 ^ 59
def prefixEnd_4695673 : Nat := 4983230072969 + 3 ^ 40 * 4695673 * 2
def baseEnd_4695673 : Nat := 2411137245339711891492499

theorem tailTrace_4695673 : CollatzResearch.WordTrace tailWord_4695673 prefixEnd_4695673 2411137245339711891492499 := by
  unfold tailWord_4695673
  simp only [CollatzResearch.WordTrace]
  refine ⟨171265264317386152946443673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114176842878257435297629115 171265264317386152946443673)
  ·
    refine ⟨128448948238039614709832755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171265264317386152946443673 128448948238039614709832755)
    ·
      refine ⟨192673422357059422064749133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128448948238039614709832755 192673422357059422064749133)
      ·
        refine ⟨72252533383897283274280925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192673422357059422064749133 72252533383897283274280925)
        ·
          refine ⟨27094700018961481227855347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72252533383897283274280925 27094700018961481227855347)
          ·
            refine ⟨40642050028442221841783021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27094700018961481227855347 40642050028442221841783021)
            ·
              refine ⟨15240768760665833190668633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40642050028442221841783021 15240768760665833190668633)
              ·
                refine ⟨11430576570499374893001475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15240768760665833190668633 11430576570499374893001475)
                ·
                  refine ⟨17145864855749062339502213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11430576570499374893001475 17145864855749062339502213)
                  ·
                    refine ⟨3214849660452949188656665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17145864855749062339502213 3214849660452949188656665)
                    ·
                      refine ⟨2411137245339711891492499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214849660452949188656665 2411137245339711891492499)
                      ·
                        rfl

theorem cell23_4695673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_4695673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695673 prefixEnd_4695673 := by exact prefixLift 4695673
  have htrace : WordTrace (prefixWord ++ tailWord_4695673) baseStart_4695673 baseEnd_4695673 := by
    simpa [prefixWord, tailWord_4695673, baseEnd_4695673] using wordTrace_append hprefix tailTrace_4695673
  have hstable : (prefixWord ++ tailWord_4695673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695673).length < 2 ^ (prefixWord ++ tailWord_4695673).sum := by decide
  have hdescent : baseEnd_4695673 < baseStart_4695673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695677 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_4695677 : Nat := 118140960795 + 4695677 * 2 ^ 59
def prefixEnd_4695677 : Nat := 4983230072969 + 3 ^ 40 * 4695677 * 2
def baseEnd_4695677 : Nat := 2411139299262329875842481

theorem tailTrace_4695677 : CollatzResearch.WordTrace tailWord_4695677 prefixEnd_4695677 2411139299262329875842481 := by
  unfold tailWord_4695677
  simp only [CollatzResearch.WordTrace]
  refine ⟨171265410209371661629589285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114176940139581107753059523 171265410209371661629589285)
  ·
    refine ⟨32112264414257186555547991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171265410209371661629589285 32112264414257186555547991)
    ·
      refine ⟨48168396621385779833321987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32112264414257186555547991 48168396621385779833321987)
      ·
        refine ⟨72252594932078669749982981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48168396621385779833321987 72252594932078669749982981)
        ·
          refine ⟨13547361549764750578121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72252594932078669749982981 13547361549764750578121809)
          ·
            refine ⟨10160521162323562933591357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13547361549764750578121809 10160521162323562933591357)
            ·
              refine ⟨3810195435871336100096759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10160521162323562933591357 3810195435871336100096759)
              ·
                refine ⟨5715293153807004150145139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810195435871336100096759 5715293153807004150145139)
                ·
                  refine ⟨8572939730710506225217709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715293153807004150145139 8572939730710506225217709)
                  ·
                    refine ⟨3214852399016439834456641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8572939730710506225217709 3214852399016439834456641)
                    ·
                      refine ⟨2411139299262329875842481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214852399016439834456641 2411139299262329875842481)
                      ·
                        rfl

theorem cell23_4695677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_4695677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695677 prefixEnd_4695677 := by exact prefixLift 4695677
  have htrace : WordTrace (prefixWord ++ tailWord_4695677) baseStart_4695677 baseEnd_4695677 := by
    simpa [prefixWord, tailWord_4695677, baseEnd_4695677] using wordTrace_append hprefix tailTrace_4695677
  have hstable : (prefixWord ++ tailWord_4695677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695677).length < 2 ^ (prefixWord ++ tailWord_4695677).sum := by decide
  have hdescent : baseEnd_4695677 < baseStart_4695677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695689 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_4695689 : Nat := 118140960795 + 4695689 * 2 ^ 59
def prefixEnd_4695689 : Nat := 4983230072969 + 3 ^ 40 * 4695689 * 2
def baseEnd_4695689 : Nat := 2411145461030183828892425

theorem tailTrace_4695689 : CollatzResearch.WordTrace tailWord_4695689 prefixEnd_4695689 2411145461030183828892425 := by
  unfold tailWord_4695689
  simp only [CollatzResearch.WordTrace]
  refine ⟨171265847885328187679026121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114177231923552125119350747 171265847885328187679026121)
  ·
    refine ⟨128449385913996140759269591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171265847885328187679026121 128449385913996140759269591)
    ·
      refine ⟨192674078870994211138904387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128449385913996140759269591 192674078870994211138904387)
      ·
        refine ⟨289011118306491316708356581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192674078870994211138904387 289011118306491316708356581)
        ·
          refine ⟨54189584682467121882816859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289011118306491316708356581 54189584682467121882816859)
          ·
            refine ⟨81284377023700682824225289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54189584682467121882816859 81284377023700682824225289)
            ·
              refine ⟨60963282767775512118168967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81284377023700682824225289 60963282767775512118168967)
              ·
                refine ⟨91444924151663268177253451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60963282767775512118168967 91444924151663268177253451)
                ·
                  refine ⟨137167386227494902265880177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91444924151663268177253451 137167386227494902265880177)
                  ·
                    refine ⟨102875539670621176699410133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137167386227494902265880177 102875539670621176699410133)
                    ·
                      refine ⟨2411145461030183828892425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102875539670621176699410133 2411145461030183828892425)
                      ·
                        rfl

theorem cell23_4695689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_4695689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695689 prefixEnd_4695689 := by exact prefixLift 4695689
  have htrace : WordTrace (prefixWord ++ tailWord_4695689) baseStart_4695689 baseEnd_4695689 := by
    simpa [prefixWord, tailWord_4695689, baseEnd_4695689] using wordTrace_append hprefix tailTrace_4695689
  have hstable : (prefixWord ++ tailWord_4695689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695689).length < 2 ^ (prefixWord ++ tailWord_4695689).sum := by decide
  have hdescent : baseEnd_4695689 < baseStart_4695689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695739 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 10]
def baseStart_4695739 : Nat := 118140960795 + 4695739 * 2 ^ 59
def prefixEnd_4695739 : Nat := 4983230072969 + 3 ^ 40 * 4695739 * 2
def baseEnd_4695739 : Nat := 803723711687636211089065

theorem tailTrace_4695739 : CollatzResearch.WordTrace tailWord_4695739 prefixEnd_4695739 803723711687636211089065 := by
  unfold tailWord_4695739
  simp only [CollatzResearch.WordTrace]
  refine ⟨171267671535147046218346271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114178447690098030812230847 171267671535147046218346271)
  ·
    refine ⟨256901507302720569327519407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171267671535147046218346271 256901507302720569327519407)
    ·
      refine ⟨385352260954080853991279111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256901507302720569327519407 385352260954080853991279111)
      ·
        refine ⟨578028391431121280986918667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385352260954080853991279111 578028391431121280986918667)
        ·
          refine ⟨867042587146681921480378001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578028391431121280986918667 867042587146681921480378001)
          ·
            refine ⟨650281940360011441110283501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867042587146681921480378001 650281940360011441110283501)
            ·
              refine ⟨243855727635004290416356313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 650281940360011441110283501 243855727635004290416356313)
              ·
                refine ⟨182891795726253217812267235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243855727635004290416356313 182891795726253217812267235)
                ·
                  refine ⟨274337693589379826718400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182891795726253217812267235 274337693589379826718400853)
                  ·
                    refine ⟨803723711687636211089065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 274337693589379826718400853 803723711687636211089065)
                    ·
                      rfl

theorem cell23_4695739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_4695739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695739 prefixEnd_4695739 := by exact prefixLift 4695739
  have htrace : WordTrace (prefixWord ++ tailWord_4695739) baseStart_4695739 baseEnd_4695739 := by
    simpa [prefixWord, tailWord_4695739, baseEnd_4695739] using wordTrace_append hprefix tailTrace_4695739
  have hstable : (prefixWord ++ tailWord_4695739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695739).length < 2 ^ (prefixWord ++ tailWord_4695739).sum := by decide
  have hdescent : baseEnd_4695739 < baseStart_4695739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695786 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_4695786 : Nat := 118140960795 + 4695786 * 2 ^ 59
def prefixEnd_4695786 : Nat := 4983230072969 + 3 ^ 40 * 4695786 * 2
def baseEnd_4695786 : Nat := 267910585405963327708831

theorem tailTrace_4695786 : CollatzResearch.WordTrace tailWord_4695786 prefixEnd_4695786 267910585405963327708831 := by
  unfold tailWord_4695786
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817346441494193311326803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114179590510651182163538141 42817346441494193311326803)
  ·
    refine ⟨64226019662241289966990205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42817346441494193311326803 64226019662241289966990205)
    ·
      refine ⟨24084757373340483737621327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64226019662241289966990205 24084757373340483737621327)
      ·
        refine ⟨36127136060010725606431991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24084757373340483737621327 36127136060010725606431991)
        ·
          refine ⟨54190704090016088409647987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36127136060010725606431991 54190704090016088409647987)
          ·
            refine ⟨81286056135024132614471981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54190704090016088409647987 81286056135024132614471981)
            ·
              refine ⟨30482271050634049730426993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81286056135024132614471981 30482271050634049730426993)
              ·
                refine ⟨22861703287975537297820245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30482271050634049730426993 22861703287975537297820245)
                ·
                  refine ⟨267910585405963327708831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22861703287975537297820245 267910585405963327708831)
                  ·
                    rfl

theorem cell23_4695786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_4695786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695786 prefixEnd_4695786 := by exact prefixLift 4695786
  have htrace : WordTrace (prefixWord ++ tailWord_4695786) baseStart_4695786 baseEnd_4695786 := by
    simpa [prefixWord, tailWord_4695786, baseEnd_4695786] using wordTrace_append hprefix tailTrace_4695786
  have hstable : (prefixWord ++ tailWord_4695786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695786).length < 2 ^ (prefixWord ++ tailWord_4695786).sum := by decide
  have hdescent : baseEnd_4695786 < baseStart_4695786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695823 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 5, 2]
def baseStart_4695823 : Nat := 118140960795 + 4695823 * 2 ^ 59
def prefixEnd_4695823 : Nat := 4983230072969 + 3 ^ 40 * 4695823 * 2
def baseEnd_4695823 : Nat := 2411214267437886304616809

theorem tailTrace_4695823 : CollatzResearch.WordTrace tailWord_4695823 prefixEnd_4695823 2411214267437886304616809 := by
  unfold tailWord_4695823
  simp only [CollatzResearch.WordTrace]
  refine ⟨171270735266842728564404123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114180490177895152376269415 171270735266842728564404123)
  ·
    refine ⟨256906102900264092846606185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171270735266842728564404123 256906102900264092846606185)
    ·
      refine ⟨192679577175198069634954639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256906102900264092846606185 192679577175198069634954639)
      ·
        refine ⟨289019365762797104452431959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192679577175198069634954639 289019365762797104452431959)
        ·
          refine ⟨433529048644195656678647939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289019365762797104452431959 433529048644195656678647939)
          ·
            refine ⟨650293572966293485017971909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433529048644195656678647939 650293572966293485017971909)
            ·
              refine ⟨121930044931180028440869733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 650293572966293485017971909 121930044931180028440869733)
              ·
                refine ⟨22861883424596255332663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121930044931180028440869733 22861883424596255332663075)
                ·
                  refine ⟨34292825136894382998994613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22861883424596255332663075 34292825136894382998994613)
                  ·
                    refine ⟨3214952356583848406155745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34292825136894382998994613 3214952356583848406155745)
                    ·
                      refine ⟨2411214267437886304616809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3214952356583848406155745 2411214267437886304616809)
                      ·
                        rfl

theorem cell23_4695823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5, 2].length) (baseStart_4695823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695823 prefixEnd_4695823 := by exact prefixLift 4695823
  have htrace : WordTrace (prefixWord ++ tailWord_4695823) baseStart_4695823 baseEnd_4695823 := by
    simpa [prefixWord, tailWord_4695823, baseEnd_4695823] using wordTrace_append hprefix tailTrace_4695823
  have hstable : (prefixWord ++ tailWord_4695823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695823).length < 2 ^ (prefixWord ++ tailWord_4695823).sum := by decide
  have hdescent : baseEnd_4695823 < baseStart_4695823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4695864 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 1, 1, 3]
def baseStart_4695864 : Nat := 118140960795 + 4695864 * 2 ^ 59
def prefixEnd_4695864 : Nat := 4983230072969 + 3 ^ 40 * 4695864 * 2
def baseEnd_4695864 : Nat := 2411235320144720644204121

theorem tailTrace_4695864 : CollatzResearch.WordTrace tailWord_4695864 prefixEnd_4695864 2411235320144720644204121 := by
  unfold tailWord_4695864
  simp only [CollatzResearch.WordTrace]
  refine ⟨85636115329847096283323323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114181487106462795044431097 85636115329847096283323323)
  ·
    refine ⟨128454172994770644424984985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85636115329847096283323323 128454172994770644424984985)
    ·
      refine ⟨96340629746077983318738739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128454172994770644424984985 96340629746077983318738739)
      ·
        refine ⟨144510944619116974978108109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96340629746077983318738739 144510944619116974978108109)
        ·
          refine ⟨54191604232168865616790541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144510944619116974978108109 54191604232168865616790541)
          ·
            refine ⟨20321851587063324606296453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54191604232168865616790541 20321851587063324606296453)
            ·
              refine ⟨3810347172574373363680585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20321851587063324606296453 3810347172574373363680585)
              ·
                refine ⟨2857760379430780022760439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810347172574373363680585 2857760379430780022760439)
                ·
                  refine ⟨4286640569146170034140659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2857760379430780022760439 4286640569146170034140659)
                  ·
                    refine ⟨6429960853719255051210989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4286640569146170034140659 6429960853719255051210989)
                    ·
                      refine ⟨2411235320144720644204121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6429960853719255051210989 2411235320144720644204121)
                      ·
                        rfl

theorem cell23_4695864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_4695864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4695864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4695864 prefixEnd_4695864 := by exact prefixLift 4695864
  have htrace : WordTrace (prefixWord ++ tailWord_4695864) baseStart_4695864 baseEnd_4695864 := by
    simpa [prefixWord, tailWord_4695864, baseEnd_4695864] using wordTrace_append hprefix tailTrace_4695864
  have hstable : (prefixWord ++ tailWord_4695864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4695864).length < 2 ^ (prefixWord ++ tailWord_4695864).sum := by decide
  have hdescent : baseEnd_4695864 < baseStart_4695864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4695864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
