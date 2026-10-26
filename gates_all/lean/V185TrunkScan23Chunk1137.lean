import V185TrunkScan23Chunk1136

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6735040 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_6735040 : Nat := 118140960795 + 6735040 * 2 ^ 59
def prefixEnd_6735040 : Nat := 4983230072969 + 3 ^ 40 * 6735040 * 2
def baseEnd_6735040 : Nat := 3458312747257434358726121

theorem tailTrace_6735040 : CollatzResearch.WordTrace tailWord_6735040 prefixEnd_6735040 3458312747257434358726121 := by
  unfold tailWord_6735040
  simp only [CollatzResearch.WordTrace]
  refine ⟨122823544760053904050385287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163764726346738538733847049 122823544760053904050385287)
  ·
    refine ⟨184235317140080856075577931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122823544760053904050385287 184235317140080856075577931)
    ·
      refine ⟨276352975710121284113366897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184235317140080856075577931 276352975710121284113366897)
      ·
        refine ⟨207264731782590963085025173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276352975710121284113366897 207264731782590963085025173)
        ·
          refine ⟨9715534302308951394610555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207264731782590963085025173 9715534302308951394610555)
          ·
            refine ⟨14573301453463427091915833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715534302308951394610555 14573301453463427091915833)
            ·
              refine ⟨10929976090097570318936875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14573301453463427091915833 10929976090097570318936875)
              ·
                refine ⟨16394964135146355478405313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929976090097570318936875 16394964135146355478405313)
                ·
                  refine ⟨12296223101359766608803985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16394964135146355478405313 12296223101359766608803985)
                  ·
                    refine ⟨9222167326019824956602989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12296223101359766608803985 9222167326019824956602989)
                    ·
                      refine ⟨3458312747257434358726121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9222167326019824956602989 3458312747257434358726121)
                      ·
                        rfl

theorem cell23_6735040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_6735040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735040 prefixEnd_6735040 := by exact prefixLift 6735040
  have htrace : WordTrace (prefixWord ++ tailWord_6735040) baseStart_6735040 baseEnd_6735040 := by
    simpa [prefixWord, tailWord_6735040, baseEnd_6735040] using wordTrace_append hprefix tailTrace_6735040
  have hstable : (prefixWord ++ tailWord_6735040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735040).length < 2 ^ (prefixWord ++ tailWord_6735040).sum := by decide
  have hdescent : baseEnd_6735040 < baseStart_6735040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735064 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 1, 4]
def baseStart_6735064 : Nat := 118140960795 + 6735064 * 2 ^ 59
def prefixEnd_6735064 : Nat := 4983230072969 + 3 ^ 40 * 6735064 * 2
def baseEnd_6735064 : Nat := 1152775023597714088275337

theorem tailTrace_6735064 : CollatzResearch.WordTrace tailWord_6735064 prefixEnd_6735064 1152775023597714088275337 := by
  unfold tailWord_6735064
  simp only [CollatzResearch.WordTrace]
  refine ⟨122823982436010430099822123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163765309914680573466429497 122823982436010430099822123)
  ·
    refine ⟨184235973654015645149733185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122823982436010430099822123 184235973654015645149733185)
    ·
      refine ⟨138176980240511733862299889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184235973654015645149733185 138176980240511733862299889)
      ·
        refine ⟨103632735180383800396724917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138176980240511733862299889 103632735180383800396724917)
        ·
          refine ⟨9715568923160981287192961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103632735180383800396724917 9715568923160981287192961)
          ·
            refine ⟨7286676692370735965394721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9715568923160981287192961 7286676692370735965394721)
            ·
              refine ⟨5465007519278051974046041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286676692370735965394721 5465007519278051974046041)
              ·
                refine ⟨4098755639458538980534531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5465007519278051974046041 4098755639458538980534531)
                ·
                  refine ⟨6148133459187808470801797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098755639458538980534531 6148133459187808470801797)
                  ·
                    refine ⟨1152775023597714088275337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148133459187808470801797 1152775023597714088275337)
                    ·
                      rfl

theorem cell23_6735064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_6735064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735064 prefixEnd_6735064 := by exact prefixLift 6735064
  have htrace : WordTrace (prefixWord ++ tailWord_6735064) baseStart_6735064 baseEnd_6735064 := by
    simpa [prefixWord, tailWord_6735064, baseEnd_6735064] using wordTrace_append hprefix tailTrace_6735064
  have hstable : (prefixWord ++ tailWord_6735064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735064).length < 2 ^ (prefixWord ++ tailWord_6735064).sum := by decide
  have hdescent : baseEnd_6735064 < baseStart_6735064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735116 : List Nat := [2, 2, 1, 2, 2, 4, 10]
def baseStart_6735116 : Nat := 118140960795 + 6735116 * 2 ^ 59
def prefixEnd_6735116 : Nat := 4983230072969 + 3 ^ 40 * 6735116 * 2
def baseEnd_6735116 : Nat := 42695700886261432856491

theorem tailTrace_6735116 : CollatzResearch.WordTrace tailWord_6735116 prefixEnd_6735116 42695700886261432856491 := by
  unfold tailWord_6735116
  simp only [CollatzResearch.WordTrace]
  refine ⟨122824930733916236540268601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163766574311888315387024801 122824930733916236540268601)
  ·
    refine ⟨92118698050437177405201451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122824930733916236540268601 92118698050437177405201451)
    ·
      refine ⟨138178047075655766107802177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92118698050437177405201451 138178047075655766107802177)
      ·
        refine ⟨103633535306741824580851633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138178047075655766107802177 103633535306741824580851633)
        ·
          refine ⟨77725151480056368435638725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103633535306741824580851633 77725151480056368435638725)
          ·
            refine ⟨14573465902510569081682261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77725151480056368435638725 14573465902510569081682261)
            ·
              refine ⟨42695700886261432856491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14573465902510569081682261 42695700886261432856491)
              ·
                rfl

theorem cell23_6735116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 10].length) (baseStart_6735116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735116 prefixEnd_6735116 := by exact prefixLift 6735116
  have htrace : WordTrace (prefixWord ++ tailWord_6735116) baseStart_6735116 baseEnd_6735116 := by
    simpa [prefixWord, tailWord_6735116, baseEnd_6735116] using wordTrace_append hprefix tailTrace_6735116
  have hstable : (prefixWord ++ tailWord_6735116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735116).length < 2 ^ (prefixWord ++ tailWord_6735116).sum := by decide
  have hdescent : baseEnd_6735116 < baseStart_6735116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735127 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6735127 : Nat := 118140960795 + 6735127 * 2 ^ 59
def prefixEnd_6735127 : Nat := 4983230072969 + 3 ^ 40 * 6735127 * 2
def baseEnd_6735127 : Nat := 3458357420074375518338221

theorem tailTrace_6735127 : CollatzResearch.WordTrace tailWord_6735127 prefixEnd_6735127 3458357420074375518338221 := by
  unfold tailWord_6735127
  simp only [CollatzResearch.WordTrace]
  refine ⟨245650262670792621959187635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163766841780528414639458423 245650262670792621959187635)
  ·
    refine ⟨368475394006188932938781453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245650262670792621959187635 368475394006188932938781453)
    ·
      refine ⟨138178272752320849852043045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368475394006188932938781453 138178272752320849852043045)
      ·
        refine ⟨25908426141060159347258071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138178272752320849852043045 25908426141060159347258071)
        ·
          refine ⟨38862639211590239020887107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25908426141060159347258071 38862639211590239020887107)
          ·
            refine ⟨58293958817385358531330661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38862639211590239020887107 58293958817385358531330661)
            ·
              refine ⟨10930117278259754724624499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58293958817385358531330661 10930117278259754724624499)
              ·
                refine ⟨16395175917389632086936749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10930117278259754724624499 16395175917389632086936749)
                ·
                  refine ⟨6148190969021112032601281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16395175917389632086936749 6148190969021112032601281)
                  ·
                    refine ⟨4611143226765834024450961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148190969021112032601281 4611143226765834024450961)
                    ·
                      refine ⟨3458357420074375518338221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611143226765834024450961 3458357420074375518338221)
                      ·
                        rfl

theorem cell23_6735127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6735127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735127 prefixEnd_6735127 := by exact prefixLift 6735127
  have htrace : WordTrace (prefixWord ++ tailWord_6735127) baseStart_6735127 baseEnd_6735127 := by
    simpa [prefixWord, tailWord_6735127, baseEnd_6735127] using wordTrace_append hprefix tailTrace_6735127
  have hstable : (prefixWord ++ tailWord_6735127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735127).length < 2 ^ (prefixWord ++ tailWord_6735127).sum := by decide
  have hdescent : baseEnd_6735127 < baseStart_6735127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735203 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6735203 : Nat := 118140960795 + 6735203 * 2 ^ 59
def prefixEnd_6735203 : Nat := 4983230072969 + 3 ^ 40 * 6735203 * 2
def baseEnd_6735203 : Nat := 3458396444604117220987871

theorem tailTrace_6735203 : CollatzResearch.WordTrace tailWord_6735203 prefixEnd_6735203 3458396444604117220987871 := by
  unfold tailWord_6735203
  simp only [CollatzResearch.WordTrace]
  refine ⟨245653034618517286938954263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163768689745678191292636175 245653034618517286938954263)
  ·
    refine ⟨368479551927775930408431395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245653034618517286938954263 368479551927775930408431395)
    ·
      refine ⟨552719327891663895612647093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368479551927775930408431395 552719327891663895612647093)
      ·
        refine ⟨51817436989843490213685665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 552719327891663895612647093 51817436989843490213685665)
        ·
          refine ⟨38863077742382617660264249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51817436989843490213685665 38863077742382617660264249)
          ·
            refine ⟨29147308306786963245198187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38863077742382617660264249 29147308306786963245198187)
            ·
              refine ⟨43720962460180444867797281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29147308306786963245198187 43720962460180444867797281)
              ·
                refine ⟨32790721845135333650847961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43720962460180444867797281 32790721845135333650847961)
                ·
                  refine ⟨24593041383851500238135971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32790721845135333650847961 24593041383851500238135971)
                  ·
                    refine ⟨36889562075777250357203957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24593041383851500238135971 36889562075777250357203957)
                    ·
                      refine ⟨3458396444604117220987871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36889562075777250357203957 3458396444604117220987871)
                      ·
                        rfl

theorem cell23_6735203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6735203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735203 prefixEnd_6735203 := by exact prefixLift 6735203
  have htrace : WordTrace (prefixWord ++ tailWord_6735203) baseStart_6735203 baseEnd_6735203 := by
    simpa [prefixWord, tailWord_6735203, baseEnd_6735203] using wordTrace_append hprefix tailTrace_6735203
  have hstable : (prefixWord ++ tailWord_6735203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735203).length < 2 ^ (prefixWord ++ tailWord_6735203).sum := by decide
  have hdescent : baseEnd_6735203 < baseStart_6735203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735204 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_6735204 : Nat := 118140960795 + 6735204 * 2 ^ 59
def prefixEnd_6735204 : Nat := 4983230072969 + 3 ^ 40 * 6735204 * 2
def baseEnd_6735204 : Nat := 3458396958084771717075367

theorem tailTrace_6735204 : CollatzResearch.WordTrace tailWord_6735204 prefixEnd_6735204 3458396958084771717075367 := by
  unfold tailWord_6735204
  simp only [CollatzResearch.WordTrace]
  refine ⟨122826535545756832054870333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163768714061009109406493777 122826535545756832054870333)
  ·
    refine ⟨46059950829658812020576375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122826535545756832054870333 46059950829658812020576375)
    ·
      refine ⟨69089926244488218030864563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46059950829658812020576375 69089926244488218030864563)
      ·
        refine ⟨103634889366732327046296845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69089926244488218030864563 103634889366732327046296845)
        ·
          refine ⟨38863083512524622642361317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103634889366732327046296845 38863083512524622642361317)
          ·
            refine ⟨7286828158598366745442747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38863083512524622642361317 7286828158598366745442747)
            ·
              refine ⟨10930242237897550118164121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286828158598366745442747 10930242237897550118164121)
              ·
                refine ⟨8197681678423162588623091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10930242237897550118164121 8197681678423162588623091)
                ·
                  refine ⟨12296522517634743882934637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197681678423162588623091 12296522517634743882934637)
                  ·
                    refine ⟨4611195944113028956100489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12296522517634743882934637 4611195944113028956100489)
                    ·
                      refine ⟨3458396958084771717075367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611195944113028956100489 3458396958084771717075367)
                      ·
                        rfl

theorem cell23_6735204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_6735204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735204 prefixEnd_6735204 := by exact prefixLift 6735204
  have htrace : WordTrace (prefixWord ++ tailWord_6735204) baseStart_6735204 baseEnd_6735204 := by
    simpa [prefixWord, tailWord_6735204, baseEnd_6735204] using wordTrace_append hprefix tailTrace_6735204
  have hstable : (prefixWord ++ tailWord_6735204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735204).length < 2 ^ (prefixWord ++ tailWord_6735204).sum := by decide
  have hdescent : baseEnd_6735204 < baseStart_6735204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735221 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6735221 : Nat := 118140960795 + 6735221 * 2 ^ 59
def prefixEnd_6735221 : Nat := 4983230072969 + 3 ^ 40 * 6735221 * 2
def baseEnd_6735221 : Nat := 3458405687255898150562789

theorem tailTrace_6735221 : CollatzResearch.WordTrace tailWord_6735221 prefixEnd_6735221 3458405687255898150562789 := by
  unfold tailWord_6735221
  simp only [CollatzResearch.WordTrace]
  refine ⟨245653691132452076013109517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163769127421634717342073011 245653691132452076013109517)
  ·
    refine ⟨92120134174669528504916069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245653691132452076013109517 92120134174669528504916069)
    ·
      refine ⟨17272525157750536594671763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92120134174669528504916069 17272525157750536594671763)
      ·
        refine ⟨25908787736625804892007645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17272525157750536594671763 25908787736625804892007645)
        ·
          refine ⟨9715795401234676834502867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25908787736625804892007645 9715795401234676834502867)
          ·
            refine ⟨14573693101852015251754301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715795401234676834502867 14573693101852015251754301)
            ·
              refine ⟨5465134913194505719407863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14573693101852015251754301 5465134913194505719407863)
              ·
                refine ⟨8197702369791758579111795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465134913194505719407863 8197702369791758579111795)
                ·
                  refine ⟨12296553554687637868667693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197702369791758579111795 12296553554687637868667693)
                  ·
                    refine ⟨4611207583007864200750385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12296553554687637868667693 4611207583007864200750385)
                    ·
                      refine ⟨3458405687255898150562789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611207583007864200750385 3458405687255898150562789)
                      ·
                        rfl

theorem cell23_6735221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6735221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735221 prefixEnd_6735221 := by exact prefixLift 6735221
  have htrace : WordTrace (prefixWord ++ tailWord_6735221) baseStart_6735221 baseEnd_6735221 := by
    simpa [prefixWord, tailWord_6735221, baseEnd_6735221] using wordTrace_append hprefix tailTrace_6735221
  have hstable : (prefixWord ++ tailWord_6735221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735221).length < 2 ^ (prefixWord ++ tailWord_6735221).sum := by decide
  have hdescent : baseEnd_6735221 < baseStart_6735221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735253 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_6735253 : Nat := 118140960795 + 6735253 * 2 ^ 59
def prefixEnd_6735253 : Nat := 4983230072969 + 3 ^ 40 * 6735253 * 2
def baseEnd_6735253 : Nat := 1152807372878947341787547

theorem tailTrace_6735253 : CollatzResearch.WordTrace tailWord_6735253 prefixEnd_6735253 1152807372878947341787547 := by
  unfold tailWord_6735253
  simp only [CollatzResearch.WordTrace]
  refine ⟨245654858268336145478274413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163769905512224096985516275 245654858268336145478274413)
  ·
    refine ⟨92120571850626054554352905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245654858268336145478274413 92120571850626054554352905)
    ·
      refine ⟨69090428887969540915764679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92120571850626054554352905 69090428887969540915764679)
      ·
        refine ⟨103635643331954311373647019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69090428887969540915764679 103635643331954311373647019)
        ·
          refine ⟨155453464997931467060470529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103635643331954311373647019 155453464997931467060470529)
          ·
            refine ⟨116590098748448600295352897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155453464997931467060470529 116590098748448600295352897)
            ·
              refine ⟨87442574061336450221514673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116590098748448600295352897 87442574061336450221514673)
              ·
                refine ⟨65581930546002337666136005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87442574061336450221514673 65581930546002337666136005)
                ·
                  refine ⟨12296611977375438312400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65581930546002337666136005 12296611977375438312400501)
                  ·
                    refine ⟨1152807372878947341787547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12296611977375438312400501 1152807372878947341787547)
                    ·
                      rfl

theorem cell23_6735253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_6735253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735253 prefixEnd_6735253 := by exact prefixLift 6735253
  have htrace : WordTrace (prefixWord ++ tailWord_6735253) baseStart_6735253 baseEnd_6735253 := by
    simpa [prefixWord, tailWord_6735253, baseEnd_6735253] using wordTrace_append hprefix tailTrace_6735253
  have hstable : (prefixWord ++ tailWord_6735253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735253).length < 2 ^ (prefixWord ++ tailWord_6735253).sum := by decide
  have hdescent : baseEnd_6735253 < baseStart_6735253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735303 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_6735303 : Nat := 118140960795 + 6735303 * 2 ^ 59
def prefixEnd_6735303 : Nat := 4983230072969 + 3 ^ 40 * 6735303 * 2
def baseEnd_6735303 : Nat := 3458447792669566829737411

theorem tailTrace_6735303 : CollatzResearch.WordTrace tailWord_6735303 prefixEnd_6735303 3458447792669566829737411 := by
  unfold tailWord_6735303
  simp only [CollatzResearch.WordTrace]
  refine ⟨245656681918155004017594563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163771121278770002678396375 245656681918155004017594563)
  ·
    refine ⟨368485022877232506026391845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245656681918155004017594563 368485022877232506026391845)
    ·
      refine ⟨69090941789481094879948471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368485022877232506026391845 69090941789481094879948471)
      ·
        refine ⟨103636412684221642319922707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69090941789481094879948471 103636412684221642319922707)
        ·
          refine ⟨155454619026332463479884061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103636412684221642319922707 155454619026332463479884061)
          ·
            refine ⟨58295482134874673804956523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155454619026332463479884061 58295482134874673804956523)
            ·
              refine ⟨87443223202312010707434785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58295482134874673804956523 87443223202312010707434785)
              ·
                refine ⟨65582417401734008030576089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87443223202312010707434785 65582417401734008030576089)
                ·
                  refine ⟨49186813051300506022932067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65582417401734008030576089 49186813051300506022932067)
                  ·
                    refine ⟨73780219576950759034398101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49186813051300506022932067 73780219576950759034398101)
                    ·
                      refine ⟨3458447792669566829737411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73780219576950759034398101 3458447792669566829737411)
                      ·
                        rfl

theorem cell23_6735303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_6735303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735303 prefixEnd_6735303 := by exact prefixLift 6735303
  have htrace : WordTrace (prefixWord ++ tailWord_6735303) baseStart_6735303 baseEnd_6735303 := by
    simpa [prefixWord, tailWord_6735303, baseEnd_6735303] using wordTrace_append hprefix tailTrace_6735303
  have hstable : (prefixWord ++ tailWord_6735303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735303).length < 2 ^ (prefixWord ++ tailWord_6735303).sum := by decide
  have hdescent : baseEnd_6735303 < baseStart_6735303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735310 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_6735310 : Nat := 118140960795 + 6735310 * 2 ^ 59
def prefixEnd_6735310 : Nat := 4983230072969 + 3 ^ 40 * 6735310 * 2
def baseEnd_6735310 : Nat := 3458451387034148302349879

theorem tailTrace_6735310 : CollatzResearch.WordTrace tailWord_6735310 prefixEnd_6735310 3458451387034148302349879 := by
  unfold tailWord_6735310
  simp only [CollatzResearch.WordTrace]
  refine ⟨30707117153641205526637423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163771291486086429475399589 30707117153641205526637423)
  ·
    refine ⟨46060675730461808289956135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30707117153641205526637423 46060675730461808289956135)
    ·
      refine ⟨69091013595692712434934203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46060675730461808289956135 69091013595692712434934203)
      ·
        refine ⟨103636520393539068652401305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69091013595692712434934203 103636520393539068652401305)
        ·
          refine ⟨77727390295154301489300979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103636520393539068652401305 77727390295154301489300979)
          ·
            refine ⟨116591085442731452233951469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77727390295154301489300979 116591085442731452233951469)
            ·
              refine ⟨43721657041024294587731801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116591085442731452233951469 43721657041024294587731801)
              ·
                refine ⟨32791242780768220940798851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43721657041024294587731801 32791242780768220940798851)
                ·
                  refine ⟨49186864171152331411198277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32791242780768220940798851 49186864171152331411198277)
                  ·
                    refine ⟨9222537032091062139599677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49186864171152331411198277 9222537032091062139599677)
                    ·
                      refine ⟨3458451387034148302349879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9222537032091062139599677 3458451387034148302349879)
                      ·
                        rfl

theorem cell23_6735310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_6735310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735310 prefixEnd_6735310 := by exact prefixLift 6735310
  have htrace : WordTrace (prefixWord ++ tailWord_6735310) baseStart_6735310 baseEnd_6735310 := by
    simpa [prefixWord, tailWord_6735310, baseEnd_6735310] using wordTrace_append hprefix tailTrace_6735310
  have hstable : (prefixWord ++ tailWord_6735310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735310).length < 2 ^ (prefixWord ++ tailWord_6735310).sum := by decide
  have hdescent : baseEnd_6735310 < baseStart_6735310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735353 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6735353 : Nat := 118140960795 + 6735353 * 2 ^ 59
def prefixEnd_6735353 : Nat := 4983230072969 + 3 ^ 40 * 6735353 * 2
def baseEnd_6735353 : Nat := 3458473466702291634112181

theorem tailTrace_6735353 : CollatzResearch.WordTrace tailWord_6735353 prefixEnd_6735353 3458473466702291634112181 := by
  unfold tailWord_6735353
  simp only [CollatzResearch.WordTrace]
  refine ⟨245658505567973862556914713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163772337045315908371276475 245658505567973862556914713)
  ·
    refine ⟨184243879175980396917686035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245658505567973862556914713 184243879175980396917686035)
    ·
      refine ⟨276365818763970595376529053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184243879175980396917686035 276365818763970595376529053)
      ·
        refine ⟨103637182036488973266198395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276365818763970595376529053 103637182036488973266198395)
        ·
          refine ⟨155455773054733459899297593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103637182036488973266198395 155455773054733459899297593)
          ·
            refine ⟨116591829791050094924473195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155455773054733459899297593 116591829791050094924473195)
            ·
              refine ⟨174887744686575142386709793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116591829791050094924473195 174887744686575142386709793)
              ·
                refine ⟨131165808514931356790032345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174887744686575142386709793 131165808514931356790032345)
                ·
                  refine ⟨98374356386198517592524259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131165808514931356790032345 98374356386198517592524259)
                  ·
                    refine ⟨147561534579297776388786389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98374356386198517592524259 147561534579297776388786389)
                    ·
                      refine ⟨3458473466702291634112181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147561534579297776388786389 3458473466702291634112181)
                      ·
                        rfl

theorem cell23_6735353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6735353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735353 prefixEnd_6735353 := by exact prefixLift 6735353
  have htrace : WordTrace (prefixWord ++ tailWord_6735353) baseStart_6735353 baseEnd_6735353 := by
    simpa [prefixWord, tailWord_6735353, baseEnd_6735353] using wordTrace_append hprefix tailTrace_6735353
  have hstable : (prefixWord ++ tailWord_6735353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735353).length < 2 ^ (prefixWord ++ tailWord_6735353).sum := by decide
  have hdescent : baseEnd_6735353 < baseStart_6735353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735410 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_6735410 : Nat := 118140960795 + 6735410 * 2 ^ 59
def prefixEnd_6735410 : Nat := 4983230072969 + 3 ^ 40 * 6735410 * 2
def baseEnd_6735410 : Nat := 3458502735099597911099419

theorem tailTrace_6735410 : CollatzResearch.WordTrace tailWord_6735410 prefixEnd_6735410 3458502735099597911099419 := by
  unfold tailWord_6735410
  simp only [CollatzResearch.WordTrace]
  refine ⟨61415146132191840322934921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163773723019178240861159789 61415146132191840322934921)
  ·
    refine ⟨46061359599143880242201191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61415146132191840322934921 46061359599143880242201191)
    ·
      refine ⟨69092039398715820363301787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46061359599143880242201191 69092039398715820363301787)
      ·
        refine ⟨103638059098073730544952681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69092039398715820363301787 103638059098073730544952681)
        ·
          refine ⟨77728544323555297908714511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103638059098073730544952681 77728544323555297908714511)
          ·
            refine ⟨116592816485332946863071767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77728544323555297908714511 116592816485332946863071767)
            ·
              refine ⟨174889224727999420294607651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116592816485332946863071767 174889224727999420294607651)
              ·
                refine ⟨262333837091999130441911477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174889224727999420294607651 262333837091999130441911477)
                ·
                  refine ⟨24593797227374918478929201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262333837091999130441911477 24593797227374918478929201)
                  ·
                    refine ⟨18445347920531188859196901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24593797227374918478929201 18445347920531188859196901)
                    ·
                      refine ⟨3458502735099597911099419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18445347920531188859196901 3458502735099597911099419)
                      ·
                        rfl

theorem cell23_6735410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_6735410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735410 prefixEnd_6735410 := by exact prefixLift 6735410
  have htrace : WordTrace (prefixWord ++ tailWord_6735410) baseStart_6735410 baseEnd_6735410 := by
    simpa [prefixWord, tailWord_6735410, baseEnd_6735410] using wordTrace_append hprefix tailTrace_6735410
  have hstable : (prefixWord ++ tailWord_6735410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735410).length < 2 ^ (prefixWord ++ tailWord_6735410).sum := by decide
  have hdescent : baseEnd_6735410 < baseStart_6735410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735417 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6735417 : Nat := 118140960795 + 6735417 * 2 ^ 59
def prefixEnd_6735417 : Nat := 4983230072969 + 3 ^ 40 * 6735417 * 2
def baseEnd_6735417 : Nat := 3458506329464179383711887

theorem tailTrace_6735417 : CollatzResearch.WordTrace tailWord_6735417 prefixEnd_6735417 3458506329464179383711887 := by
  unfold tailWord_6735417
  simp only [CollatzResearch.WordTrace]
  refine ⟨245660839839742001487244505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163773893226494667658163003 245660839839742001487244505)
  ·
    refine ⟨184245629879806501115433379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245660839839742001487244505 184245629879806501115433379)
    ·
      refine ⟨276368444819709751673150069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184245629879806501115433379 276368444819709751673150069)
      ·
        refine ⟨25909541701847789219357819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276368444819709751673150069 25909541701847789219357819)
        ·
          refine ⟨38864312552771683829036729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25909541701847789219357819 38864312552771683829036729)
          ·
            refine ⟨29148234414578762871777547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38864312552771683829036729 29148234414578762871777547)
            ·
              refine ⟨43722351621868144307666321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29148234414578762871777547 43722351621868144307666321)
              ·
                refine ⟨32791763716401108230749741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43722351621868144307666321 32791763716401108230749741)
                ·
                  refine ⟨12296911393650415586531153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32791763716401108230749741 12296911393650415586531153)
                  ·
                    refine ⟨9222683545237811689898365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12296911393650415586531153 9222683545237811689898365)
                    ·
                      refine ⟨3458506329464179383711887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9222683545237811689898365 3458506329464179383711887)
                      ·
                        rfl

theorem cell23_6735417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6735417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735417 prefixEnd_6735417 := by exact prefixLift 6735417
  have htrace : WordTrace (prefixWord ++ tailWord_6735417) baseStart_6735417 baseEnd_6735417 := by
    simpa [prefixWord, tailWord_6735417, baseEnd_6735417] using wordTrace_append hprefix tailTrace_6735417
  have hstable : (prefixWord ++ tailWord_6735417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735417).length < 2 ^ (prefixWord ++ tailWord_6735417).sum := by decide
  have hdescent : baseEnd_6735417 < baseStart_6735417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735431 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_6735431 : Nat := 118140960795 + 6735431 * 2 ^ 59
def prefixEnd_6735431 : Nat := 4983230072969 + 3 ^ 40 * 6735431 * 2
def baseEnd_6735431 : Nat := 3458513518193342328936823

theorem tailTrace_6735431 : CollatzResearch.WordTrace tailWord_6735431 prefixEnd_6735431 3458513518193342328936823 := by
  unfold tailWord_6735431
  simp only [CollatzResearch.WordTrace]
  refine ⟨245661350461691281878254147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163774233641127521252169431 245661350461691281878254147)
  ·
    refine ⟨368492025692536922817381221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245661350461691281878254147 368492025692536922817381221)
    ·
      refine ⟨69092254817350673028258979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368492025692536922817381221 69092254817350673028258979)
      ·
        refine ⟨103638382226026009542388469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69092254817350673028258979 103638382226026009542388469)
        ·
          refine ⟨9716098333689938394598919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103638382226026009542388469 9716098333689938394598919)
          ·
            refine ⟨14574147500534907591898379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716098333689938394598919 14574147500534907591898379)
            ·
              refine ⟨21861221250802361387847569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14574147500534907591898379 21861221250802361387847569)
              ·
                refine ⟨16395915938101771040885677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21861221250802361387847569 16395915938101771040885677)
                ·
                  refine ⟨6148468476788164140332129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16395915938101771040885677 6148468476788164140332129)
                  ·
                    refine ⟨4611351357591123105249097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148468476788164140332129 4611351357591123105249097)
                    ·
                      refine ⟨3458513518193342328936823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611351357591123105249097 3458513518193342328936823)
                      ·
                        rfl

theorem cell23_6735431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_6735431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735431 prefixEnd_6735431 := by exact prefixLift 6735431
  have htrace : WordTrace (prefixWord ++ tailWord_6735431) baseStart_6735431 baseEnd_6735431 := by
    simpa [prefixWord, tailWord_6735431, baseEnd_6735431] using wordTrace_append hprefix tailTrace_6735431
  have hstable : (prefixWord ++ tailWord_6735431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735431).length < 2 ^ (prefixWord ++ tailWord_6735431).sum := by decide
  have hdescent : baseEnd_6735431 < baseStart_6735431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735447 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_6735447 : Nat := 118140960795 + 6735447 * 2 ^ 59
def prefixEnd_6735447 : Nat := 4983230072969 + 3 ^ 40 * 6735447 * 2
def baseEnd_6735447 : Nat := 3458521733883814266336749

theorem tailTrace_6735447 : CollatzResearch.WordTrace tailWord_6735447 prefixEnd_6735447 3458521733883814266336749 := by
  unfold tailWord_6735447
  simp only [CollatzResearch.WordTrace]
  refine ⟨245661934029633316610836595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163774622686422211073891063 245661934029633316610836595)
  ·
    refine ⟨368492901044449974916254893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245661934029633316610836595 368492901044449974916254893)
    ·
      refine ⟨138184837891668740593595585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368492901044449974916254893 138184837891668740593595585)
      ·
        refine ⟨103638628418751555445196689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138184837891668740593595585 103638628418751555445196689)
        ·
          refine ⟨77728971314063666583897517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103638628418751555445196689 77728971314063666583897517)
          ·
            refine ⟨29148364242773874968961569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77728971314063666583897517 29148364242773874968961569)
            ·
              refine ⟨21861273182080406226721177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29148364242773874968961569 21861273182080406226721177)
              ·
                refine ⟨16395954886560304670040883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21861273182080406226721177 16395954886560304670040883)
                ·
                  refine ⟨24593932329840457005061325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16395954886560304670040883 24593932329840457005061325)
                  ·
                    refine ⟨9222724623690171376897997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24593932329840457005061325 9222724623690171376897997)
                    ·
                      refine ⟨3458521733883814266336749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9222724623690171376897997 3458521733883814266336749)
                      ·
                        rfl

theorem cell23_6735447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_6735447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735447 prefixEnd_6735447 := by exact prefixLift 6735447
  have htrace : WordTrace (prefixWord ++ tailWord_6735447) baseStart_6735447 baseEnd_6735447 := by
    simpa [prefixWord, tailWord_6735447, baseEnd_6735447] using wordTrace_append hprefix tailTrace_6735447
  have hstable : (prefixWord ++ tailWord_6735447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735447).length < 2 ^ (prefixWord ++ tailWord_6735447).sum := by decide
  have hdescent : baseEnd_6735447 < baseStart_6735447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735481 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 2, 1, 3]
def baseStart_6735481 : Nat := 118140960795 + 6735481 * 2 ^ 59
def prefixEnd_6735481 : Nat := 4983230072969 + 3 ^ 40 * 6735481 * 2
def baseEnd_6735481 : Nat := 3458539192226067133311593

theorem tailTrace_6735481 : CollatzResearch.WordTrace tailWord_6735481 prefixEnd_6735481 3458539192226067133311593 := by
  unfold tailWord_6735481
  simp only [CollatzResearch.WordTrace]
  refine ⟨245663174111510140417574297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163775449407673426945049531 245663174111510140417574297)
  ·
    refine ⟨184247380583632605313180723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245663174111510140417574297 184247380583632605313180723)
    ·
      refine ⟨276371070875448907969771085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184247380583632605313180723 276371070875448907969771085)
      ·
        refine ⟨103639151578293340488664157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276371070875448907969771085 103639151578293340488664157)
        ·
          refine ⟨38864681841860002683249059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103639151578293340488664157 38864681841860002683249059)
          ·
            refine ⟨58297022762790004024873589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38864681841860002683249059 58297022762790004024873589)
            ·
              refine ⟨5465345884011562877331899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58297022762790004024873589 5465345884011562877331899)
              ·
                refine ⟨8198018826017344315997849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465345884011562877331899 8198018826017344315997849)
                ·
                  refine ⟨6148514119513008236998387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198018826017344315997849 6148514119513008236998387)
                  ·
                    refine ⟨9222771179269512355497581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6148514119513008236998387 9222771179269512355497581)
                    ·
                      refine ⟨3458539192226067133311593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9222771179269512355497581 3458539192226067133311593)
                      ·
                        rfl

theorem cell23_6735481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_6735481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735481 prefixEnd_6735481 := by exact prefixLift 6735481
  have htrace : WordTrace (prefixWord ++ tailWord_6735481) baseStart_6735481 baseEnd_6735481 := by
    simpa [prefixWord, tailWord_6735481, baseEnd_6735481] using wordTrace_append hprefix tailTrace_6735481
  have hstable : (prefixWord ++ tailWord_6735481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735481).length < 2 ^ (prefixWord ++ tailWord_6735481).sum := by decide
  have hdescent : baseEnd_6735481 < baseStart_6735481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735521 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6735521 : Nat := 118140960795 + 6735521 * 2 ^ 59
def prefixEnd_6735521 : Nat := 4983230072969 + 3 ^ 40 * 6735521 * 2
def baseEnd_6735521 : Nat := 3458559731452246976811409

theorem tailTrace_6735521 : CollatzResearch.WordTrace tailWord_6735521 prefixEnd_6735521 3458559731452246976811409 := by
  unfold tailWord_6735521
  simp only [CollatzResearch.WordTrace]
  refine ⟨245664633031365227249030417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163776422020910151499353611 245664633031365227249030417)
  ·
    refine ⟨184248474773523920436772813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245664633031365227249030417 184248474773523920436772813)
    ·
      refine ⟨69093178040071470163789805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184248474773523920436772813 69093178040071470163789805)
      ·
        refine ⟨25909941765026801311421177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69093178040071470163789805 25909941765026801311421177)
        ·
          refine ⟨19432456323770100983565883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25909941765026801311421177 19432456323770100983565883)
          ·
            refine ⟨29148684485655151475348825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19432456323770100983565883 29148684485655151475348825)
            ·
              refine ⟨21861513364241363606511619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29148684485655151475348825 21861513364241363606511619)
              ·
                refine ⟨32792270046362045409767429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21861513364241363606511619 32792270046362045409767429)
                ·
                  refine ⟨6148550633692883514331393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32792270046362045409767429 6148550633692883514331393)
                  ·
                    refine ⟨4611412975269662635748545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148550633692883514331393 4611412975269662635748545)
                    ·
                      refine ⟨3458559731452246976811409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611412975269662635748545 3458559731452246976811409)
                      ·
                        rfl

theorem cell23_6735521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6735521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735521 prefixEnd_6735521 := by exact prefixLift 6735521
  have htrace : WordTrace (prefixWord ++ tailWord_6735521) baseStart_6735521 baseEnd_6735521 := by
    simpa [prefixWord, tailWord_6735521, baseEnd_6735521] using wordTrace_append hprefix tailTrace_6735521
  have hstable : (prefixWord ++ tailWord_6735521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735521).length < 2 ^ (prefixWord ++ tailWord_6735521).sum := by decide
  have hdescent : baseEnd_6735521 < baseStart_6735521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735538 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_6735538 : Nat := 118140960795 + 6735538 * 2 ^ 59
def prefixEnd_6735538 : Nat := 4983230072969 + 3 ^ 40 * 6735538 * 2
def baseEnd_6735538 : Nat := 3458568460623373410298831

theorem tailTrace_6735538 : CollatzResearch.WordTrace tailWord_6735538 prefixEnd_6735538 3458568460623373410298831 := by
  unfold tailWord_6735538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61416313268075909788099817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163776835381535759434932845 61416313268075909788099817)
  ·
    refine ⟨46062234951056932341074863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61416313268075909788099817 46062234951056932341074863)
    ·
      refine ⟨69093352426585398511612295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46062234951056932341074863 69093352426585398511612295)
      ·
        refine ⟨103640028639878097767418443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69093352426585398511612295 103640028639878097767418443)
        ·
          refine ⟨155460042959817146651127665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103640028639878097767418443 155460042959817146651127665)
          ·
            refine ⟨116595032219862859988345749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155460042959817146651127665 116595032219862859988345749)
            ·
              refine ⟨5465392135306071561953707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116595032219862859988345749 5465392135306071561953707)
              ·
                refine ⟨8198088202959107342930561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465392135306071561953707 8198088202959107342930561)
                ·
                  refine ⟨6148566152219330507197921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198088202959107342930561 6148566152219330507197921)
                  ·
                    refine ⟨4611424614164497880398441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148566152219330507197921 4611424614164497880398441)
                    ·
                      refine ⟨3458568460623373410298831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611424614164497880398441 3458568460623373410298831)
                      ·
                        rfl

theorem cell23_6735538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_6735538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735538 prefixEnd_6735538 := by exact prefixLift 6735538
  have htrace : WordTrace (prefixWord ++ tailWord_6735538) baseStart_6735538 baseEnd_6735538 := by
    simpa [prefixWord, tailWord_6735538, baseEnd_6735538] using wordTrace_append hprefix tailTrace_6735538
  have hstable : (prefixWord ++ tailWord_6735538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735538).length < 2 ^ (prefixWord ++ tailWord_6735538).sum := by decide
  have hdescent : baseEnd_6735538 < baseStart_6735538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735594 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_6735594 : Nat := 118140960795 + 6735594 * 2 ^ 59
def prefixEnd_6735594 : Nat := 4983230072969 + 3 ^ 40 * 6735594 * 2
def baseEnd_6735594 : Nat := 3458597215540025191198573

theorem tailTrace_6735594 : CollatzResearch.WordTrace tailWord_6735594 prefixEnd_6735594 3458597215540025191198573 := by
  unfold tailWord_6735594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61416823890025190179109459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163778197040067173810958557 61416823890025190179109459)
  ·
    refine ⟨92125235835037785268664189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61416823890025190179109459 92125235835037785268664189)
    ·
      refine ⟨34546963438139169475749071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92125235835037785268664189 34546963438139169475749071)
      ·
        refine ⟨51820445157208754213623607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34546963438139169475749071 51820445157208754213623607)
        ·
          refine ⟨77730667735813131320435411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51820445157208754213623607 77730667735813131320435411)
          ·
            refine ⟨116596001603719696980653117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77730667735813131320435411 116596001603719696980653117)
            ·
              refine ⟨43723500601394886367744919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116596001603719696980653117 43723500601394886367744919)
              ·
                refine ⟨65585250902092329551617379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43723500601394886367744919 65585250902092329551617379)
                ·
                  refine ⟨98377876353138494327426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65585250902092329551617379 98377876353138494327426069)
                  ·
                    refine ⟨4611462954053366921598097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98377876353138494327426069 4611462954053366921598097)
                    ·
                      refine ⟨3458597215540025191198573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611462954053366921598097 3458597215540025191198573)
                      ·
                        rfl

theorem cell23_6735594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_6735594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735594 prefixEnd_6735594 := by exact prefixLift 6735594
  have htrace : WordTrace (prefixWord ++ tailWord_6735594) baseStart_6735594 baseEnd_6735594 := by
    simpa [prefixWord, tailWord_6735594, baseEnd_6735594] using wordTrace_append hprefix tailTrace_6735594
  have hstable : (prefixWord ++ tailWord_6735594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735594).length < 2 ^ (prefixWord ++ tailWord_6735594).sum := by decide
  have hdescent : baseEnd_6735594 < baseStart_6735594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735637 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6735637 : Nat := 118140960795 + 6735637 * 2 ^ 59
def prefixEnd_6735637 : Nat := 4983230072969 + 3 ^ 40 * 6735637 * 2
def baseEnd_6735637 : Nat := 3458619295208168522960875

theorem tailTrace_6735637 : CollatzResearch.WordTrace tailWord_6735637 prefixEnd_6735637 3458619295208168522960875 := by
  unfold tailWord_6735637
  simp only [CollatzResearch.WordTrace]
  refine ⟨245668863898944979060253165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163779242599296652706835443 245668863898944979060253165)
  ·
    refine ⟨92125823962104367147594937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245668863898944979060253165 92125823962104367147594937)
    ·
      refine ⟨69094367971578275360696203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92125823962104367147594937 69094367971578275360696203)
      ·
        refine ⟨103641551957367413041044305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69094367971578275360696203 103641551957367413041044305)
        ·
          refine ⟨77731163968025559780783229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103641551957367413041044305 77731163968025559780783229)
          ·
            refine ⟨29149186488009584917793711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77731163968025559780783229 29149186488009584917793711)
            ·
              refine ⟨43723779732014377376690567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29149186488009584917793711 43723779732014377376690567)
              ·
                refine ⟨65585669598021566065035851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43723779732014377376690567 65585669598021566065035851)
                ·
                  refine ⟨98378504397032349097553777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65585669598021566065035851 98378504397032349097553777)
                  ·
                    refine ⟨73783878297774261823165333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98378504397032349097553777 73783878297774261823165333)
                    ·
                      refine ⟨3458619295208168522960875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73783878297774261823165333 3458619295208168522960875)
                      ·
                        rfl

theorem cell23_6735637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6735637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735637 prefixEnd_6735637 := by exact prefixLift 6735637
  have htrace : WordTrace (prefixWord ++ tailWord_6735637) baseStart_6735637 baseEnd_6735637 := by
    simpa [prefixWord, tailWord_6735637, baseEnd_6735637] using wordTrace_append hprefix tailTrace_6735637
  have hstable : (prefixWord ++ tailWord_6735637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735637).length < 2 ^ (prefixWord ++ tailWord_6735637).sum := by decide
  have hdescent : baseEnd_6735637 < baseStart_6735637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735711 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 2, 4]
def baseStart_6735711 : Nat := 118140960795 + 6735711 * 2 ^ 59
def prefixEnd_6735711 : Nat := 4983230072969 + 3 ^ 40 * 6735711 * 2
def baseEnd_6735711 : Nat := 1152885764258867077811845

theorem tailTrace_6735711 : CollatzResearch.WordTrace tailWord_6735711 prefixEnd_6735711 1152885764258867077811845 := by
  unfold tailWord_6735711
  simp only [CollatzResearch.WordTrace]
  refine ⟨245671562900676889698446987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163781041933784593132297991 245671562900676889698446987)
  ·
    refine ⟨368507344351015334547670481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245671562900676889698446987 368507344351015334547670481)
    ·
      refine ⟨276380508263261500910752861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368507344351015334547670481 276380508263261500910752861)
      ·
        refine ⟨103642690598723062841532323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276380508263261500910752861 103642690598723062841532323)
        ·
          refine ⟨155464035898084594262298485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103642690598723062841532323 155464035898084594262298485)
          ·
            refine ⟨14574753365445430712090483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155464035898084594262298485 14574753365445430712090483)
            ·
              refine ⟨21862130048168146068135725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14574753365445430712090483 21862130048168146068135725)
              ·
                refine ⟨8198298768063054775550897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21862130048168146068135725 8198298768063054775550897)
                ·
                  refine ⟨6148724076047291081663173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198298768063054775550897 6148724076047291081663173)
                  ·
                    refine ⟨1152885764258867077811845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148724076047291081663173 1152885764258867077811845)
                    ·
                      rfl

theorem cell23_6735711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_6735711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735711 prefixEnd_6735711 := by exact prefixLift 6735711
  have htrace : WordTrace (prefixWord ++ tailWord_6735711) baseStart_6735711 baseEnd_6735711 := by
    simpa [prefixWord, tailWord_6735711, baseEnd_6735711] using wordTrace_append hprefix tailTrace_6735711
  have hstable : (prefixWord ++ tailWord_6735711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735711).length < 2 ^ (prefixWord ++ tailWord_6735711).sum := by decide
  have hdescent : baseEnd_6735711 < baseStart_6735711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735745 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_6735745 : Nat := 118140960795 + 6735745 * 2 ^ 59
def prefixEnd_6735745 : Nat := 4983230072969 + 3 ^ 40 * 6735745 * 2
def baseEnd_6735745 : Nat := 1152891583706284700136793

theorem tailTrace_6735745 : CollatzResearch.WordTrace tailWord_6735745 prefixEnd_6735745 1152891583706284700136793 := by
  unfold tailWord_6735745
  simp only [CollatzResearch.WordTrace]
  refine ⟨245672802982553713505184689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163781868655035809003456459 245672802982553713505184689)
  ·
    refine ⟨184254602236915285128888517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245672802982553713505184689 184254602236915285128888517)
    ·
      refine ⟨34547737919421615961666597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184254602236915285128888517 34547737919421615961666597)
      ·
        refine ⟨6477700859891552992812487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34547737919421615961666597 6477700859891552992812487)
        ·
          refine ⟨9716551289837329489218731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477700859891552992812487 9716551289837329489218731)
          ·
            refine ⟨14574826934755994233828097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716551289837329489218731 14574826934755994233828097)
            ·
              refine ⟨10931120201066995675371073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14574826934755994233828097 10931120201066995675371073)
              ·
                refine ⟨8198340150800246756528305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10931120201066995675371073 8198340150800246756528305)
                ·
                  refine ⟨6148755113100185067396229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198340150800246756528305 6148755113100185067396229)
                  ·
                    refine ⟨1152891583706284700136793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148755113100185067396229 1152891583706284700136793)
                    ·
                      rfl

theorem cell23_6735745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_6735745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735745 prefixEnd_6735745 := by exact prefixLift 6735745
  have htrace : WordTrace (prefixWord ++ tailWord_6735745) baseStart_6735745 baseEnd_6735745 := by
    simpa [prefixWord, tailWord_6735745, baseEnd_6735745] using wordTrace_append hprefix tailTrace_6735745
  have hstable : (prefixWord ++ tailWord_6735745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735745).length < 2 ^ (prefixWord ++ tailWord_6735745).sum := by decide
  have hdescent : baseEnd_6735745 < baseStart_6735745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735752 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6735752 : Nat := 118140960795 + 6735752 * 2 ^ 59
def prefixEnd_6735752 : Nat := 4983230072969 + 3 ^ 40 * 6735752 * 2
def baseEnd_6735752 : Nat := 3458678345483435573022847

theorem tailTrace_6735752 : CollatzResearch.WordTrace tailWord_6735752 prefixEnd_6735752 3458678345483435573022847 := by
  unfold tailWord_6735752
  simp only [CollatzResearch.WordTrace]
  refine ⟨122836529146764176850344755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163782038862352235800459673 122836529146764176850344755)
  ·
    refine ⟨184254793720146265275517133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122836529146764176850344755 184254793720146265275517133)
    ·
      refine ⟨69095547645054849478318925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184254793720146265275517133 69095547645054849478318925)
      ·
        refine ⟨25910830366895568554369597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69095547645054849478318925 25910830366895568554369597)
        ·
          refine ⟨9716561387585838207888599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25910830366895568554369597 9716561387585838207888599)
          ·
            refine ⟨14574842081378757311832899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716561387585838207888599 14574842081378757311832899)
            ·
              refine ⟨21862263122068135967749349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14574842081378757311832899 21862263122068135967749349)
              ·
                refine ⟨4099174335387775493953003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21862263122068135967749349 4099174335387775493953003)
                ·
                  refine ⟨6148761503081663240929505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099174335387775493953003 6148761503081663240929505)
                  ·
                    refine ⟨4611571127311247430697129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148761503081663240929505 4611571127311247430697129)
                    ·
                      refine ⟨3458678345483435573022847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611571127311247430697129 3458678345483435573022847)
                      ·
                        rfl

theorem cell23_6735752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6735752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735752 prefixEnd_6735752 := by exact prefixLift 6735752
  have htrace : WordTrace (prefixWord ++ tailWord_6735752) baseStart_6735752 baseEnd_6735752 := by
    simpa [prefixWord, tailWord_6735752, baseEnd_6735752] using wordTrace_append hprefix tailTrace_6735752
  have hstable : (prefixWord ++ tailWord_6735752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735752).length < 2 ^ (prefixWord ++ tailWord_6735752).sum := by decide
  have hdescent : baseEnd_6735752 < baseStart_6735752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735758 : List Nat := [4, 1, 1, 5, 1, 2, 1, 8]
def baseStart_6735758 : Nat := 118140960795 + 6735758 * 2 ^ 59
def prefixEnd_6735758 : Nat := 4983230072969 + 3 ^ 40 * 6735758 * 2
def baseEnd_6735758 : Nat := 128099312087680094427697

theorem tailTrace_6735758 : CollatzResearch.WordTrace tailWord_6735758 prefixEnd_6735758 128099312087680094427697 := by
  unfold tailWord_6735758
  simp only [CollatzResearch.WordTrace]
  refine ⟨30709159641438327090675991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163782184754337744483605285 30709159641438327090675991)
  ·
    refine ⟨46063739462157490636013987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30709159641438327090675991 46063739462157490636013987)
    ·
      refine ⟨69095609193236235954020981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46063739462157490636013987 69095609193236235954020981)
      ·
        refine ⟨6477713361865897120689467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69095609193236235954020981 6477713361865897120689467)
        ·
          refine ⟨9716570042798845681034201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477713361865897120689467 9716570042798845681034201)
          ·
            refine ⟨7287427532099134260775651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9716570042798845681034201 7287427532099134260775651)
            ·
              refine ⟨10931141298148701391163477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287427532099134260775651 10931141298148701391163477)
              ·
                refine ⟨128099312087680094427697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10931141298148701391163477 128099312087680094427697)
                ·
                  rfl

theorem cell23_6735758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_6735758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735758 prefixEnd_6735758 := by exact prefixLift 6735758
  have htrace : WordTrace (prefixWord ++ tailWord_6735758) baseStart_6735758 baseEnd_6735758 := by
    simpa [prefixWord, tailWord_6735758, baseEnd_6735758] using wordTrace_append hprefix tailTrace_6735758
  have hstable : (prefixWord ++ tailWord_6735758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735758).length < 2 ^ (prefixWord ++ tailWord_6735758).sum := by decide
  have hdescent : baseEnd_6735758 < baseStart_6735758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735761 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_6735761 : Nat := 118140960795 + 6735761 * 2 ^ 59
def prefixEnd_6735761 : Nat := 4983230072969 + 3 ^ 40 * 6735761 * 2
def baseEnd_6735761 : Nat := 3458682966809326037810305

theorem tailTrace_6735761 : CollatzResearch.WordTrace tailWord_6735761 prefixEnd_6735761 3458682966809326037810305 := by
  unfold tailWord_6735761
  simp only [CollatzResearch.WordTrace]
  refine ⟨245673386550495748237767137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163782257700330498825178091 245673386550495748237767137)
  ·
    refine ⟨184255039912871811178325353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245673386550495748237767137 184255039912871811178325353)
    ·
      refine ⟨138191279934653858383744015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184255039912871811178325353 138191279934653858383744015)
      ·
        refine ⟨207286919901980787575616023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138191279934653858383744015 207286919901980787575616023)
        ·
          refine ⟨310930379852971181363424035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207286919901980787575616023 310930379852971181363424035)
          ·
            refine ⟨466395569779456772045136053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310930379852971181363424035 466395569779456772045136053)
            ·
              refine ⟨43724584666824072379231505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466395569779456772045136053 43724584666824072379231505)
              ·
                refine ⟨32793438500118054284423629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43724584666824072379231505 32793438500118054284423629)
                ·
                  refine ⟨12297539437544270356658861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32793438500118054284423629 12297539437544270356658861)
                  ·
                    refine ⟨4611577289079101383747073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12297539437544270356658861 4611577289079101383747073)
                    ·
                      refine ⟨3458682966809326037810305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611577289079101383747073 3458682966809326037810305)
                      ·
                        rfl

theorem cell23_6735761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_6735761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735761 prefixEnd_6735761 := by exact prefixLift 6735761
  have htrace : WordTrace (prefixWord ++ tailWord_6735761) baseStart_6735761 baseEnd_6735761 := by
    simpa [prefixWord, tailWord_6735761, baseEnd_6735761] using wordTrace_append hprefix tailTrace_6735761
  have hstable : (prefixWord ++ tailWord_6735761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735761).length < 2 ^ (prefixWord ++ tailWord_6735761).sum := by decide
  have hdescent : baseEnd_6735761 < baseStart_6735761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735791 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 4, 2]
def baseStart_6735791 : Nat := 118140960795 + 6735791 * 2 ^ 59
def prefixEnd_6735791 : Nat := 4983230072969 + 3 ^ 40 * 6735791 * 2
def baseEnd_6735791 : Nat := 3458698371228960920435167

theorem tailTrace_6735791 : CollatzResearch.WordTrace tailWord_6735791 prefixEnd_6735791 3458698371228960920435167 := by
  unfold tailWord_6735791
  simp only [CollatzResearch.WordTrace]
  refine ⟨245674480740387063361359227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163782987160258042240906151 245674480740387063361359227)
  ·
    refine ⟨368511721110580595042038841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245674480740387063361359227 368511721110580595042038841)
    ·
      refine ⟨276383790832935446281529131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368511721110580595042038841 276383790832935446281529131)
      ·
        refine ⟨414575686249403169422293697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276383790832935446281529131 414575686249403169422293697)
        ·
          refine ⟨310931764687052377066720273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414575686249403169422293697 310931764687052377066720273)
          ·
            refine ⟨233198823515289282800040205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310931764687052377066720273 233198823515289282800040205)
            ·
              refine ⟨87449558818233481050015077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233198823515289282800040205 87449558818233481050015077)
              ·
                refine ⟨16396792278418777696877827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87449558818233481050015077 16396792278418777696877827)
                ·
                  refine ⟨24595188417628166545316741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16396792278418777696877827 24595188417628166545316741)
                  ·
                    refine ⟨4611597828305281227246889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24595188417628166545316741 4611597828305281227246889)
                    ·
                      refine ⟨3458698371228960920435167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611597828305281227246889 3458698371228960920435167)
                      ·
                        rfl

theorem cell23_6735791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4, 2].length) (baseStart_6735791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735791 prefixEnd_6735791 := by exact prefixLift 6735791
  have htrace : WordTrace (prefixWord ++ tailWord_6735791) baseStart_6735791 baseEnd_6735791 := by
    simpa [prefixWord, tailWord_6735791, baseEnd_6735791] using wordTrace_append hprefix tailTrace_6735791
  have hstable : (prefixWord ++ tailWord_6735791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735791).length < 2 ^ (prefixWord ++ tailWord_6735791).sum := by decide
  have hdescent : baseEnd_6735791 < baseStart_6735791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735794 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_6735794 : Nat := 118140960795 + 6735794 * 2 ^ 59
def prefixEnd_6735794 : Nat := 4983230072969 + 3 ^ 40 * 6735794 * 2
def baseEnd_6735794 : Nat := 3458699911670924408697653

theorem tailTrace_6735794 : CollatzResearch.WordTrace tailWord_6735794 prefixEnd_6735794 3458699911670924408697653 := by
  unfold tailWord_6735794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61418647539844048718429609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163783060106250796582478957 61418647539844048718429609)
  ·
    refine ⟨46063985654883036538822207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61418647539844048718429609 46063985654883036538822207)
    ·
      refine ⟨69095978482324554808233311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46063985654883036538822207 69095978482324554808233311)
      ·
        refine ⟨103643967723486832212349967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69095978482324554808233311 103643967723486832212349967)
        ·
          refine ⟨155465951585230248318524951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103643967723486832212349967 155465951585230248318524951)
          ·
            refine ⟨233198927377845372477787427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155465951585230248318524951 233198927377845372477787427)
            ·
              refine ⟨349798391066768058716681141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233198927377845372477787427 349798391066768058716681141)
              ·
                refine ⟨32793599162509505504688857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349798391066768058716681141 32793599162509505504688857)
                ·
                  refine ⟨24595199371882129128516643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32793599162509505504688857 24595199371882129128516643)
                  ·
                    refine ⟨36892799057823193692774965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24595199371882129128516643 36892799057823193692774965)
                    ·
                      refine ⟨3458699911670924408697653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36892799057823193692774965 3458699911670924408697653)
                      ·
                        rfl

theorem cell23_6735794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_6735794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735794 prefixEnd_6735794 := by exact prefixLift 6735794
  have htrace : WordTrace (prefixWord ++ tailWord_6735794) baseStart_6735794 baseEnd_6735794 := by
    simpa [prefixWord, tailWord_6735794, baseEnd_6735794] using wordTrace_append hprefix tailTrace_6735794
  have hstable : (prefixWord ++ tailWord_6735794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735794).length < 2 ^ (prefixWord ++ tailWord_6735794).sum := by decide
  have hdescent : baseEnd_6735794 < baseStart_6735794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735808 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2]
def baseStart_6735808 : Nat := 118140960795 + 6735808 * 2 ^ 59
def prefixEnd_6735808 : Nat := 4983230072969 + 3 ^ 40 * 6735808 * 2
def baseEnd_6735808 : Nat := 3458707100400087353922589

theorem tailTrace_6735808 : CollatzResearch.WordTrace tailWord_6735808 prefixEnd_6735808 3458707100400087353922589 := by
  unfold tailWord_6735808
  simp only [CollatzResearch.WordTrace]
  refine ⟨122837550390662737632364039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163783400520883650176485385 122837550390662737632364039)
  ·
    refine ⟨184256325585994106448546059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122837550390662737632364039 184256325585994106448546059)
    ·
      refine ⟨276384488378991159672819089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184256325585994106448546059 276384488378991159672819089)
      ·
        refine ⟨207288366284243369754614317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276384488378991159672819089 207288366284243369754614317)
        ·
          refine ⟨77733137356591263657980369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207288366284243369754614317 77733137356591263657980369)
          ·
            refine ⟨58299853017443447743485277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77733137356591263657980369 58299853017443447743485277)
            ·
              refine ⟨21862444881541292903806979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58299853017443447743485277 21862444881541292903806979)
              ·
                refine ⟨32793667322311939355710469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21862444881541292903806979 32793667322311939355710469)
                ·
                  refine ⟨6148812622933488629195713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32793667322311939355710469 6148812622933488629195713)
                  ·
                    refine ⟨4611609467200116471896785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148812622933488629195713 4611609467200116471896785)
                    ·
                      refine ⟨3458707100400087353922589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611609467200116471896785 3458707100400087353922589)
                      ·
                        rfl

theorem cell23_6735808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_6735808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735808 prefixEnd_6735808 := by exact prefixLift 6735808
  have htrace : WordTrace (prefixWord ++ tailWord_6735808) baseStart_6735808 baseEnd_6735808 := by
    simpa [prefixWord, tailWord_6735808, baseEnd_6735808] using wordTrace_append hprefix tailTrace_6735808
  have hstable : (prefixWord ++ tailWord_6735808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735808).length < 2 ^ (prefixWord ++ tailWord_6735808).sum := by decide
  have hdescent : baseEnd_6735808 < baseStart_6735808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735844 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_6735844 : Nat := 118140960795 + 6735844 * 2 ^ 59
def prefixEnd_6735844 : Nat := 4983230072969 + 3 ^ 40 * 6735844 * 2
def baseEnd_6735844 : Nat := 1152908528567883071024141

theorem tailTrace_6735844 : CollatzResearch.WordTrace tailWord_6735844 prefixEnd_6735844 1152908528567883071024141 := by
  unfold tailWord_6735844
  simp only [CollatzResearch.WordTrace]
  refine ⟨122838206904597526706519293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163784275872796702275359057 122838206904597526706519293)
  ·
    refine ⟨46064327589224072514944735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122838206904597526706519293 46064327589224072514944735)
    ·
      refine ⟨69096491383836108772417103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46064327589224072514944735 69096491383836108772417103)
      ·
        refine ⟨103644737075754163158625655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69096491383836108772417103 103644737075754163158625655)
        ·
          refine ⟨155467105613631244737938483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103644737075754163158625655 155467105613631244737938483)
          ·
            refine ⟨233200658420446867106907725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155467105613631244737938483 233200658420446867106907725)
            ·
              refine ⟨87450246907667575165090397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233200658420446867106907725 87450246907667575165090397)
              ·
                refine ⟨32793842590375340686908899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87450246907667575165090397 32793842590375340686908899)
                ·
                  refine ⟨49190763885563011030363349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32793842590375340686908899 49190763885563011030363349)
                  ·
                    refine ⟨1152908528567883071024141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49190763885563011030363349 1152908528567883071024141)
                    ·
                      rfl

theorem cell23_6735844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_6735844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735844 prefixEnd_6735844 := by exact prefixLift 6735844
  have htrace : WordTrace (prefixWord ++ tailWord_6735844) baseStart_6735844 baseEnd_6735844 := by
    simpa [prefixWord, tailWord_6735844, baseEnd_6735844] using wordTrace_append hprefix tailTrace_6735844
  have hstable : (prefixWord ++ tailWord_6735844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735844).length < 2 ^ (prefixWord ++ tailWord_6735844).sum := by decide
  have hdescent : baseEnd_6735844 < baseStart_6735844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735876 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6735876 : Nat := 118140960795 + 6735876 * 2 ^ 59
def prefixEnd_6735876 : Nat := 4983230072969 + 3 ^ 40 * 6735876 * 2
def baseEnd_6735876 : Nat := 3458742017084593087872277

theorem tailTrace_6735876 : CollatzResearch.WordTrace tailWord_6735876 prefixEnd_6735876 3458742017084593087872277 := by
  unfold tailWord_6735876
  simp only [CollatzResearch.WordTrace]
  refine ⟨122838790472539561439101741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163785053963386081918802321 122838790472539561439101741)
  ·
    refine ⟨46064546427202335539663153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122838790472539561439101741 46064546427202335539663153)
    ·
      refine ⟨34548409820401751654747365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46064546427202335539663153 34548409820401751654747365)
      ·
        refine ⟨6477826841325328435265131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34548409820401751654747365 6477826841325328435265131)
        ·
          refine ⟨9716740261987992652897697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477826841325328435265131 9716740261987992652897697)
          ·
            refine ⟨7287555196490994489673273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9716740261987992652897697 7287555196490994489673273)
            ·
              refine ⟨5465666397368245867254955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7287555196490994489673273 5465666397368245867254955)
              ·
                refine ⟨8198499596052368800882433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465666397368245867254955 8198499596052368800882433)
                ·
                  refine ⟨6148874697039276600661825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198499596052368800882433 6148874697039276600661825)
                  ·
                    refine ⟨4611656022779457450496369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6148874697039276600661825 4611656022779457450496369)
                    ·
                      refine ⟨3458742017084593087872277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611656022779457450496369 3458742017084593087872277)
                      ·
                        rfl

theorem cell23_6735876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6735876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735876 prefixEnd_6735876 := by exact prefixLift 6735876
  have htrace : WordTrace (prefixWord ++ tailWord_6735876) baseStart_6735876 baseEnd_6735876 := by
    simpa [prefixWord, tailWord_6735876, baseEnd_6735876] using wordTrace_append hprefix tailTrace_6735876
  have hstable : (prefixWord ++ tailWord_6735876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735876).length < 2 ^ (prefixWord ++ tailWord_6735876).sum := by decide
  have hdescent : baseEnd_6735876 < baseStart_6735876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735891 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 3, 4]
def baseStart_6735891 : Nat := 118140960795 + 6735891 * 2 ^ 59
def prefixEnd_6735891 : Nat := 4983230072969 + 3 ^ 40 * 6735891 * 2
def baseEnd_6735891 : Nat := 1152916573098136843061569

theorem tailTrace_6735891 : CollatzResearch.WordTrace tailWord_6735891 prefixEnd_6735891 1152916573098136843061569 := by
  unfold tailWord_6735891
  simp only [CollatzResearch.WordTrace]
  refine ⟨245678128040024780439999527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163785418693349853626666351 245678128040024780439999527)
  ·
    refine ⟨368517192060037170659999291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245678128040024780439999527 368517192060037170659999291)
    ·
      refine ⟨552775788090055755989998937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368517192060037170659999291 552775788090055755989998937)
      ·
        refine ⟨414581841067541816992499203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552775788090055755989998937 414581841067541816992499203)
        ·
          refine ⟨621872761601312725488748805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414581841067541816992499203 621872761601312725488748805)
          ·
            refine ⟨116601142800246136029140401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 621872761601312725488748805 116601142800246136029140401)
            ·
              refine ⟨87450857100184602021855301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116601142800246136029140401 87450857100184602021855301)
              ·
                refine ⟨16397035706284612879097869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87450857100184602021855301 16397035706284612879097869)
                ·
                  refine ⟨6148888389856729829661701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16397035706284612879097869 6148888389856729829661701)
                  ·
                    refine ⟨1152916573098136843061569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6148888389856729829661701 1152916573098136843061569)
                    ·
                      rfl

theorem cell23_6735891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 4].length) (baseStart_6735891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735891 prefixEnd_6735891 := by exact prefixLift 6735891
  have htrace : WordTrace (prefixWord ++ tailWord_6735891) baseStart_6735891 baseEnd_6735891 := by
    simpa [prefixWord, tailWord_6735891, baseEnd_6735891] using wordTrace_append hprefix tailTrace_6735891
  have hstable : (prefixWord ++ tailWord_6735891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735891).length < 2 ^ (prefixWord ++ tailWord_6735891).sum := by decide
  have hdescent : baseEnd_6735891 < baseStart_6735891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735898 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_6735898 : Nat := 118140960795 + 6735898 * 2 ^ 59
def prefixEnd_6735898 : Nat := 4983230072969 + 3 ^ 40 * 6735898 * 2
def baseEnd_6735898 : Nat := 3458753313658992001797175

theorem tailTrace_6735898 : CollatzResearch.WordTrace tailWord_6735898 prefixEnd_6735898 3458753313658992001797175 := by
  unfold tailWord_6735898
  simp only [CollatzResearch.WordTrace]
  refine ⟨61419595837749855158876087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163785588900666280423669565 61419595837749855158876087)
  ·
    refine ⟨92129393756624782738314131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61419595837749855158876087 92129393756624782738314131)
    ·
      refine ⟨138194090634937174107471197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92129393756624782738314131 138194090634937174107471197)
      ·
        refine ⟨51822783988101440290301699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138194090634937174107471197 51822783988101440290301699)
        ·
          refine ⟨77734175982152160435452549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51822783988101440290301699 77734175982152160435452549)
          ·
            refine ⟨14575157996653530081647353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77734175982152160435452549 14575157996653530081647353)
            ·
              refine ⟨10931368497490147561235515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14575157996653530081647353 10931368497490147561235515)
              ·
                refine ⟨16397052746235221341853273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10931368497490147561235515 16397052746235221341853273)
                ·
                  refine ⟨12297789559676416006389955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16397052746235221341853273 12297789559676416006389955)
                  ·
                    refine ⟨18446684339514624009584933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12297789559676416006389955 18446684339514624009584933)
                    ·
                      refine ⟨3458753313658992001797175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18446684339514624009584933 3458753313658992001797175)
                      ·
                        rfl

theorem cell23_6735898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_6735898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735898 prefixEnd_6735898 := by exact prefixLift 6735898
  have htrace : WordTrace (prefixWord ++ tailWord_6735898) baseStart_6735898 baseEnd_6735898 := by
    simpa [prefixWord, tailWord_6735898, baseEnd_6735898] using wordTrace_append hprefix tailTrace_6735898
  have hstable : (prefixWord ++ tailWord_6735898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735898).length < 2 ^ (prefixWord ++ tailWord_6735898).sum := by decide
  have hdescent : baseEnd_6735898 < baseStart_6735898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735921 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 6]
def baseStart_6735921 : Nat := 118140960795 + 6735921 * 2 ^ 59
def prefixEnd_6735921 : Nat := 4983230072969 + 3 ^ 40 * 6735921 * 2
def baseEnd_6735921 : Nat := 384307235968227267978841

theorem tailTrace_6735921 : CollatzResearch.WordTrace tailWord_6735921 prefixEnd_6735921 384307235968227267978841 := by
  unfold tailWord_6735921
  simp only [CollatzResearch.WordTrace]
  refine ⟨245679222229916095563591617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163786148153277397042394411 245679222229916095563591617)
  ·
    refine ⟨184259416672437071672693713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245679222229916095563591617 184259416672437071672693713)
    ·
      refine ⟨138194562504327803754520285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184259416672437071672693713 138194562504327803754520285)
      ·
        refine ⟨51822960939122926407945107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138194562504327803754520285 51822960939122926407945107)
        ·
          refine ⟨77734441408684389611917661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51822960939122926407945107 77734441408684389611917661)
          ·
            refine ⟨29150415528256646104469123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77734441408684389611917661 29150415528256646104469123)
            ·
              refine ⟨43725623292384969156703685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29150415528256646104469123 43725623292384969156703685)
              ·
                refine ⟨8198554367322181716881941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43725623292384969156703685 8198554367322181716881941)
                ·
                  refine ⟨384307235968227267978841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8198554367322181716881941 384307235968227267978841)
                  ·
                    rfl

theorem cell23_6735921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_6735921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735921 prefixEnd_6735921 := by exact prefixLift 6735921
  have htrace : WordTrace (prefixWord ++ tailWord_6735921) baseStart_6735921 baseEnd_6735921 := by
    simpa [prefixWord, tailWord_6735921, baseEnd_6735921] using wordTrace_append hprefix tailTrace_6735921
  have hstable : (prefixWord ++ tailWord_6735921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735921).length < 2 ^ (prefixWord ++ tailWord_6735921).sum := by decide
  have hdescent : baseEnd_6735921 < baseStart_6735921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735948 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6735948 : Nat := 118140960795 + 6735948 * 2 ^ 59
def prefixEnd_6735948 : Nat := 4983230072969 + 3 ^ 40 * 6735948 * 2
def baseEnd_6735948 : Nat := 3458778987691716806171945

theorem tailTrace_6735948 : CollatzResearch.WordTrace tailWord_6735948 prefixEnd_6735948 3458778987691716806171945 := by
  unfold tailWord_6735948
  simp only [CollatzResearch.WordTrace]
  refine ⟨122840103500409139587412249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163786804667212186116549665 122840103500409139587412249)
  ·
    refine ⟨92130077625306854690559187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122840103500409139587412249 92130077625306854690559187)
    ·
      refine ⟨138195116437960282035838781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92130077625306854690559187 138195116437960282035838781)
      ·
        refine ⟨51823168664235105763439543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138195116437960282035838781 51823168664235105763439543)
        ·
          refine ⟨77734752996352658645159315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51823168664235105763439543 77734752996352658645159315)
          ·
            refine ⟨116602129494528987967738973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77734752996352658645159315 116602129494528987967738973)
            ·
              refine ⟨43725798560448370487902115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116602129494528987967738973 43725798560448370487902115)
              ·
                refine ⟨65588697840672555731853173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43725798560448370487902115 65588697840672555731853173)
                ·
                  refine ⟨6148940422563052099861235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65588697840672555731853173 6148940422563052099861235)
                  ·
                    refine ⟨9223410633844578149791853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6148940422563052099861235 9223410633844578149791853)
                    ·
                      refine ⟨3458778987691716806171945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9223410633844578149791853 3458778987691716806171945)
                      ·
                        rfl

theorem cell23_6735948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6735948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735948 prefixEnd_6735948 := by exact prefixLift 6735948
  have htrace : WordTrace (prefixWord ++ tailWord_6735948) baseStart_6735948 baseEnd_6735948 := by
    simpa [prefixWord, tailWord_6735948, baseEnd_6735948] using wordTrace_append hprefix tailTrace_6735948
  have hstable : (prefixWord ++ tailWord_6735948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735948).length < 2 ^ (prefixWord ++ tailWord_6735948).sum := by decide
  have hdescent : baseEnd_6735948 < baseStart_6735948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735968 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_6735968 : Nat := 118140960795 + 6735968 * 2 ^ 59
def prefixEnd_6735968 : Nat := 4983230072969 + 3 ^ 40 * 6735968 * 2
def baseEnd_6735968 : Nat := 1152929752434935575973951

theorem tailTrace_6735968 : CollatzResearch.WordTrace tailWord_6735968 prefixEnd_6735968 1152929752434935575973951 := by
  unfold tailWord_6735968
  simp only [CollatzResearch.WordTrace]
  refine ⟨122840468230372911295276279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163787290973830548393701705 122840468230372911295276279)
  ·
    refine ⟨184260702345559366942914419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122840468230372911295276279 184260702345559366942914419)
    ·
      refine ⟨276391053518339050414371629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184260702345559366942914419 276391053518339050414371629)
      ·
        refine ⟨103646645069377143905389361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276391053518339050414371629 103646645069377143905389361)
        ·
          refine ⟨77734983802032857929042021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103646645069377143905389361 77734983802032857929042021)
          ·
            refine ⟨14575309462881160861695379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77734983802032857929042021 14575309462881160861695379)
            ·
              refine ⟨21862964194321741292543069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575309462881160861695379 21862964194321741292543069)
              ·
                refine ⟨8198611572870652984703651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21862964194321741292543069 8198611572870652984703651)
                ·
                  refine ⟨12297917359305979477055477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8198611572870652984703651 12297917359305979477055477)
                  ·
                    refine ⟨1152929752434935575973951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12297917359305979477055477 1152929752434935575973951)
                    ·
                      rfl

theorem cell23_6735968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_6735968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735968 prefixEnd_6735968 := by exact prefixLift 6735968
  have htrace : WordTrace (prefixWord ++ tailWord_6735968) baseStart_6735968 baseEnd_6735968 := by
    simpa [prefixWord, tailWord_6735968, baseEnd_6735968] using wordTrace_append hprefix tailTrace_6735968
  have hstable : (prefixWord ++ tailWord_6735968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735968).length < 2 ^ (prefixWord ++ tailWord_6735968).sum := by decide
  have hdescent : baseEnd_6735968 < baseStart_6735968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735982 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6735982 : Nat := 118140960795 + 6735982 * 2 ^ 59
def prefixEnd_6735982 : Nat := 4983230072969 + 3 ^ 40 * 6735982 * 2
def baseEnd_6735982 : Nat := 3458796446033969673146789

theorem tailTrace_6735982 : CollatzResearch.WordTrace tailWord_6735982 prefixEnd_6735982 3458796446033969673146789 := by
  unfold tailWord_6735982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30710180885336887872695275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163787631388463401987708133 30710180885336887872695275)
  ·
    refine ⟨46065271328005331809042913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30710180885336887872695275 46065271328005331809042913)
    ·
      refine ⟨34548953496003998856782185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46065271328005331809042913 34548953496003998856782185)
      ·
        refine ⟨25911715122002999142586639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34548953496003998856782185 25911715122002999142586639)
        ·
          refine ⟨38867572683004498713879959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25911715122002999142586639 38867572683004498713879959)
          ·
            refine ⟨58301359024506748070819939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38867572683004498713879959 58301359024506748070819939)
            ·
              refine ⟨87452038536760122106229909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58301359024506748070819939 87452038536760122106229909)
              ·
                refine ⟨4099314306410630723729527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87452038536760122106229909 4099314306410630723729527)
                ·
                  refine ⟨6148971459615946085594291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099314306410630723729527 6148971459615946085594291)
                  ·
                    refine ⟨9223457189423919128391437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6148971459615946085594291 9223457189423919128391437)
                    ·
                      refine ⟨3458796446033969673146789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9223457189423919128391437 3458796446033969673146789)
                      ·
                        rfl

theorem cell23_6735982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6735982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735982 prefixEnd_6735982 := by exact prefixLift 6735982
  have htrace : WordTrace (prefixWord ++ tailWord_6735982) baseStart_6735982 baseEnd_6735982 := by
    simpa [prefixWord, tailWord_6735982, baseEnd_6735982] using wordTrace_append hprefix tailTrace_6735982
  have hstable : (prefixWord ++ tailWord_6735982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735982).length < 2 ^ (prefixWord ++ tailWord_6735982).sum := by decide
  have hdescent : baseEnd_6735982 < baseStart_6735982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6735991 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_6735991 : Nat := 118140960795 + 6735991 * 2 ^ 59
def prefixEnd_6735991 : Nat := 4983230072969 + 3 ^ 40 * 6735991 * 2
def baseEnd_6735991 : Nat := 3458801067359860137934247

theorem tailTrace_6735991 : CollatzResearch.WordTrace tailWord_6735991 prefixEnd_6735991 3458801067359860137934247 := by
  unfold tailWord_6735991
  simp only [CollatzResearch.WordTrace]
  refine ⟨245681775339662497518639827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163787850226441665012426551 245681775339662497518639827)
  ·
    refine ⟨368522663009493746277959741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245681775339662497518639827 368522663009493746277959741)
    ·
      refine ⟨138195998628560154854234903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368522663009493746277959741 138195998628560154854234903)
      ·
        refine ⟨207293997942840232281352355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138195998628560154854234903 207293997942840232281352355)
        ·
          refine ⟨310940996914260348422028533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207293997942840232281352355 310940996914260348422028533)
          ·
            refine ⟨29150718460711907664565175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310940996914260348422028533 29150718460711907664565175)
            ·
              refine ⟨43726077691067861496847763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29150718460711907664565175 43726077691067861496847763)
              ·
                refine ⟨65589116536601792245271645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43726077691067861496847763 65589116536601792245271645)
                ·
                  refine ⟨24595918701225672091976867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65589116536601792245271645 24595918701225672091976867)
                  ·
                    refine ⟨36893878051838508137965301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24595918701225672091976867 36893878051838508137965301)
                    ·
                      refine ⟨3458801067359860137934247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36893878051838508137965301 3458801067359860137934247)
                      ·
                        rfl

theorem cell23_6735991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_6735991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6735991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6735991 prefixEnd_6735991 := by exact prefixLift 6735991
  have htrace : WordTrace (prefixWord ++ tailWord_6735991) baseStart_6735991 baseEnd_6735991 := by
    simpa [prefixWord, tailWord_6735991, baseEnd_6735991] using wordTrace_append hprefix tailTrace_6735991
  have hstable : (prefixWord ++ tailWord_6735991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6735991).length < 2 ^ (prefixWord ++ tailWord_6735991).sum := by decide
  have hdescent : baseEnd_6735991 < baseStart_6735991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6735991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736005 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_6736005 : Nat := 118140960795 + 6736005 * 2 ^ 59
def prefixEnd_6736005 : Nat := 4983230072969 + 3 ^ 40 * 6736005 * 2
def baseEnd_6736005 : Nat := 3458808256089023083159183

theorem tailTrace_6736005 : CollatzResearch.WordTrace tailWord_6736005 prefixEnd_6736005 3458808256089023083159183 := by
  unfold tailWord_6736005
  simp only [CollatzResearch.WordTrace]
  refine ⟨245682285961611777909649469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163788190641074518606432979 245682285961611777909649469)
  ·
    refine ⟨92130857235604416716118551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245682285961611777909649469 92130857235604416716118551)
    ·
      refine ⟨138196285853406625074177827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92130857235604416716118551 138196285853406625074177827)
      ·
        refine ⟨207294428780109937611266741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138196285853406625074177827 207294428780109937611266741)
        ·
          refine ⟨19433852698135306651056257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207294428780109937611266741 19433852698135306651056257)
          ·
            refine ⟨14575389523601479988292193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19433852698135306651056257 14575389523601479988292193)
            ·
              refine ⟨10931542142701109991219145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14575389523601479988292193 10931542142701109991219145)
              ·
                refine ⟨8198656607025832493414359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10931542142701109991219145 8198656607025832493414359)
                ·
                  refine ⟨12297984910538748740121539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8198656607025832493414359 12297984910538748740121539)
                  ·
                    refine ⟨18446977365808123110182309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12297984910538748740121539 18446977365808123110182309)
                    ·
                      refine ⟨3458808256089023083159183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18446977365808123110182309 3458808256089023083159183)
                      ·
                        rfl

theorem cell23_6736005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_6736005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736005 prefixEnd_6736005 := by exact prefixLift 6736005
  have htrace : WordTrace (prefixWord ++ tailWord_6736005) baseStart_6736005 baseEnd_6736005 := by
    simpa [prefixWord, tailWord_6736005, baseEnd_6736005] using wordTrace_append hprefix tailTrace_6736005
  have hstable : (prefixWord ++ tailWord_6736005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736005).length < 2 ^ (prefixWord ++ tailWord_6736005).sum := by decide
  have hdescent : baseEnd_6736005 < baseStart_6736005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736018 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6736018 : Nat := 118140960795 + 6736018 * 2 ^ 59
def prefixEnd_6736018 : Nat := 4983230072969 + 3 ^ 40 * 6736018 * 2
def baseEnd_6736018 : Nat := 3458814931337531532296623

theorem tailTrace_6736018 : CollatzResearch.WordTrace tailWord_6736018 prefixEnd_6736018 3458814931337531532296623 := by
  unfold tailWord_6736018
  simp only [CollatzResearch.WordTrace]
  refine ⟨61420690027641170282468177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163788506740376454086581805 61420690027641170282468177)
  ·
    refine ⟨46065517520730877711851133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61420690027641170282468177 46065517520730877711851133)
    ·
      refine ⟨17274569070274079141944175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46065517520730877711851133 17274569070274079141944175)
      ·
        refine ⟨25911853605411118712916263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17274569070274079141944175 25911853605411118712916263)
        ·
          refine ⟨38867780408116678069374395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25911853605411118712916263 38867780408116678069374395)
          ·
            refine ⟨58301670612175017104061593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38867780408116678069374395 58301670612175017104061593)
            ·
              refine ⟨43726252959131262828046195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58301670612175017104061593 43726252959131262828046195)
              ·
                refine ⟨65589379438696894242069293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43726252959131262828046195 65589379438696894242069293)
                ·
                  refine ⟨24596017289511335340775985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65589379438696894242069293 24596017289511335340775985)
                  ·
                    refine ⟨18447012967133501505581989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24596017289511335340775985 18447012967133501505581989)
                    ·
                      refine ⟨3458814931337531532296623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18447012967133501505581989 3458814931337531532296623)
                      ·
                        rfl

theorem cell23_6736018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6736018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736018 prefixEnd_6736018 := by exact prefixLift 6736018
  have htrace : WordTrace (prefixWord ++ tailWord_6736018) baseStart_6736018 baseEnd_6736018 := by
    simpa [prefixWord, tailWord_6736018, baseEnd_6736018] using wordTrace_append hprefix tailTrace_6736018
  have hstable : (prefixWord ++ tailWord_6736018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736018).length < 2 ^ (prefixWord ++ tailWord_6736018).sum := by decide
  have hdescent : baseEnd_6736018 < baseStart_6736018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736049 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_6736049 : Nat := 118140960795 + 6736049 * 2 ^ 59
def prefixEnd_6736049 : Nat := 4983230072969 + 3 ^ 40 * 6736049 * 2
def baseEnd_6736049 : Nat := 1152943616412606970336327

theorem tailTrace_6736049 : CollatzResearch.WordTrace tailWord_6736049 prefixEnd_6736049 1152943616412606970336327 := by
  unfold tailWord_6736049
  simp only [CollatzResearch.WordTrace]
  refine ⟨245683890773452373424251201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163789260515634915616167467 245683890773452373424251201)
  ·
    refine ⟨184262918080089280068188401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245683890773452373424251201 184262918080089280068188401)
    ·
      refine ⟨138197188560066960051141301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184262918080089280068188401 138197188560066960051141301)
      ·
        refine ⟨12955986427506277504794497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138197188560066960051141301 12955986427506277504794497)
        ·
          refine ⟨9716989820629708128595873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12955986427506277504794497 9716989820629708128595873)
          ·
            refine ⟨7287742365472281096446905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9716989820629708128595873 7287742365472281096446905)
            ·
              refine ⟨5465806774104210822335179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7287742365472281096446905 5465806774104210822335179)
              ·
                refine ⟨8198710161156316233502769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465806774104210822335179 8198710161156316233502769)
                ·
                  refine ⟨6149032620867237175127077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8198710161156316233502769 6149032620867237175127077)
                  ·
                    refine ⟨1152943616412606970336327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149032620867237175127077 1152943616412606970336327)
                    ·
                      rfl

theorem cell23_6736049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_6736049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736049 prefixEnd_6736049 := by exact prefixLift 6736049
  have htrace : WordTrace (prefixWord ++ tailWord_6736049) baseStart_6736049 baseEnd_6736049 := by
    simpa [prefixWord, tailWord_6736049, baseEnd_6736049] using wordTrace_append hprefix tailTrace_6736049
  have hstable : (prefixWord ++ tailWord_6736049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736049).length < 2 ^ (prefixWord ++ tailWord_6736049).sum := by decide
  have hdescent : baseEnd_6736049 < baseStart_6736049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736061 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6736061 : Nat := 118140960795 + 6736061 * 2 ^ 59
def prefixEnd_6736061 : Nat := 4983230072969 + 3 ^ 40 * 6736061 * 2
def baseEnd_6736061 : Nat := 3458837011005674864058925

theorem tailTrace_6736061 : CollatzResearch.WordTrace tailWord_6736061 prefixEnd_6736061 3458837011005674864058925 := by
  unfold tailWord_6736061
  simp only [CollatzResearch.WordTrace]
  refine ⟨245684328449408899473688037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163789552299605932982458691 245684328449408899473688037)
  ·
    refine ⟨46065811584264168651316507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245684328449408899473688037 46065811584264168651316507)
    ·
      refine ⟨69098717376396252976974761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46065811584264168651316507 69098717376396252976974761)
      ·
        refine ⟨51824038032297189732731071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69098717376396252976974761 51824038032297189732731071)
        ·
          refine ⟨77736057048445784599096607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51824038032297189732731071 77736057048445784599096607)
          ·
            refine ⟨116604085572668676898644911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77736057048445784599096607 116604085572668676898644911)
            ·
              refine ⟨174906128359003015347967367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116604085572668676898644911 174906128359003015347967367)
              ·
                refine ⟨262359192538504523021951051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174906128359003015347967367 262359192538504523021951051)
                ·
                  refine ⟨393538788807756784532926577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262359192538504523021951051 393538788807756784532926577)
                  ·
                    refine ⟨295154091605817588399694933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393538788807756784532926577 295154091605817588399694933)
                    ·
                      refine ⟨3458837011005674864058925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 295154091605817588399694933 3458837011005674864058925)
                      ·
                        rfl

theorem cell23_6736061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6736061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736061 prefixEnd_6736061 := by exact prefixLift 6736061
  have htrace : WordTrace (prefixWord ++ tailWord_6736061) baseStart_6736061 baseEnd_6736061 := by
    simpa [prefixWord, tailWord_6736061, baseEnd_6736061] using wordTrace_append hprefix tailTrace_6736061
  have hstable : (prefixWord ++ tailWord_6736061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736061).length < 2 ^ (prefixWord ++ tailWord_6736061).sum := by decide
  have hdescent : baseEnd_6736061 < baseStart_6736061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736071 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 6]
def baseStart_6736071 : Nat := 118140960795 + 6736071 * 2 ^ 59
def prefixEnd_6736071 : Nat := 4983230072969 + 3 ^ 40 * 6736071 * 2
def baseEnd_6736071 : Nat := 1152947381937406608311293

theorem tailTrace_6736071 : CollatzResearch.WordTrace tailWord_6736071 prefixEnd_6736071 1152947381937406608311293 := by
  unfold tailWord_6736071
  simp only [CollatzResearch.WordTrace]
  refine ⟨245684693179372671181552067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163789795452915114121034711 245684693179372671181552067)
  ·
    refine ⟨368527039769059006772328101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245684693179372671181552067 368527039769059006772328101)
    ·
      refine ⟨69098819956698563769811519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368527039769059006772328101 69098819956698563769811519)
      ·
        refine ⟨103648229935047845654717279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69098819956698563769811519 103648229935047845654717279)
        ·
          refine ⟨155472344902571768482075919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103648229935047845654717279 155472344902571768482075919)
          ·
            refine ⟨233208517353857652723113879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155472344902571768482075919 233208517353857652723113879)
            ·
              refine ⟨349812776030786479084670819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233208517353857652723113879 349812776030786479084670819)
              ·
                refine ⟨524719164046179718627006229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349812776030786479084670819 524719164046179718627006229)
                ·
                  refine ⟨24596210814664674310640917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 524719164046179718627006229 24596210814664674310640917)
                  ·
                    refine ⟨1152947381937406608311293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24596210814664674310640917 1152947381937406608311293)
                    ·
                      rfl

theorem cell23_6736071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_6736071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736071 prefixEnd_6736071 := by exact prefixLift 6736071
  have htrace : WordTrace (prefixWord ++ tailWord_6736071) baseStart_6736071 baseEnd_6736071 := by
    simpa [prefixWord, tailWord_6736071, baseEnd_6736071] using wordTrace_append hprefix tailTrace_6736071
  have hstable : (prefixWord ++ tailWord_6736071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736071).length < 2 ^ (prefixWord ++ tailWord_6736071).sum := by decide
  have hdescent : baseEnd_6736071 < baseStart_6736071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736108 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6736108 : Nat := 118140960795 + 6736108 * 2 ^ 59
def prefixEnd_6736108 : Nat := 4983230072969 + 3 ^ 40 * 6736108 * 2
def baseEnd_6736108 : Nat := 3458861144596436180171209

theorem tailTrace_6736108 : CollatzResearch.WordTrace tailWord_6736108 prefixEnd_6736108 3458861144596436180171209 := by
  unfold tailWord_6736108
  simp only [CollatzResearch.WordTrace]
  refine ⟨122843021340119313250324489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163790695120159084333765985 122843021340119313250324489)
  ·
    refine ⟨92132266005089484937743367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122843021340119313250324489 92132266005089484937743367)
    ·
      refine ⟨138198399007634227406615051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92132266005089484937743367 138198399007634227406615051)
      ·
        refine ⟨207297598511451341109922577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138198399007634227406615051 207297598511451341109922577)
        ·
          refine ⟨155473198883588505832441933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207297598511451341109922577 155473198883588505832441933)
          ·
            refine ⟨58302449581345689687165725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155473198883588505832441933 58302449581345689687165725)
            ·
              refine ⟨21863418593004633632687147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58302449581345689687165725 21863418593004633632687147)
              ·
                refine ⟨32795127889506950449030721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863418593004633632687147 32795127889506950449030721)
                ·
                  refine ⟨24596345917130212836773041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32795127889506950449030721 24596345917130212836773041)
                  ·
                    refine ⟨18447259437847659627579781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24596345917130212836773041 18447259437847659627579781)
                    ·
                      refine ⟨3458861144596436180171209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18447259437847659627579781 3458861144596436180171209)
                      ·
                        rfl

theorem cell23_6736108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6736108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736108 prefixEnd_6736108 := by exact prefixLift 6736108
  have htrace : WordTrace (prefixWord ++ tailWord_6736108) baseStart_6736108 baseEnd_6736108 := by
    simpa [prefixWord, tailWord_6736108, baseEnd_6736108] using wordTrace_append hprefix tailTrace_6736108
  have hstable : (prefixWord ++ tailWord_6736108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736108).length < 2 ^ (prefixWord ++ tailWord_6736108).sum := by decide
  have hdescent : baseEnd_6736108 < baseStart_6736108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736118 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6736118 : Nat := 118140960795 + 6736118 * 2 ^ 59
def prefixEnd_6736118 : Nat := 4983230072969 + 3 ^ 40 * 6736118 * 2
def baseEnd_6736118 : Nat := 384318475489220126782907

theorem tailTrace_6736118 : CollatzResearch.WordTrace tailWord_6736118 prefixEnd_6736118 384318475489220126782907 := by
  unfold tailWord_6736118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15355400463137649888032063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163790938273468265472342005 15355400463137649888032063)
  ·
    refine ⟨23033100694706474832048095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15355400463137649888032063 23033100694706474832048095)
    ·
      refine ⟨34549651042059712248072143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23033100694706474832048095 34549651042059712248072143)
      ·
        refine ⟨51824476563089568372108215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34549651042059712248072143 51824476563089568372108215)
        ·
          refine ⟨77736714844634352558162323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51824476563089568372108215 77736714844634352558162323)
          ·
            refine ⟨116605072266951528837243485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77736714844634352558162323 116605072266951528837243485)
            ·
              refine ⟨43726902100106823313966307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116605072266951528837243485 43726902100106823313966307)
              ·
                refine ⟨65590353150160234970949461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43726902100106823313966307 65590353150160234970949461)
                ·
                  refine ⟨384318475489220126782907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65590353150160234970949461 384318475489220126782907)
                  ·
                    rfl

theorem cell23_6736118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6736118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736118 prefixEnd_6736118 := by exact prefixLift 6736118
  have htrace : WordTrace (prefixWord ++ tailWord_6736118) baseStart_6736118 baseEnd_6736118 := by
    simpa [prefixWord, tailWord_6736118, baseEnd_6736118] using wordTrace_append hprefix tailTrace_6736118
  have hstable : (prefixWord ++ tailWord_6736118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736118).length < 2 ^ (prefixWord ++ tailWord_6736118).sum := by decide
  have hdescent : baseEnd_6736118 < baseStart_6736118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736185 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6736185 : Nat := 118140960795 + 6736185 * 2 ^ 59
def prefixEnd_6736185 : Nat := 4983230072969 + 3 ^ 40 * 6736185 * 2
def baseEnd_6736185 : Nat := 3458900682606832378908355

theorem tailTrace_6736185 : CollatzResearch.WordTrace tailWord_6736185 prefixEnd_6736185 3458900682606832378908355 := by
  unfold tailWord_6736185
  simp only [CollatzResearch.WordTrace]
  refine ⟨245688851100959668651202009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163792567400639779100801339 245688851100959668651202009)
  ·
    refine ⟨184266638325719751488401507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245688851100959668651202009 184266638325719751488401507)
    ·
      refine ⟨276399957488579627232602261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184266638325719751488401507 276399957488579627232602261)
      ·
        refine ⟨12956248007277170026528231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276399957488579627232602261 12956248007277170026528231)
        ·
          refine ⟨19434372010915755039792347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12956248007277170026528231 19434372010915755039792347)
          ·
            refine ⟨29151558016373632559688521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19434372010915755039792347 29151558016373632559688521)
            ·
              refine ⟨21863668512280224419766391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29151558016373632559688521 21863668512280224419766391)
              ·
                refine ⟨32795502768420336629649587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863668512280224419766391 32795502768420336629649587)
                ·
                  refine ⟨49193254152630504944474381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32795502768420336629649587 49193254152630504944474381)
                  ·
                    refine ⟨18447470307236439354177893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49193254152630504944474381 18447470307236439354177893)
                    ·
                      refine ⟨3458900682606832378908355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18447470307236439354177893 3458900682606832378908355)
                      ·
                        rfl

theorem cell23_6736185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6736185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736185 prefixEnd_6736185 := by exact prefixLift 6736185
  have htrace : WordTrace (prefixWord ++ tailWord_6736185) baseStart_6736185 baseEnd_6736185 := by
    simpa [prefixWord, tailWord_6736185, baseEnd_6736185] using wordTrace_append hprefix tailTrace_6736185
  have hstable : (prefixWord ++ tailWord_6736185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736185).length < 2 ^ (prefixWord ++ tailWord_6736185).sum := by decide
  have hdescent : baseEnd_6736185 < baseStart_6736185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736208 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 8]
def baseStart_6736208 : Nat := 118140960795 + 6736208 * 2 ^ 59
def prefixEnd_6736208 : Nat := 4983230072969 + 3 ^ 40 * 6736208 * 2
def baseEnd_6736208 : Nat := 384323610295765087657861

theorem tailTrace_6736208 : CollatzResearch.WordTrace tailWord_6736208 prefixEnd_6736208 384323610295765087657861 := by
  unfold tailWord_6736208
  simp only [CollatzResearch.WordTrace]
  refine ⟨122844844989938171789644639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163793126653250895719526185 122844844989938171789644639)
  ·
    refine ⟨184267267484907257684466959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122844844989938171789644639 184267267484907257684466959)
    ·
      refine ⟨276400901227360886526700439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184267267484907257684466959 276400901227360886526700439)
      ·
        refine ⟨414601351841041329790050659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276400901227360886526700439 414601351841041329790050659)
        ·
          refine ⟨621902027761561994685075989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414601351841041329790050659 621902027761561994685075989)
          ·
            refine ⟨29151657551323218500862937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 621902027761561994685075989 29151657551323218500862937)
            ·
              refine ⟨21863743163492413875647203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29151657551323218500862937 21863743163492413875647203)
              ·
                refine ⟨32795614745238620813470805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21863743163492413875647203 32795614745238620813470805)
                ·
                  refine ⟨384323610295765087657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32795614745238620813470805 384323610295765087657861)
                  ·
                    rfl

theorem cell23_6736208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_6736208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736208 prefixEnd_6736208 := by exact prefixLift 6736208
  have htrace : WordTrace (prefixWord ++ tailWord_6736208) baseStart_6736208 baseEnd_6736208 := by
    simpa [prefixWord, tailWord_6736208, baseEnd_6736208] using wordTrace_append hprefix tailTrace_6736208
  have hstable : (prefixWord ++ tailWord_6736208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736208).length < 2 ^ (prefixWord ++ tailWord_6736208).sum := by decide
  have hdescent : baseEnd_6736208 < baseStart_6736208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736212 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_6736212 : Nat := 118140960795 + 6736212 * 2 ^ 59
def prefixEnd_6736212 : Nat := 4983230072969 + 3 ^ 40 * 6736212 * 2
def baseEnd_6736212 : Nat := 1152971515528167924423577

theorem tailTrace_6736212 : CollatzResearch.WordTrace tailWord_6736212 prefixEnd_6736212 1152971515528167924423577 := by
  unfold tailWord_6736212
  simp only [CollatzResearch.WordTrace]
  refine ⟨122844917935930926131217445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163793223914574568174956593 122844917935930926131217445)
  ·
    refine ⟨23033422112987048649603271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122844917935930926131217445 23033422112987048649603271)
    ·
      refine ⟨34550133169480572974404907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23033422112987048649603271 34550133169480572974404907)
      ·
        refine ⟨51825199754220859461607361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34550133169480572974404907 51825199754220859461607361)
        ·
          refine ⟨38868899815665644596205521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51825199754220859461607361 38868899815665644596205521)
          ·
            refine ⟨29151674861749233447154141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38868899815665644596205521 29151674861749233447154141)
            ·
              refine ⟨10931878073155962542682803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29151674861749233447154141 10931878073155962542682803)
              ·
                refine ⟨16397817109733943814024205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10931878073155962542682803 16397817109733943814024205)
                ·
                  refine ⟨6149181416150228930259077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16397817109733943814024205 6149181416150228930259077)
                  ·
                    refine ⟨1152971515528167924423577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149181416150228930259077 1152971515528167924423577)
                    ·
                      rfl

theorem cell23_6736212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_6736212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736212 prefixEnd_6736212 := by exact prefixLift 6736212
  have htrace : WordTrace (prefixWord ++ tailWord_6736212) baseStart_6736212 baseEnd_6736212 := by
    simpa [prefixWord, tailWord_6736212, baseEnd_6736212] using wordTrace_append hprefix tailTrace_6736212
  have hstable : (prefixWord ++ tailWord_6736212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736212).length < 2 ^ (prefixWord ++ tailWord_6736212).sum := by decide
  have hdescent : baseEnd_6736212 < baseStart_6736212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736286 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6736286 : Nat := 118140960795 + 6736286 * 2 ^ 59
def prefixEnd_6736286 : Nat := 4983230072969 + 3 ^ 40 * 6736286 * 2
def baseEnd_6736286 : Nat := 3458952544152936483745391

theorem tailTrace_6736286 : CollatzResearch.WordTrace tailWord_6736286 prefixEnd_6736286 3458952544152936483745391 := by
  unfold tailWord_6736286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30711566859199220362578589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163795023249062508600419141 30711566859199220362578589)
  ·
    refine ⟨11516837572199707635966971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30711566859199220362578589 11516837572199707635966971)
    ·
      refine ⟨17275256358299561453950457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11516837572199707635966971 17275256358299561453950457)
      ·
        refine ⟨12956442268724671090462843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17275256358299561453950457 12956442268724671090462843)
        ·
          refine ⟨19434663403087006635694265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12956442268724671090462843 19434663403087006635694265)
          ·
            refine ⟨14575997552315254976770699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19434663403087006635694265 14575997552315254976770699)
            ·
              refine ⟨21863996328472882465156049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575997552315254976770699 21863996328472882465156049)
              ·
                refine ⟨16397997246354661848867037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21863996328472882465156049 16397997246354661848867037)
                ·
                  refine ⟨6149248967382998193325139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16397997246354661848867037 6149248967382998193325139)
                  ·
                    refine ⟨9223873451074497289987709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149248967382998193325139 9223873451074497289987709)
                    ·
                      refine ⟨3458952544152936483745391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9223873451074497289987709 3458952544152936483745391)
                      ·
                        rfl

theorem cell23_6736286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6736286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736286 prefixEnd_6736286 := by exact prefixLift 6736286
  have htrace : WordTrace (prefixWord ++ tailWord_6736286) baseStart_6736286 baseEnd_6736286 := by
    simpa [prefixWord, tailWord_6736286, baseEnd_6736286] using wordTrace_append hprefix tailTrace_6736286
  have hstable : (prefixWord ++ tailWord_6736286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736286).length < 2 ^ (prefixWord ++ tailWord_6736286).sum := by decide
  have hdescent : baseEnd_6736286 < baseStart_6736286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736296 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6736296 : Nat := 118140960795 + 6736296 * 2 ^ 59
def prefixEnd_6736296 : Nat := 4983230072969 + 3 ^ 40 * 6736296 * 2
def baseEnd_6736296 : Nat := 3458957678959481444620345

theorem tailTrace_6736296 : CollatzResearch.WordTrace tailWord_6736296 prefixEnd_6736296 3458957678959481444620345 := by
  unfold tailWord_6736296
  simp only [CollatzResearch.WordTrace]
  refine ⟨122846449801778767304246371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163795266402371689738995161 122846449801778767304246371)
  ·
    refine ⟨184269674702668150956369557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122846449801778767304246371 184269674702668150956369557)
    ·
      refine ⟨8637641001687569576079823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184269674702668150956369557 8637641001687569576079823)
      ·
        refine ⟨12956461502531354364119735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8637641001687569576079823 12956461502531354364119735)
        ·
          refine ⟨19434692253797031546179603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12956461502531354364119735 19434692253797031546179603)
          ·
            refine ⟨29152038380695547319269405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19434692253797031546179603 29152038380695547319269405)
            ·
              refine ⟨10932014392760830244726027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29152038380695547319269405 10932014392760830244726027)
              ·
                refine ⟨16398021589141245367089041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932014392760830244726027 16398021589141245367089041)
                ·
                  refine ⟨12298516191855934025316781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16398021589141245367089041 12298516191855934025316781)
                  ·
                    refine ⟨4611943571945975259493793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12298516191855934025316781 4611943571945975259493793)
                    ·
                      refine ⟨3458957678959481444620345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611943571945975259493793 3458957678959481444620345)
                      ·
                        rfl

theorem cell23_6736296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6736296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736296 prefixEnd_6736296 := by exact prefixLift 6736296
  have htrace : WordTrace (prefixWord ++ tailWord_6736296) baseStart_6736296 baseEnd_6736296 := by
    simpa [prefixWord, tailWord_6736296, baseEnd_6736296] using wordTrace_append hprefix tailTrace_6736296
  have hstable : (prefixWord ++ tailWord_6736296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736296).length < 2 ^ (prefixWord ++ tailWord_6736296).sum := by decide
  have hdescent : baseEnd_6736296 < baseStart_6736296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736309 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_6736309 : Nat := 118140960795 + 6736309 * 2 ^ 59
def prefixEnd_6736309 : Nat := 4983230072969 + 3 ^ 40 * 6736309 * 2
def baseEnd_6736309 : Nat := 3458964354207989893757785

theorem tailTrace_6736309 : CollatzResearch.WordTrace tailWord_6736309 prefixEnd_6736309 3458964354207989893757785 := by
  unfold tailWord_6736309
  simp only [CollatzResearch.WordTrace]
  refine ⟨245693373752510437828715981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163795582501673625219143987 245693373752510437828715981)
  ·
    refine ⟨92135015157191414185768493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245693373752510437828715981 92135015157191414185768493)
    ·
      refine ⟨34550630683946780319663185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92135015157191414185768493 34550630683946780319663185)
      ·
        refine ⟨25912973012960085239747389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34550630683946780319663185 25912973012960085239747389)
        ·
          refine ⟨9717364879860031964905271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25912973012960085239747389 9717364879860031964905271)
          ·
            refine ⟨14576047319790047947357907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717364879860031964905271 14576047319790047947357907)
            ·
              refine ⟨21864070979685071921036861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576047319790047947357907 21864070979685071921036861)
              ·
                refine ⟨8199026617381901970388823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21864070979685071921036861 8199026617381901970388823)
                ·
                  refine ⟨12298539926072852955583235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199026617381901970388823 12298539926072852955583235)
                  ·
                    refine ⟨18447809889109279433374853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12298539926072852955583235 18447809889109279433374853)
                    ·
                      refine ⟨3458964354207989893757785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18447809889109279433374853 3458964354207989893757785)
                      ·
                        rfl

theorem cell23_6736309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_6736309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736309 prefixEnd_6736309 := by exact prefixLift 6736309
  have htrace : WordTrace (prefixWord ++ tailWord_6736309) baseStart_6736309 baseEnd_6736309 := by
    simpa [prefixWord, tailWord_6736309, baseEnd_6736309] using wordTrace_append hprefix tailTrace_6736309
  have hstable : (prefixWord ++ tailWord_6736309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736309).length < 2 ^ (prefixWord ++ tailWord_6736309).sum := by decide
  have hdescent : baseEnd_6736309 < baseStart_6736309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736369 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_6736369 : Nat := 118140960795 + 6736369 * 2 ^ 59
def prefixEnd_6736369 : Nat := 4983230072969 + 3 ^ 40 * 6736369 * 2
def baseEnd_6736369 : Nat := 3458995163047259659007509

theorem tailTrace_6736369 : CollatzResearch.WordTrace tailWord_6736369 prefixEnd_6736369 3458995163047259659007509 := by
  unfold tailWord_6736369
  simp only [CollatzResearch.WordTrace]
  refine ⟨245695562132293068075900161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163797041421528712050600107 245695562132293068075900161)
  ·
    refine ⟨184271671599219801056925121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245695562132293068075900161 184271671599219801056925121)
    ·
      refine ⟨138203753699414850792693841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184271671599219801056925121 138203753699414850792693841)
      ·
        refine ⟨103652815274561138094520381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138203753699414850792693841 103652815274561138094520381)
        ·
          refine ⟨38869805727960426785445143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103652815274561138094520381 38869805727960426785445143)
          ·
            refine ⟨58304708591940640178167715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38869805727960426785445143 58304708591940640178167715)
            ·
              refine ⟨87457062887910960267251573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58304708591940640178167715 87457062887910960267251573)
              ·
                refine ⟨8199099645741652525054835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87457062887910960267251573 8199099645741652525054835)
                ·
                  refine ⟨12298649468612478787582253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199099645741652525054835 12298649468612478787582253)
                  ·
                    refine ⟨4611993550729679545343345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12298649468612478787582253 4611993550729679545343345)
                    ·
                      refine ⟨3458995163047259659007509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4611993550729679545343345 3458995163047259659007509)
                      ·
                        rfl

theorem cell23_6736369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_6736369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736369 prefixEnd_6736369 := by exact prefixLift 6736369
  have htrace : WordTrace (prefixWord ++ tailWord_6736369) baseStart_6736369 baseEnd_6736369 := by
    simpa [prefixWord, tailWord_6736369, baseEnd_6736369] using wordTrace_append hprefix tailTrace_6736369
  have hstable : (prefixWord ++ tailWord_6736369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736369).length < 2 ^ (prefixWord ++ tailWord_6736369).sum := by decide
  have hdescent : baseEnd_6736369 < baseStart_6736369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736405 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 9]
def baseStart_6736405 : Nat := 118140960795 + 6736405 * 2 ^ 59
def prefixEnd_6736405 : Nat := 4983230072969 + 3 ^ 40 * 6736405 * 2
def baseEnd_6736405 : Nat := 384334849816757946461927

theorem tailTrace_6736405 : CollatzResearch.WordTrace tailWord_6736405 prefixEnd_6736405 384334849816757946461927 := by
  unfold tailWord_6736405
  simp only [CollatzResearch.WordTrace]
  refine ⟨245696875160162646224210669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163797916773441764149473779 245696875160162646224210669)
  ·
    refine ⟨92136328185060992334079001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245696875160162646224210669 92136328185060992334079001)
    ·
      refine ⟨69102246138795744250559251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92136328185060992334079001 69102246138795744250559251)
      ·
        refine ⟨103653369208193616375838877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69102246138795744250559251 103653369208193616375838877)
        ·
          refine ⟨38870013453072606140939579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103653369208193616375838877 38870013453072606140939579)
          ·
            refine ⟨58305020179608909211409369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38870013453072606140939579 58305020179608909211409369)
            ·
              refine ⟨43728765134706681908557027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58305020179608909211409369 43728765134706681908557027)
              ·
                refine ⟨65593147702060022862835541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43728765134706681908557027 65593147702060022862835541)
                ·
                  refine ⟨384334849816757946461927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65593147702060022862835541 384334849816757946461927)
                  ·
                    rfl

theorem cell23_6736405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_6736405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736405 prefixEnd_6736405 := by exact prefixLift 6736405
  have htrace : WordTrace (prefixWord ++ tailWord_6736405) baseStart_6736405 baseEnd_6736405 := by
    simpa [prefixWord, tailWord_6736405, baseEnd_6736405] using wordTrace_append hprefix tailTrace_6736405
  have hstable : (prefixWord ++ tailWord_6736405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736405).length < 2 ^ (prefixWord ++ tailWord_6736405).sum := by decide
  have hdescent : baseEnd_6736405 < baseStart_6736405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736416 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6736416 : Nat := 118140960795 + 6736416 * 2 ^ 59
def prefixEnd_6736416 : Nat := 4983230072969 + 3 ^ 40 * 6736416 * 2
def baseEnd_6736416 : Nat := 3459019296638020975119793

theorem tailTrace_6736416 : CollatzResearch.WordTrace tailWord_6736416 prefixEnd_6736416 3459019296638020975119793 := by
  unfold tailWord_6736416
  simp only [CollatzResearch.WordTrace]
  refine ⟨122848638181561397551430551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163798184242081863401907401 122848638181561397551430551)
  ·
    refine ⟨184272957272342096327145827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122848638181561397551430551 184272957272342096327145827)
    ·
      refine ⟨276409435908513144490718741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184272957272342096327145827 276409435908513144490718741)
      ·
        refine ⟨12956692308211553648002441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276409435908513144490718741 12956692308211553648002441)
        ·
          refine ⟨9717519231158665236001831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12956692308211553648002441 9717519231158665236001831)
          ·
            refine ⟨14576278846737997854002747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717519231158665236001831 14576278846737997854002747)
            ·
              refine ⟨21864418270106996781004121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576278846737997854002747 21864418270106996781004121)
              ·
                refine ⟨16398313702580247585753091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21864418270106996781004121 16398313702580247585753091)
                ·
                  refine ⟨24597470553870371378629637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16398313702580247585753091 24597470553870371378629637)
                  ·
                    refine ⟨4612025728850694633493057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24597470553870371378629637 4612025728850694633493057)
                    ·
                      refine ⟨3459019296638020975119793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612025728850694633493057 3459019296638020975119793)
                      ·
                        rfl

theorem cell23_6736416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6736416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736416 prefixEnd_6736416 := by exact prefixLift 6736416
  have htrace : WordTrace (prefixWord ++ tailWord_6736416) baseStart_6736416 baseEnd_6736416 := by
    simpa [prefixWord, tailWord_6736416, baseEnd_6736416] using wordTrace_append hprefix tailTrace_6736416
  have hstable : (prefixWord ++ tailWord_6736416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736416).length < 2 ^ (prefixWord ++ tailWord_6736416).sum := by decide
  have hdescent : baseEnd_6736416 < baseStart_6736416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736420 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6736420 : Nat := 118140960795 + 6736420 * 2 ^ 59
def prefixEnd_6736420 : Nat := 4983230072969 + 3 ^ 40 * 6736420 * 2
def baseEnd_6736420 : Nat := 3459021350560638959469775

theorem tailTrace_6736420 : CollatzResearch.WordTrace tailWord_6736420 prefixEnd_6736420 3459021350560638959469775 := by
  unfold tailWord_6736420
  simp only [CollatzResearch.WordTrace]
  refine ⟨122848711127554151893003357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163798281503405535857337809 122848711127554151893003357)
  ·
    refine ⟨46068266672832806959876259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122848711127554151893003357 46068266672832806959876259)
    ·
      refine ⟨69102400009249210439814389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46068266672832806959876259 69102400009249210439814389)
      ·
        refine ⟨6478350000867113478732599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69102400009249210439814389 6478350000867113478732599)
        ·
          refine ⟨9717525001300670218098899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478350000867113478732599 9717525001300670218098899)
          ·
            refine ⟨14576287501951005327148349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717525001300670218098899 14576287501951005327148349)
            ·
              refine ⟨5466107813231626997680631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14576287501951005327148349 5466107813231626997680631)
              ·
                refine ⟨8199161719847440496520947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466107813231626997680631 8199161719847440496520947)
                ·
                  refine ⟨12298742579771160744781421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199161719847440496520947 12298742579771160744781421)
                  ·
                    refine ⟨4612028467414185279293033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12298742579771160744781421 4612028467414185279293033)
                    ·
                      refine ⟨3459021350560638959469775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612028467414185279293033 3459021350560638959469775)
                      ·
                        rfl

theorem cell23_6736420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6736420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736420 prefixEnd_6736420 := by exact prefixLift 6736420
  have htrace : WordTrace (prefixWord ++ tailWord_6736420) baseStart_6736420 baseEnd_6736420 := by
    simpa [prefixWord, tailWord_6736420, baseEnd_6736420] using wordTrace_append hprefix tailTrace_6736420
  have hstable : (prefixWord ++ tailWord_6736420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736420).length < 2 ^ (prefixWord ++ tailWord_6736420).sum := by decide
  have hdescent : baseEnd_6736420 < baseStart_6736420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736446 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6736446 : Nat := 118140960795 + 6736446 * 2 ^ 59
def prefixEnd_6736446 : Nat := 4983230072969 + 3 ^ 40 * 6736446 * 2
def baseEnd_6736446 : Nat := 3459034701057655857744655

theorem tailTrace_6736446 : CollatzResearch.WordTrace tailWord_6736446 prefixEnd_6736446 3459034701057655857744655 := by
  unfold tailWord_6736446
  simp only [CollatzResearch.WordTrace]
  refine ⟨30712296319126763778306649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163798913702009406817635461 30712296319126763778306649)
  ·
    refine ⟨23034222239345072833729987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30712296319126763778306649 23034222239345072833729987)
    ·
      refine ⟨34551333359017609250594981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23034222239345072833729987 34551333359017609250594981)
      ·
        refine ⟨6478375004815801734486559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34551333359017609250594981 6478375004815801734486559)
        ·
          refine ⟨9717562507223702601729839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478375004815801734486559 9717562507223702601729839)
          ·
            refine ⟨14576343760835553902594759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717562507223702601729839 14576343760835553902594759)
            ·
              refine ⟨21864515641253330853892139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576343760835553902594759 21864515641253330853892139)
              ·
                refine ⟨32796773461879996280838209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21864515641253330853892139 32796773461879996280838209)
                ·
                  refine ⟨24597580096409997210628657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32796773461879996280838209 24597580096409997210628657)
                  ·
                    refine ⟨18448185072307497907971493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24597580096409997210628657 18448185072307497907971493)
                    ·
                      refine ⟨3459034701057655857744655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18448185072307497907971493 3459034701057655857744655)
                      ·
                        rfl

theorem cell23_6736446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6736446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736446 prefixEnd_6736446 := by exact prefixLift 6736446
  have htrace : WordTrace (prefixWord ++ tailWord_6736446) baseStart_6736446 baseEnd_6736446 := by
    simpa [prefixWord, tailWord_6736446, baseEnd_6736446] using wordTrace_append hprefix tailTrace_6736446
  have hstable : (prefixWord ++ tailWord_6736446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736446).length < 2 ^ (prefixWord ++ tailWord_6736446).sum := by decide
  have hdescent : baseEnd_6736446 < baseStart_6736446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736449 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6736449 : Nat := 118140960795 + 6736449 * 2 ^ 59
def prefixEnd_6736449 : Nat := 4983230072969 + 3 ^ 40 * 6736449 * 2
def baseEnd_6736449 : Nat := 3459036241499619346007141

theorem tailTrace_6736449 : CollatzResearch.WordTrace tailWord_6736449 prefixEnd_6736449 3459036241499619346007141 := by
  unfold tailWord_6736449
  simp only [CollatzResearch.WordTrace]
  refine ⟨245698479972003241738812401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163798986648002161159208267 245698479972003241738812401)
  ·
    refine ⟨184273859979002431304109301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245698479972003241738812401 184273859979002431304109301)
    ·
      refine ⟨17275674373031477934760247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184273859979002431304109301 17275674373031477934760247)
      ·
        refine ⟨25913511559547216902140371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17275674373031477934760247 25913511559547216902140371)
        ·
          refine ⟨38870267339320825353210557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25913511559547216902140371 38870267339320825353210557)
          ·
            refine ⟨14576350252245309507453959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38870267339320825353210557 14576350252245309507453959)
            ·
              refine ⟨21864525378367964261180939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576350252245309507453959 21864525378367964261180939)
              ·
                refine ⟨32796788067551946391771409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21864525378367964261180939 32796788067551946391771409)
                ·
                  refine ⟨24597591050663959793828557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32796788067551946391771409 24597591050663959793828557)
                  ·
                    refine ⟨9224096643998984922685709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24597591050663959793828557 9224096643998984922685709)
                    ·
                      refine ⟨3459036241499619346007141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224096643998984922685709 3459036241499619346007141)
                      ·
                        rfl

theorem cell23_6736449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6736449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736449 prefixEnd_6736449 := by exact prefixLift 6736449
  have htrace : WordTrace (prefixWord ++ tailWord_6736449) baseStart_6736449 baseEnd_6736449 := by
    simpa [prefixWord, tailWord_6736449, baseEnd_6736449] using wordTrace_append hprefix tailTrace_6736449
  have hstable : (prefixWord ++ tailWord_6736449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736449).length < 2 ^ (prefixWord ++ tailWord_6736449).sum := by decide
  have hdescent : baseEnd_6736449 < baseStart_6736449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736562 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_6736562 : Nat := 118140960795 + 6736562 * 2 ^ 59
def prefixEnd_6736562 : Nat := 4983230072969 + 3 ^ 40 * 6736562 * 2
def baseEnd_6736562 : Nat := 3459094264813577403894121

theorem tailTrace_6736562 : CollatzResearch.WordTrace tailWord_6736562 prefixEnd_6736562 3459094264813577403894121 := by
  unfold tailWord_6736562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61425650355148465509418985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163801734280395908025117293 61425650355148465509418985)
  ·
    refine ⟨46069237766361349132064239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61425650355148465509418985 46069237766361349132064239)
    ·
      refine ⟨69103856649542023698096359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46069237766361349132064239 69103856649542023698096359)
      ·
        refine ⟨103655784974313035547144539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69103856649542023698096359 103655784974313035547144539)
        ·
          refine ⟨155483677461469553320716809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103655784974313035547144539 155483677461469553320716809)
          ·
            refine ⟨116612758096102164990537607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155483677461469553320716809 116612758096102164990537607)
            ·
              refine ⟨174919137144153247485806411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116612758096102164990537607 174919137144153247485806411)
              ·
                refine ⟨262378705716229871228709617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174919137144153247485806411 262378705716229871228709617)
                ·
                  refine ⟨196784029287172403421532213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262378705716229871228709617 196784029287172403421532213)
                  ·
                    refine ⟨18448502745672412820768645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196784029287172403421532213 18448502745672412820768645)
                    ·
                      refine ⟨3459094264813577403894121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18448502745672412820768645 3459094264813577403894121)
                      ·
                        rfl

theorem cell23_6736562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_6736562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736562 prefixEnd_6736562 := by exact prefixLift 6736562
  have htrace : WordTrace (prefixWord ++ tailWord_6736562) baseStart_6736562 baseEnd_6736562 := by
    simpa [prefixWord, tailWord_6736562, baseEnd_6736562] using wordTrace_append hprefix tailTrace_6736562
  have hstable : (prefixWord ++ tailWord_6736562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736562).length < 2 ^ (prefixWord ++ tailWord_6736562).sum := by decide
  have hdescent : baseEnd_6736562 < baseStart_6736562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736576 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_6736576 : Nat := 118140960795 + 6736576 * 2 ^ 59
def prefixEnd_6736576 : Nat := 4983230072969 + 3 ^ 40 * 6736576 * 2
def baseEnd_6736576 : Nat := 1153033817847580116373019

theorem tailTrace_6736576 : CollatzResearch.WordTrace tailWord_6736576 prefixEnd_6736576 1153033817847580116373019 := by
  unfold tailWord_6736576
  simp only [CollatzResearch.WordTrace]
  refine ⟨122851556021271571214342791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163802074695028761619123721 122851556021271571214342791)
  ·
    refine ⟨184277334031907356821514187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122851556021271571214342791 184277334031907356821514187)
    ·
      refine ⟨276416001047861035232271281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184277334031907356821514187 276416001047861035232271281)
      ·
        refine ⟨207312000785895776424203461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276416001047861035232271281 207312000785895776424203461)
        ·
          refine ⟨38871000147355458079538149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207312000785895776424203461 38871000147355458079538149)
          ·
            refine ⟨7288312527629148389913403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38871000147355458079538149 7288312527629148389913403)
            ·
              refine ⟨10932468791443722584870105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288312527629148389913403 10932468791443722584870105)
              ·
                refine ⟨8199351593582791938652579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10932468791443722584870105 8199351593582791938652579)
                ·
                  refine ⟨12299027390374187907978869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199351593582791938652579 12299027390374187907978869)
                  ·
                    refine ⟨1153033817847580116373019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299027390374187907978869 1153033817847580116373019)
                    ·
                      rfl

theorem cell23_6736576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_6736576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736576 prefixEnd_6736576 := by exact prefixLift 6736576
  have htrace : WordTrace (prefixWord ++ tailWord_6736576) baseStart_6736576 baseEnd_6736576 := by
    simpa [prefixWord, tailWord_6736576, baseEnd_6736576] using wordTrace_append hprefix tailTrace_6736576
  have hstable : (prefixWord ++ tailWord_6736576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736576).length < 2 ^ (prefixWord ++ tailWord_6736576).sum := by decide
  have hdescent : baseEnd_6736576 < baseStart_6736576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736599 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_6736599 : Nat := 118140960795 + 6736599 * 2 ^ 59
def prefixEnd_6736599 : Nat := 4983230072969 + 3 ^ 40 * 6736599 * 2
def baseEnd_6736599 : Nat := 3459113263597793759131451

theorem tailTrace_6736599 : CollatzResearch.WordTrace tailWord_6736599 prefixEnd_6736599 3459113263597793759131451 := by
  unfold tailWord_6736599
  simp only [CollatzResearch.WordTrace]
  refine ⟨245703950921459817356772851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163802633947639878237848567 245703950921459817356772851)
  ·
    refine ⟨368555926382189726035159277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245703950921459817356772851 368555926382189726035159277)
    ·
      refine ⟨138208472393321147263184729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368555926382189726035159277 138208472393321147263184729)
      ·
        refine ⟨103656354294990860447388547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138208472393321147263184729 103656354294990860447388547)
        ·
          refine ⟨155484531442486290671082821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103656354294990860447388547 155484531442486290671082821)
          ·
            refine ⟨29153349645466179500828029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155484531442486290671082821 29153349645466179500828029)
            ·
              refine ⟨10932506117049817312810511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29153349645466179500828029 10932506117049817312810511)
              ·
                refine ⟨16398759175574725969215767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932506117049817312810511 16398759175574725969215767)
                ·
                  refine ⟨24598138763362088953823651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16398759175574725969215767 24598138763362088953823651)
                  ·
                    refine ⟨36897208145043133430735477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24598138763362088953823651 36897208145043133430735477)
                    ·
                      refine ⟨3459113263597793759131451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36897208145043133430735477 3459113263597793759131451)
                      ·
                        rfl

theorem cell23_6736599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_6736599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736599 prefixEnd_6736599 := by exact prefixLift 6736599
  have htrace : WordTrace (prefixWord ++ tailWord_6736599) baseStart_6736599 baseEnd_6736599 := by
    simpa [prefixWord, tailWord_6736599, baseEnd_6736599] using wordTrace_append hprefix tailTrace_6736599
  have hstable : (prefixWord ++ tailWord_6736599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736599).length < 2 ^ (prefixWord ++ tailWord_6736599).sum := by decide
  have hdescent : baseEnd_6736599 < baseStart_6736599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736626 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6736626 : Nat := 118140960795 + 6736626 * 2 ^ 59
def prefixEnd_6736626 : Nat := 4983230072969 + 3 ^ 40 * 6736626 * 2
def baseEnd_6736626 : Nat := 3459127127575465153493827

theorem tailTrace_6736626 : CollatzResearch.WordTrace tailWord_6736626 prefixEnd_6736626 3459127127575465153493827 := by
  unfold tailWord_6736626
  simp only [CollatzResearch.WordTrace]
  refine ⟨61426233923090500242001433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163803290461574667312003821 61426233923090500242001433)
  ·
    refine ⟨46069675442317875181501075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61426233923090500242001433 46069675442317875181501075)
    ·
      refine ⟨69104513163476812772251613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46069675442317875181501075 69104513163476812772251613)
      ·
        refine ⟨25914192436303804789594355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69104513163476812772251613 25914192436303804789594355)
        ·
          refine ⟨38871288654455707184391533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25914192436303804789594355 38871288654455707184391533)
          ·
            refine ⟨14576733245420890194146825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38871288654455707184391533 14576733245420890194146825)
            ·
              refine ⟨10932549934065667645610119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14576733245420890194146825 10932549934065667645610119)
              ·
                refine ⟨16398824901098501468415179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932549934065667645610119 16398824901098501468415179)
                ·
                  refine ⟨24598237351647752202622769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16398824901098501468415179 24598237351647752202622769)
                  ·
                    refine ⟨18448678013735814151967077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24598237351647752202622769 18448678013735814151967077)
                    ·
                      refine ⟨3459127127575465153493827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18448678013735814151967077 3459127127575465153493827)
                      ·
                        rfl

theorem cell23_6736626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6736626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736626 prefixEnd_6736626 := by exact prefixLift 6736626
  have htrace : WordTrace (prefixWord ++ tailWord_6736626) baseStart_6736626 baseEnd_6736626 := by
    simpa [prefixWord, tailWord_6736626, baseEnd_6736626] using wordTrace_append hprefix tailTrace_6736626
  have hstable : (prefixWord ++ tailWord_6736626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736626).length < 2 ^ (prefixWord ++ tailWord_6736626).sum := by decide
  have hdescent : baseEnd_6736626 < baseStart_6736626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736632 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_6736632 : Nat := 118140960795 + 6736632 * 2 ^ 59
def prefixEnd_6736632 : Nat := 4983230072969 + 3 ^ 40 * 6736632 * 2
def baseEnd_6736632 : Nat := 1153043402819797376672933

theorem tailTrace_6736632 : CollatzResearch.WordTrace tailWord_6736632 prefixEnd_6736632 1153043402819797376672933 := by
  unfold tailWord_6736632
  simp only [CollatzResearch.WordTrace]
  refine ⟨122852577265170131996362075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163803436353560175995149433 122852577265170131996362075)
  ·
    refine ⟨184278865897755197994543113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122852577265170131996362075 184278865897755197994543113)
    ·
      refine ⟨138209149423316398495907335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184278865897755197994543113 138209149423316398495907335)
      ·
        refine ⟨207313724134974597743861003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138209149423316398495907335 207313724134974597743861003)
        ·
          refine ⟨310970586202461896615791505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207313724134974597743861003 310970586202461896615791505)
          ·
            refine ⟨233227939651846422461843629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310970586202461896615791505 233227939651846422461843629)
            ·
              refine ⟨87460477369442408423191361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233227939651846422461843629 87460477369442408423191361)
              ·
                refine ⟨65595358027081806317393521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87460477369442408423191361 65595358027081806317393521)
                ·
                  refine ⟨49196518520311354738045141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65595358027081806317393521 49196518520311354738045141)
                  ·
                    refine ⟨1153043402819797376672933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49196518520311354738045141 1153043402819797376672933)
                    ·
                      rfl

theorem cell23_6736632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_6736632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736632 prefixEnd_6736632 := by exact prefixLift 6736632
  have htrace : WordTrace (prefixWord ++ tailWord_6736632) baseStart_6736632 baseEnd_6736632 := by
    simpa [prefixWord, tailWord_6736632, baseEnd_6736632] using wordTrace_append hprefix tailTrace_6736632
  have hstable : (prefixWord ++ tailWord_6736632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736632).length < 2 ^ (prefixWord ++ tailWord_6736632).sum := by decide
  have hdescent : baseEnd_6736632 < baseStart_6736632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736647 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6736647 : Nat := 118140960795 + 6736647 * 2 ^ 59
def prefixEnd_6736647 : Nat := 4983230072969 + 3 ^ 40 * 6736647 * 2
def baseEnd_6736647 : Nat := 3459137910669209571331231

theorem tailTrace_6736647 : CollatzResearch.WordTrace tailWord_6736647 prefixEnd_6736647 3459137910669209571331231 := by
  unfold tailWord_6736647
  simp only [CollatzResearch.WordTrace]
  refine ⟨245705701625285921554520195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163803801083523947703013463 245705701625285921554520195)
  ·
    refine ⟨368558552437928882331780293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245705701625285921554520195 368558552437928882331780293)
    ·
      refine ⟨69104728582111665437208805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368558552437928882331780293 69104728582111665437208805)
      ·
        refine ⟨12957136609145937269476651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69104728582111665437208805 12957136609145937269476651)
        ·
          refine ⟨19435704913718905904214977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957136609145937269476651 19435704913718905904214977)
          ·
            refine ⟨14576778685289179428161233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19435704913718905904214977 14576778685289179428161233)
            ·
              refine ⟨10932584013966884571120925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14576778685289179428161233 10932584013966884571120925)
              ·
                refine ⟨4099719005237581714170347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10932584013966884571120925 4099719005237581714170347)
                ·
                  refine ⟨6149578507856372571255521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099719005237581714170347 6149578507856372571255521)
                  ·
                    refine ⟨4612183880892279428441641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149578507856372571255521 4612183880892279428441641)
                    ·
                      refine ⟨3459137910669209571331231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612183880892279428441641 3459137910669209571331231)
                      ·
                        rfl

theorem cell23_6736647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6736647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736647 prefixEnd_6736647 := by exact prefixLift 6736647
  have htrace : WordTrace (prefixWord ++ tailWord_6736647) baseStart_6736647 baseEnd_6736647 := by
    simpa [prefixWord, tailWord_6736647, baseEnd_6736647] using wordTrace_append hprefix tailTrace_6736647
  have hstable : (prefixWord ++ tailWord_6736647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736647).length < 2 ^ (prefixWord ++ tailWord_6736647).sum := by decide
  have hdescent : baseEnd_6736647 < baseStart_6736647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736663 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6736663 : Nat := 118140960795 + 6736663 * 2 ^ 59
def prefixEnd_6736663 : Nat := 4983230072969 + 3 ^ 40 * 6736663 * 2
def baseEnd_6736663 : Nat := 3459146126359681508731157

theorem tailTrace_6736663 : CollatzResearch.WordTrace tailWord_6736663 prefixEnd_6736663 3459146126359681508731157 := by
  unfold tailWord_6736663
  simp only [CollatzResearch.WordTrace]
  refine ⟨245706285193227956287102643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163804190128818637524735095 245706285193227956287102643)
  ·
    refine ⟨368559427789841934430653965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245706285193227956287102643 368559427789841934430653965)
    ·
      refine ⟨138209785421190725411495237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368559427789841934430653965 138209785421190725411495237)
      ·
        refine ⟨25914334766473261014655357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138209785421190725411495237 25914334766473261014655357)
        ·
          refine ⟨9717875537427472880495759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25914334766473261014655357 9717875537427472880495759)
          ·
            refine ⟨14576813306141209320743639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717875537427472880495759 14576813306141209320743639)
            ·
              refine ⟨21865219959211813981115459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576813306141209320743639 21865219959211813981115459)
              ·
                refine ⟨32797829938817720971673189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21865219959211813981115459 32797829938817720971673189)
                ·
                  refine ⟨6149593113528322682188723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32797829938817720971673189 6149593113528322682188723)
                  ·
                    refine ⟨9224389670292484023283085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149593113528322682188723 9224389670292484023283085)
                    ·
                      refine ⟨3459146126359681508731157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224389670292484023283085 3459146126359681508731157)
                      ·
                        rfl

theorem cell23_6736663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6736663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736663 prefixEnd_6736663 := by exact prefixLift 6736663
  have htrace : WordTrace (prefixWord ++ tailWord_6736663) baseStart_6736663 baseEnd_6736663 := by
    simpa [prefixWord, tailWord_6736663, baseEnd_6736663] using wordTrace_append hprefix tailTrace_6736663
  have hstable : (prefixWord ++ tailWord_6736663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736663).length < 2 ^ (prefixWord ++ tailWord_6736663).sum := by decide
  have hdescent : baseEnd_6736663 < baseStart_6736663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736680 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_6736680 : Nat := 118140960795 + 6736680 * 2 ^ 59
def prefixEnd_6736680 : Nat := 4983230072969 + 3 ^ 40 * 6736680 * 2
def baseEnd_6736680 : Nat := 3459154855530807942218579

theorem tailTrace_6736680 : CollatzResearch.WordTrace tailWord_6736680 prefixEnd_6736680 3459154855530807942218579 := by
  unfold tailWord_6736680
  simp only [CollatzResearch.WordTrace]
  refine ⟨122853452617083184095235747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163804603489444245460314329 122853452617083184095235747)
  ·
    refine ⟨184280178925624776142853621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122853452617083184095235747 184280178925624776142853621)
    ·
      refine ⟨17276266774277322763392527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184280178925624776142853621 17276266774277322763392527)
      ·
        refine ⟨25914400161415984145088791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276266774277322763392527 25914400161415984145088791)
        ·
          refine ⟨38871600242123976217633187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25914400161415984145088791 38871600242123976217633187)
          ·
            refine ⟨58307400363185964326449781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38871600242123976217633187 58307400363185964326449781)
            ·
              refine ⟨5466318784048684155604667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58307400363185964326449781 5466318784048684155604667)
              ·
                refine ⟨8199478176073026233407001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466318784048684155604667 8199478176073026233407001)
                ·
                  refine ⟨6149608632054769675055251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8199478176073026233407001 6149608632054769675055251)
                  ·
                    refine ⟨9224412948082154512582877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149608632054769675055251 9224412948082154512582877)
                    ·
                      refine ⟨3459154855530807942218579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224412948082154512582877 3459154855530807942218579)
                      ·
                        rfl

theorem cell23_6736680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_6736680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736680 prefixEnd_6736680 := by exact prefixLift 6736680
  have htrace : WordTrace (prefixWord ++ tailWord_6736680) baseStart_6736680 baseEnd_6736680 := by
    simpa [prefixWord, tailWord_6736680, baseEnd_6736680] using wordTrace_append hprefix tailTrace_6736680
  have hstable : (prefixWord ++ tailWord_6736680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736680).length < 2 ^ (prefixWord ++ tailWord_6736680).sum := by decide
  have hdescent : baseEnd_6736680 < baseStart_6736680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736689 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6736689 : Nat := 118140960795 + 6736689 * 2 ^ 59
def prefixEnd_6736689 : Nat := 4983230072969 + 3 ^ 40 * 6736689 * 2
def baseEnd_6736689 : Nat := 3459159476856698407006037

theorem tailTrace_6736689 : CollatzResearch.WordTrace tailWord_6736689 prefixEnd_6736689 3459159476856698407006037 := by
  unfold tailWord_6736689
  simp only [CollatzResearch.WordTrace]
  refine ⟨245707233491133762727549121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163804822327422508485032747 245707233491133762727549121)
  ·
    refine ⟨184280425118350322045661841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245707233491133762727549121 184280425118350322045661841)
    ·
      refine ⟨138210318838762741534246381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184280425118350322045661841 138210318838762741534246381)
      ·
        refine ⟨51828869564536028075342393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138210318838762741534246381 51828869564536028075342393)
        ·
          refine ⟨38871652173402021056506795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51828869564536028075342393 38871652173402021056506795)
          ·
            refine ⟨58307478260103031584760193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38871652173402021056506795 58307478260103031584760193)
            ·
              refine ⟨43730608695077273688570145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58307478260103031584760193 43730608695077273688570145)
              ·
                refine ⟨32797956521307955266427609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43730608695077273688570145 32797956521307955266427609)
                ·
                  refine ⟨24598467390980966449820707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32797956521307955266427609 24598467390980966449820707)
                  ·
                    refine ⟨36897701086471449674731061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24598467390980966449820707 36897701086471449674731061)
                    ·
                      refine ⟨3459159476856698407006037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36897701086471449674731061 3459159476856698407006037)
                      ·
                        rfl

theorem cell23_6736689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6736689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736689 prefixEnd_6736689 := by exact prefixLift 6736689
  have htrace : WordTrace (prefixWord ++ tailWord_6736689) baseStart_6736689 baseEnd_6736689 := by
    simpa [prefixWord, tailWord_6736689, baseEnd_6736689] using wordTrace_append hprefix tailTrace_6736689
  have hstable : (prefixWord ++ tailWord_6736689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736689).length < 2 ^ (prefixWord ++ tailWord_6736689).sum := by decide
  have hdescent : baseEnd_6736689 < baseStart_6736689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736703 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 4, 2, 2]
def baseStart_6736703 : Nat := 118140960795 + 6736703 * 2 ^ 59
def prefixEnd_6736703 : Nat := 4983230072969 + 3 ^ 40 * 6736703 * 2
def baseEnd_6736703 : Nat := 3459166665585861352230973

theorem tailTrace_6736703 : CollatzResearch.WordTrace tailWord_6736703 prefixEnd_6736703 3459166665585861352230973 := by
  unfold tailWord_6736703
  simp only [CollatzResearch.WordTrace]
  refine ⟨245707744113083043118558763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163805162742055362079039175 245707744113083043118558763)
  ·
    refine ⟨368561616169624564677838145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245707744113083043118558763 368561616169624564677838145)
    ·
      refine ⟨276421212127218423508378609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368561616169624564677838145 276421212127218423508378609)
      ·
        refine ⟨207315909095413817631283957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276421212127218423508378609 207315909095413817631283957)
        ·
          refine ⟨19435866477695045402932871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207315909095413817631283957 19435866477695045402932871)
          ·
            refine ⟨29153799716542568104399307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19435866477695045402932871 29153799716542568104399307)
            ·
              refine ⟨43730699574813852156598961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29153799716542568104399307 43730699574813852156598961)
              ·
                refine ⟨32798024681110389117449221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43730699574813852156598961 32798024681110389117449221)
                ·
                  refine ⟨6149629627708197959521729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32798024681110389117449221 6149629627708197959521729)
                  ·
                    refine ⟨4612222220781148469641297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149629627708197959521729 4612222220781148469641297)
                    ·
                      refine ⟨3459166665585861352230973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612222220781148469641297 3459166665585861352230973)
                      ·
                        rfl

theorem cell23_6736703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_6736703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736703 prefixEnd_6736703 := by exact prefixLift 6736703
  have htrace : WordTrace (prefixWord ++ tailWord_6736703) baseStart_6736703 baseEnd_6736703 := by
    simpa [prefixWord, tailWord_6736703, baseEnd_6736703] using wordTrace_append hprefix tailTrace_6736703
  have hstable : (prefixWord ++ tailWord_6736703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736703).length < 2 ^ (prefixWord ++ tailWord_6736703).sum := by decide
  have hdescent : baseEnd_6736703 < baseStart_6736703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736749 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6736749 : Nat := 118140960795 + 6736749 * 2 ^ 59
def prefixEnd_6736749 : Nat := 4983230072969 + 3 ^ 40 * 6736749 * 2
def baseEnd_6736749 : Nat := 3459190285695968172255761

theorem tailTrace_6736749 : CollatzResearch.WordTrace tailWord_6736749 prefixEnd_6736749 3459190285695968172255761 := by
  unfold tailWord_6736749
  simp only [CollatzResearch.WordTrace]
  refine ⟨245709421870916392974733301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163806281247277595316488867 245709421870916392974733301)
  ·
    refine ⟨23035258300398411841381247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245709421870916392974733301 23035258300398411841381247)
    ·
      refine ⟨34552887450597617762071871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23035258300398411841381247 34552887450597617762071871)
      ·
        refine ⟨51829331175896426643107807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34552887450597617762071871 51829331175896426643107807)
        ·
          refine ⟨77743996763844639964661711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51829331175896426643107807 77743996763844639964661711)
          ·
            refine ⟨116615995145766959946992567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77743996763844639964661711 116615995145766959946992567)
            ·
              refine ⟨174923992718650439920488851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116615995145766959946992567 174923992718650439920488851)
              ·
                refine ⟨262385989077975659880733277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174923992718650439920488851 262385989077975659880733277)
                ·
                  refine ⟨98394745904240872455274979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262385989077975659880733277 98394745904240872455274979)
                  ·
                    refine ⟨147592118856361308682912469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98394745904240872455274979 147592118856361308682912469)
                    ·
                      refine ⟨3459190285695968172255761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147592118856361308682912469 3459190285695968172255761)
                      ·
                        rfl

theorem cell23_6736749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6736749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736749 prefixEnd_6736749 := by exact prefixLift 6736749
  have htrace : WordTrace (prefixWord ++ tailWord_6736749) baseStart_6736749 baseEnd_6736749 := by
    simpa [prefixWord, tailWord_6736749, baseEnd_6736749] using wordTrace_append hprefix tailTrace_6736749
  have hstable : (prefixWord ++ tailWord_6736749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736749).length < 2 ^ (prefixWord ++ tailWord_6736749).sum := by decide
  have hdescent : baseEnd_6736749 < baseStart_6736749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736759 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_6736759 : Nat := 118140960795 + 6736759 * 2 ^ 59
def prefixEnd_6736759 : Nat := 4983230072969 + 3 ^ 40 * 6736759 * 2
def baseEnd_6736759 : Nat := 3459195420502513133130715

theorem tailTrace_6736759 : CollatzResearch.WordTrace tailWord_6736759 prefixEnd_6736759 3459195420502513133130715 := by
  unfold tailWord_6736759
  simp only [CollatzResearch.WordTrace]
  refine ⟨245709786600880164682597331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163806524400586776455064887 245709786600880164682597331)
  ·
    refine ⟨368564679901320247023895997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245709786600880164682597331 368564679901320247023895997)
    ·
      refine ⟨138211754962995092633960999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368564679901320247023895997 138211754962995092633960999)
      ·
        refine ⟨207317632444492638950941499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138211754962995092633960999 207317632444492638950941499)
        ·
          refine ⟨310976448666738958426412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207317632444492638950941499 310976448666738958426412249)
          ·
            refine ⟨233232336500054218819809187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310976448666738958426412249 233232336500054218819809187)
            ·
              refine ⟨349848504750081328229713781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233232336500054218819809187 349848504750081328229713781)
              ·
                refine ⟨32798297320320124521535667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349848504750081328229713781 32798297320320124521535667)
                ·
                  refine ⟨49197445980480186782303501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32798297320320124521535667 49197445980480186782303501)
                  ·
                    refine ⟨18449042242680070043363813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49197445980480186782303501 18449042242680070043363813)
                    ·
                      refine ⟨3459195420502513133130715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18449042242680070043363813 3459195420502513133130715)
                      ·
                        rfl

theorem cell23_6736759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_6736759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736759 prefixEnd_6736759 := by exact prefixLift 6736759
  have htrace : WordTrace (prefixWord ++ tailWord_6736759) baseStart_6736759 baseEnd_6736759 := by
    simpa [prefixWord, tailWord_6736759, baseEnd_6736759] using wordTrace_append hprefix tailTrace_6736759
  have hstable : (prefixWord ++ tailWord_6736759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736759).length < 2 ^ (prefixWord ++ tailWord_6736759).sum := by decide
  have hdescent : baseEnd_6736759 < baseStart_6736759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736843 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 3]
def baseStart_6736843 : Nat := 118140960795 + 6736843 * 2 ^ 59
def prefixEnd_6736843 : Nat := 4983230072969 + 3 ^ 40 * 6736843 * 2
def baseEnd_6736843 : Nat := 3459238552877490804480329

theorem tailTrace_6736843 : CollatzResearch.WordTrace tailWord_6736843 prefixEnd_6736843 3459238552877490804480329 := by
  unfold tailWord_6736843
  simp only [CollatzResearch.WordTrace]
  refine ⟨245712850332575847028655183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163808566888383898019103455 245712850332575847028655183)
  ·
    refine ⟨368569275498863770542982775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245712850332575847028655183 368569275498863770542982775)
    ·
      refine ⟨552853913248295655814474163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368569275498863770542982775 552853913248295655814474163)
      ·
        refine ⟨829280869872443483721711245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552853913248295655814474163 829280869872443483721711245)
        ·
          refine ⟨310980326202166306395641717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 829280869872443483721711245 310980326202166306395641717)
          ·
            refine ⟨29154405581453091224591411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310980326202166306395641717 29154405581453091224591411)
            ·
              refine ⟨43731608372179636836887117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29154405581453091224591411 43731608372179636836887117)
              ·
                refine ⟨16399353139567363813832669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43731608372179636836887117 16399353139567363813832669)
                ·
                  refine ⟨6149757427337761430187251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16399353139567363813832669 6149757427337761430187251)
                  ·
                    refine ⟨9224636141006642145280877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149757427337761430187251 9224636141006642145280877)
                    ·
                      refine ⟨3459238552877490804480329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224636141006642145280877 3459238552877490804480329)
                      ·
                        rfl

theorem cell23_6736843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 3].length) (baseStart_6736843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736843 prefixEnd_6736843 := by exact prefixLift 6736843
  have htrace : WordTrace (prefixWord ++ tailWord_6736843) baseStart_6736843 baseEnd_6736843 := by
    simpa [prefixWord, tailWord_6736843, baseEnd_6736843] using wordTrace_append hprefix tailTrace_6736843
  have hstable : (prefixWord ++ tailWord_6736843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736843).length < 2 ^ (prefixWord ++ tailWord_6736843).sum := by decide
  have hdescent : baseEnd_6736843 < baseStart_6736843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736850 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_6736850 : Nat := 118140960795 + 6736850 * 2 ^ 59
def prefixEnd_6736850 : Nat := 4983230072969 + 3 ^ 40 * 6736850 * 2
def baseEnd_6736850 : Nat := 384360238582452475232533

theorem tailTrace_6736850 : CollatzResearch.WordTrace tailWord_6736850 prefixEnd_6736850 384360238582452475232533 := by
  unfold tailWord_6736850
  simp only [CollatzResearch.WordTrace]
  refine ⟨61428276410887621806040001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163808737095700324816106669 61428276410887621806040001)
  ·
    refine ⟨46071207308165716354530001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61428276410887621806040001 46071207308165716354530001)
    ·
      refine ⟨34553405481124287265897501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46071207308165716354530001 34553405481124287265897501)
      ·
        refine ⟨12957527055421607724711563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34553405481124287265897501 12957527055421607724711563)
        ·
          refine ⟨19436290583132411587067345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957527055421607724711563 19436290583132411587067345)
          ·
            refine ⟨14577217937349308690300509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19436290583132411587067345 14577217937349308690300509)
            ·
              refine ⟨5466456726505990758862691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14577217937349308690300509 5466456726505990758862691)
              ·
                refine ⟨8199685089758986138294037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466456726505990758862691 8199685089758986138294037)
                ·
                  refine ⟨384360238582452475232533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8199685089758986138294037 384360238582452475232533)
                  ·
                    rfl

theorem cell23_6736850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_6736850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736850 prefixEnd_6736850 := by exact prefixLift 6736850
  have htrace : WordTrace (prefixWord ++ tailWord_6736850) baseStart_6736850 baseEnd_6736850 := by
    simpa [prefixWord, tailWord_6736850, baseEnd_6736850] using wordTrace_append hprefix tailTrace_6736850
  have hstable : (prefixWord ++ tailWord_6736850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736850).length < 2 ^ (prefixWord ++ tailWord_6736850).sum := by decide
  have hdescent : baseEnd_6736850 < baseStart_6736850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736893 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6736893 : Nat := 118140960795 + 6736893 * 2 ^ 59
def prefixEnd_6736893 : Nat := 4983230072969 + 3 ^ 40 * 6736893 * 2
def baseEnd_6736893 : Nat := 1153088075636738536285033

theorem tailTrace_6736893 : CollatzResearch.WordTrace tailWord_6736893 prefixEnd_6736893 1153088075636738536285033 := by
  unfold tailWord_6736893
  simp only [CollatzResearch.WordTrace]
  refine ⟨245714673982394705567975333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163809782654929803711983555 245714673982394705567975333)
  ·
    refine ⟨46071501371699007293995375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245714673982394705567975333 46071501371699007293995375)
    ·
      refine ⟨69107252057548510940993063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46071501371699007293995375 69107252057548510940993063)
      ·
        refine ⟨103660878086322766411489595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69107252057548510940993063 103660878086322766411489595)
        ·
          refine ⟨155491317129484149617234393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103660878086322766411489595 155491317129484149617234393)
          ·
            refine ⟨116618487847113112212925795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155491317129484149617234393 116618487847113112212925795)
            ·
              refine ⟨174927731770669668319388693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116618487847113112212925795 174927731770669668319388693)
              ·
                refine ⟨8199737426750140702471345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174927731770669668319388693 8199737426750140702471345)
                ·
                  refine ⟨6149803070062605526853509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8199737426750140702471345 6149803070062605526853509)
                  ·
                    refine ⟨1153088075636738536285033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149803070062605526853509 1153088075636738536285033)
                    ·
                      rfl

theorem cell23_6736893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6736893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736893 prefixEnd_6736893 := by exact prefixLift 6736893
  have htrace : WordTrace (prefixWord ++ tailWord_6736893) baseStart_6736893 baseEnd_6736893 := by
    simpa [prefixWord, tailWord_6736893, baseEnd_6736893] using wordTrace_append hprefix tailTrace_6736893
  have hstable : (prefixWord ++ tailWord_6736893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736893).length < 2 ^ (prefixWord ++ tailWord_6736893).sum := by decide
  have hdescent : baseEnd_6736893 < baseStart_6736893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736894 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6736894 : Nat := 118140960795 + 6736894 * 2 ^ 59
def prefixEnd_6736894 : Nat := 4983230072969 + 3 ^ 40 * 6736894 * 2
def baseEnd_6736894 : Nat := 3459264740390870104942595

theorem tailTrace_6736894 : CollatzResearch.WordTrace tailWord_6736894 prefixEnd_6736894 3459264740390870104942595 := by
  unfold tailWord_6736894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714338806923885342345217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163809806970260721825841157 30714338806923885342345217)
  ·
    refine ⟨23035754105192914006758913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30714338806923885342345217 23035754105192914006758913)
    ·
      refine ⟨17276815578894685505069185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23035754105192914006758913 17276815578894685505069185)
      ·
        refine ⟨12957611684171014128801889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17276815578894685505069185 12957611684171014128801889)
        ·
          refine ⟨9718208763128260596601417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12957611684171014128801889 9718208763128260596601417)
          ·
            refine ⟨7288656572346195447451063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718208763128260596601417 7288656572346195447451063)
            ·
              refine ⟨10932984858519293171176595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288656572346195447451063 10932984858519293171176595)
              ·
                refine ⟨16399477287778939756764893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932984858519293171176595 16399477287778939756764893)
                ·
                  refine ⟨6149803982917102408786835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16399477287778939756764893 6149803982917102408786835)
                  ·
                    refine ⟨9224705974375653613180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149803982917102408786835 9224705974375653613180253)
                    ·
                      refine ⟨3459264740390870104942595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224705974375653613180253 3459264740390870104942595)
                      ·
                        rfl

theorem cell23_6736894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6736894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736894 prefixEnd_6736894 := by exact prefixLift 6736894
  have htrace : WordTrace (prefixWord ++ tailWord_6736894) baseStart_6736894 baseEnd_6736894 := by
    simpa [prefixWord, tailWord_6736894, baseEnd_6736894] using wordTrace_append hprefix tailTrace_6736894
  have hstable : (prefixWord ++ tailWord_6736894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736894).length < 2 ^ (prefixWord ++ tailWord_6736894).sum := by decide
  have hdescent : baseEnd_6736894 < baseStart_6736894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736903 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6736903 : Nat := 118140960795 + 6736903 * 2 ^ 59
def prefixEnd_6736903 : Nat := 4983230072969 + 3 ^ 40 * 6736903 * 2
def baseEnd_6736903 : Nat := 3459269361716760569730053

theorem tailTrace_6736903 : CollatzResearch.WordTrace tailWord_6736903 prefixEnd_6736903 3459269361716760569730053 := by
  unfold tailWord_6736903
  simp only [CollatzResearch.WordTrace]
  refine ⟨245715038712358477275839363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163810025808238984850559575 245715038712358477275839363)
  ·
    refine ⟨368572558068537715913759045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245715038712358477275839363 368572558068537715913759045)
    ·
      refine ⟨69107354637850821733829821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 368572558068537715913759045 69107354637850821733829821)
      ·
        refine ⟨25915257989194058150186183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69107354637850821733829821 25915257989194058150186183)
        ·
          refine ⟨38872886983791087225279275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25915257989194058150186183 38872886983791087225279275)
          ·
            refine ⟨58309330475686630837918913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38872886983791087225279275 58309330475686630837918913)
            ·
              refine ⟨43731997856764973128439185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58309330475686630837918913 43731997856764973128439185)
              ·
                refine ⟨32798998392573729846329389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43731997856764973128439185 32798998392573729846329389)
                ·
                  refine ⟨12299624397215148692373521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32798998392573729846329389 12299624397215148692373521)
                  ·
                    refine ⟨9224718297911361519280141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12299624397215148692373521 9224718297911361519280141)
                    ·
                      refine ⟨3459269361716760569730053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224718297911361519280141 3459269361716760569730053)
                      ·
                        rfl

theorem cell23_6736903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6736903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736903 prefixEnd_6736903 := by exact prefixLift 6736903
  have htrace : WordTrace (prefixWord ++ tailWord_6736903) baseStart_6736903 baseEnd_6736903 := by
    simpa [prefixWord, tailWord_6736903, baseEnd_6736903] using wordTrace_append hprefix tailTrace_6736903
  have hstable : (prefixWord ++ tailWord_6736903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736903).length < 2 ^ (prefixWord ++ tailWord_6736903).sum := by decide
  have hdescent : baseEnd_6736903 < baseStart_6736903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736906 : List Nat := [3, 1, 2, 2, 3, 1, 1, 10]
def baseStart_6736906 : Nat := 118140960795 + 6736906 * 2 ^ 59
def prefixEnd_6736906 : Nat := 4983230072969 + 3 ^ 40 * 6736906 * 2
def baseEnd_6736906 : Nat := 128121144524397187333057

theorem tailTrace_6736906 : CollatzResearch.WordTrace tailWord_6736906 prefixEnd_6736906 128121144524397187333057 := by
  unfold tailWord_6736906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61428787032836902197049643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163810098754231739192132381 61428787032836902197049643)
  ·
    refine ⟨92143180549255353295574465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61428787032836902197049643 92143180549255353295574465)
    ·
      refine ⟨69107385411941514971680849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92143180549255353295574465 69107385411941514971680849)
      ·
        refine ⟨51830539058956136228760637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69107385411941514971680849 51830539058956136228760637)
        ·
          refine ⟨19436452147108551085785239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51830539058956136228760637 19436452147108551085785239)
          ·
            refine ⟨29154678220662826628677859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19436452147108551085785239 29154678220662826628677859)
            ·
              refine ⟨43732017330994239943016789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29154678220662826628677859 43732017330994239943016789)
              ·
                refine ⟨128121144524397187333057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43732017330994239943016789 128121144524397187333057)
                ·
                  rfl

theorem cell23_6736906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_6736906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736906 prefixEnd_6736906 := by exact prefixLift 6736906
  have htrace : WordTrace (prefixWord ++ tailWord_6736906) baseStart_6736906 baseEnd_6736906 := by
    simpa [prefixWord, tailWord_6736906, baseEnd_6736906] using wordTrace_append hprefix tailTrace_6736906
  have hstable : (prefixWord ++ tailWord_6736906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736906).length < 2 ^ (prefixWord ++ tailWord_6736906).sum := by decide
  have hdescent : baseEnd_6736906 < baseStart_6736906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736910 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_6736910 : Nat := 118140960795 + 6736910 * 2 ^ 59
def prefixEnd_6736910 : Nat := 4983230072969 + 3 ^ 40 * 6736910 * 2
def baseEnd_6736910 : Nat := 1153090985360447347447507

theorem tailTrace_6736910 : CollatzResearch.WordTrace tailWord_6736910 prefixEnd_6736910 1153090985360447347447507 := by
  unfold tailWord_6736910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714411752916639683918023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163810196015555411647562789 30714411752916639683918023)
  ·
    refine ⟨46071617629374959525877035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30714411752916639683918023 46071617629374959525877035)
    ·
      refine ⟨69107426444062439288815553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46071617629374959525877035 69107426444062439288815553)
      ·
        refine ⟨51830569833046829466611665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69107426444062439288815553 51830569833046829466611665)
        ·
          refine ⟨38872927374785122099958749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51830569833046829466611665 38872927374785122099958749)
          ·
            refine ⟨14577347765544420787484531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38872927374785122099958749 14577347765544420787484531)
            ·
              refine ⟨21866021648316631181226797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14577347765544420787484531 21866021648316631181226797)
              ·
                refine ⟨8199758118118736692960049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21866021648316631181226797 8199758118118736692960049)
                ·
                  refine ⟨6149818588589052519720037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8199758118118736692960049 6149818588589052519720037)
                  ·
                    refine ⟨1153090985360447347447507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6149818588589052519720037 1153090985360447347447507)
                    ·
                      rfl

theorem cell23_6736910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_6736910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736910 prefixEnd_6736910 := by exact prefixLift 6736910
  have htrace : WordTrace (prefixWord ++ tailWord_6736910) baseStart_6736910 baseEnd_6736910 := by
    simpa [prefixWord, tailWord_6736910, baseEnd_6736910] using wordTrace_append hprefix tailTrace_6736910
  have hstable : (prefixWord ++ tailWord_6736910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736910).length < 2 ^ (prefixWord ++ tailWord_6736910).sum := by decide
  have hdescent : baseEnd_6736910 < baseStart_6736910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736920 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_6736920 : Nat := 118140960795 + 6736920 * 2 ^ 59
def prefixEnd_6736920 : Nat := 4983230072969 + 3 ^ 40 * 6736920 * 2
def baseEnd_6736920 : Nat := 3459278090887887003217475

theorem tailTrace_6736920 : CollatzResearch.WordTrace tailWord_6736920 prefixEnd_6736920 3459278090887887003217475 := by
  unfold tailWord_6736920
  simp only [CollatzResearch.WordTrace]
  refine ⟨122857829376648444589604107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163810439168864592786138809 122857829376648444589604107)
  ·
    refine ⟨184286744064972666884406161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122857829376648444589604107 184286744064972666884406161)
    ·
      refine ⟨138215058048729500163304621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184286744064972666884406161 138215058048729500163304621)
      ·
        refine ⟨51830646768273562561239233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138215058048729500163304621 51830646768273562561239233)
        ·
          refine ⟨38872985076205171920929425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51830646768273562561239233 38872985076205171920929425)
          ·
            refine ⟨29154738807153878940697069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38872985076205171920929425 29154738807153878940697069)
            ·
              refine ⟨10933027052682704602761401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29154738807153878940697069 10933027052682704602761401)
              ·
                refine ⟨8199770289512028452071051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10933027052682704602761401 8199770289512028452071051)
                ·
                  refine ⟨12299655434268042678106577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199770289512028452071051 12299655434268042678106577)
                  ·
                    refine ⟨9224741575701032008579933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12299655434268042678106577 9224741575701032008579933)
                    ·
                      refine ⟨3459278090887887003217475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224741575701032008579933 3459278090887887003217475)
                      ·
                        rfl

theorem cell23_6736920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_6736920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736920 prefixEnd_6736920 := by exact prefixLift 6736920
  have htrace : WordTrace (prefixWord ++ tailWord_6736920) baseStart_6736920 baseEnd_6736920 := by
    simpa [prefixWord, tailWord_6736920, baseEnd_6736920] using wordTrace_append hprefix tailTrace_6736920
  have hstable : (prefixWord ++ tailWord_6736920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736920).length < 2 ^ (prefixWord ++ tailWord_6736920).sum := by decide
  have hdescent : baseEnd_6736920 < baseStart_6736920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736933 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_6736933 : Nat := 118140960795 + 6736933 * 2 ^ 59
def prefixEnd_6736933 : Nat := 4983230072969 + 3 ^ 40 * 6736933 * 2
def baseEnd_6736933 : Nat := 3459284766136395452354915

theorem tailTrace_6736933 : CollatzResearch.WordTrace tailWord_6736933 prefixEnd_6736933 3459284766136395452354915 := by
  unfold tailWord_6736933
  simp only [CollatzResearch.WordTrace]
  refine ⟨245716132902249792399431453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163810755268166528266287635 245716132902249792399431453)
  ·
    refine ⟨92143549838343672149786795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245716132902249792399431453 92143549838343672149786795)
    ·
      refine ⟨138215324757515508224680193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92143549838343672149786795 138215324757515508224680193)
      ·
        refine ⟨103661493568136631168510145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138215324757515508224680193 103661493568136631168510145)
        ·
          refine ⟨77746120176102473376382609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103661493568136631168510145 77746120176102473376382609)
          ·
            refine ⟨58309590132076855032286957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77746120176102473376382609 58309590132076855032286957)
            ·
              refine ⟨21866096299528820637107609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58309590132076855032286957 21866096299528820637107609)
              ·
                refine ⟨16399572224646615477830707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21866096299528820637107609 16399572224646615477830707)
                ·
                  refine ⟨24599358336969923216746061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16399572224646615477830707 24599358336969923216746061)
                  ·
                    refine ⟨9224759376363721206279773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24599358336969923216746061 9224759376363721206279773)
                    ·
                      refine ⟨3459284766136395452354915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224759376363721206279773 3459284766136395452354915)
                      ·
                        rfl

theorem cell23_6736933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_6736933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736933 prefixEnd_6736933 := by exact prefixLift 6736933
  have htrace : WordTrace (prefixWord ++ tailWord_6736933) baseStart_6736933 baseEnd_6736933 := by
    simpa [prefixWord, tailWord_6736933, baseEnd_6736933] using wordTrace_append hprefix tailTrace_6736933
  have hstable : (prefixWord ++ tailWord_6736933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736933).length < 2 ^ (prefixWord ++ tailWord_6736933).sum := by decide
  have hdescent : baseEnd_6736933 < baseStart_6736933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736976 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_6736976 : Nat := 118140960795 + 6736976 * 2 ^ 59
def prefixEnd_6736976 : Nat := 4983230072969 + 3 ^ 40 * 6736976 * 2
def baseEnd_6736976 : Nat := 3459306845804538784117217

theorem tailTrace_6736976 : CollatzResearch.WordTrace tailWord_6736976 prefixEnd_6736976 3459306845804538784117217 := by
  unfold tailWord_6736976
  simp only [CollatzResearch.WordTrace]
  refine ⟨122858850620547005371623391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163811800827396007162164521 122858850620547005371623391)
  ·
    refine ⟨184288275930820508057435087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122858850620547005371623391 184288275930820508057435087)
    ·
      refine ⟨276432413896230762086152631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184288275930820508057435087 276432413896230762086152631)
      ·
        refine ⟨414648620844346143129228947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276432413896230762086152631 414648620844346143129228947)
        ·
          refine ⟨621972931266519214693843421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414648620844346143129228947 621972931266519214693843421)
          ·
            refine ⟨233239849224944705510191283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621972931266519214693843421 233239849224944705510191283)
            ·
              refine ⟨349859773837417058265286925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233239849224944705510191283 349859773837417058265286925)
              ·
                refine ⟨131197415189031396849482597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349859773837417058265286925 131197415189031396849482597)
                ·
                  refine ⟨24599515347943386909277987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131197415189031396849482597 24599515347943386909277987)
                  ·
                    refine ⟨36899273021915080363916981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24599515347943386909277987 36899273021915080363916981)
                    ·
                      refine ⟨3459306845804538784117217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36899273021915080363916981 3459306845804538784117217)
                      ·
                        rfl

theorem cell23_6736976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_6736976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736976 prefixEnd_6736976 := by exact prefixLift 6736976
  have htrace : WordTrace (prefixWord ++ tailWord_6736976) baseStart_6736976 baseEnd_6736976 := by
    simpa [prefixWord, tailWord_6736976, baseEnd_6736976] using wordTrace_append hprefix tailTrace_6736976
  have hstable : (prefixWord ++ tailWord_6736976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736976).length < 2 ^ (prefixWord ++ tailWord_6736976).sum := by decide
  have hdescent : baseEnd_6736976 < baseStart_6736976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736994 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6736994 : Nat := 118140960795 + 6736994 * 2 ^ 59
def prefixEnd_6736994 : Nat := 4983230072969 + 3 ^ 40 * 6736994 * 2
def baseEnd_6736994 : Nat := 3459316088456319713692135

theorem tailTrace_6736994 : CollatzResearch.WordTrace tailWord_6736994 prefixEnd_6736994 3459316088456319713692135 := by
  unfold tailWord_6736994
  simp only [CollatzResearch.WordTrace]
  refine ⟨61429589438757199954350509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163812238503352533211601357 61429589438757199954350509)
  ·
    refine ⟨23036096039533949982881441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61429589438757199954350509 23036096039533949982881441)
    ·
      refine ⟨17277072029650462487161081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23036096039533949982881441 17277072029650462487161081)
      ·
        refine ⟨12957804022237846865370811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17277072029650462487161081 12957804022237846865370811)
        ·
          refine ⟨19436706033356770298056217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957804022237846865370811 19436706033356770298056217)
          ·
            refine ⟨14577529525017577723542163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19436706033356770298056217 14577529525017577723542163)
            ·
              refine ⟨21866294287526366585313245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14577529525017577723542163 21866294287526366585313245)
              ·
                refine ⟨8199860357822387469492467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21866294287526366585313245 8199860357822387469492467)
                ·
                  refine ⟨12299790536733581204238701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199860357822387469492467 12299790536733581204238701)
                  ·
                    refine ⟨4612421451275092951589513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12299790536733581204238701 4612421451275092951589513)
                    ·
                      refine ⟨3459316088456319713692135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612421451275092951589513 3459316088456319713692135)
                      ·
                        rfl

theorem cell23_6736994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6736994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736994 prefixEnd_6736994 := by exact prefixLift 6736994
  have htrace : WordTrace (prefixWord ++ tailWord_6736994) baseStart_6736994 baseEnd_6736994 := by
    simpa [prefixWord, tailWord_6736994, baseEnd_6736994] using wordTrace_append hprefix tailTrace_6736994
  have hstable : (prefixWord ++ tailWord_6736994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736994).length < 2 ^ (prefixWord ++ tailWord_6736994).sum := by decide
  have hdescent : baseEnd_6736994 < baseStart_6736994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6736996 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 11]
def baseStart_6736996 : Nat := 118140960795 + 6736996 * 2 ^ 59
def prefixEnd_6736996 : Nat := 4983230072969 + 3 ^ 40 * 6736996 * 2
def baseEnd_6736996 : Nat := 384368568379736522874125

theorem tailTrace_6736996 : CollatzResearch.WordTrace tailWord_6736996 prefixEnd_6736996 384368568379736522874125 := by
  unfold tailWord_6736996
  simp only [CollatzResearch.WordTrace]
  refine ⟨122859215350510777079487421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163812287134014369439316561 122859215350510777079487421)
  ·
    refine ⟨46072205756441541404807783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122859215350510777079487421 46072205756441541404807783)
    ·
      refine ⟨69108308634662312107211675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46072205756441541404807783 69108308634662312107211675)
      ·
        refine ⟨103662462951993468160817513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69108308634662312107211675 103662462951993468160817513)
        ·
          refine ⟨77746847213995101120613135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103662462951993468160817513 77746847213995101120613135)
          ·
            refine ⟨116620270820992651680919703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77746847213995101120613135 116620270820992651680919703)
            ·
              refine ⟨174930406231488977521379555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116620270820992651680919703 174930406231488977521379555)
              ·
                refine ⟨262395609347233466282069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174930406231488977521379555 262395609347233466282069333)
                ·
                  refine ⟨384368568379736522874125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 262395609347233466282069333 384368568379736522874125)
                  ·
                    rfl

theorem cell23_6736996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_6736996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6736996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6736996 prefixEnd_6736996 := by exact prefixLift 6736996
  have htrace : WordTrace (prefixWord ++ tailWord_6736996) baseStart_6736996 baseEnd_6736996 := by
    simpa [prefixWord, tailWord_6736996, baseEnd_6736996] using wordTrace_append hprefix tailTrace_6736996
  have hstable : (prefixWord ++ tailWord_6736996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6736996).length < 2 ^ (prefixWord ++ tailWord_6736996).sum := by decide
  have hdescent : baseEnd_6736996 < baseStart_6736996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6736996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737047 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 5]
def baseStart_6737047 : Nat := 118140960795 + 6737047 * 2 ^ 59
def prefixEnd_6737047 : Nat := 4983230072969 + 3 ^ 40 * 6737047 * 2
def baseEnd_6737047 : Nat := 384371478103445334036599

theorem tailTrace_6737047 : CollatzResearch.WordTrace tailWord_6737047 prefixEnd_6737047 384371478103445334036599 := by
  unfold tailWord_6737047
  simp only [CollatzResearch.WordTrace]
  refine ⟨245720290823836789869081395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163813527215891193246054263 245720290823836789869081395)
  ·
    refine ⟨368580436235755184803622093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245720290823836789869081395 368580436235755184803622093)
    ·
      refine ⟨138217663588408194301358285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368580436235755184803622093 138217663588408194301358285)
      ·
        refine ⟨51831623845653072863009357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138217663588408194301358285 51831623845653072863009357)
        ·
          refine ⟨19436858942119902323628509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51831623845653072863009357 19436858942119902323628509)
          ·
            refine ⟨7288822103294963371360691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19436858942119902323628509 7288822103294963371360691)
            ·
              refine ⟨10933233154942445057041037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288822103294963371360691 10933233154942445057041037)
              ·
                refine ⟨4099962433103416896390389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10933233154942445057041037 4099962433103416896390389)
                ·
                  refine ⟨384371478103445334036599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4099962433103416896390389 384371478103445334036599)
                  ·
                    rfl

theorem cell23_6737047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 5].length) (baseStart_6737047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737047 prefixEnd_6737047 := by exact prefixLift 6737047
  have htrace : WordTrace (prefixWord ++ tailWord_6737047) baseStart_6737047 baseEnd_6737047 := by
    simpa [prefixWord, tailWord_6737047, baseEnd_6737047] using wordTrace_append hprefix tailTrace_6737047
  have hstable : (prefixWord ++ tailWord_6737047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737047).length < 2 ^ (prefixWord ++ tailWord_6737047).sum := by decide
  have hdescent : baseEnd_6737047 < baseStart_6737047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737053 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6737053 : Nat := 118140960795 + 6737053 * 2 ^ 59
def prefixEnd_6737053 : Nat := 4983230072969 + 3 ^ 40 * 6737053 * 2
def baseEnd_6737053 : Nat := 3459346383814934982854363

theorem tailTrace_6737053 : CollatzResearch.WordTrace tailWord_6737053 prefixEnd_6737053 3459346383814934982854363 := by
  unfold tailWord_6737053
  simp only [CollatzResearch.WordTrace]
  refine ⟨245720509661815052893799813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163813673107876701929199875 245720509661815052893799813)
  ·
    refine ⟨46072595561590322417587465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245720509661815052893799813 46072595561590322417587465)
    ·
      refine ⟨34554446671192741813190599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46072595561590322417587465 34554446671192741813190599)
      ·
        refine ⟨51831670006789112719785899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34554446671192741813190599 51831670006789112719785899)
        ·
          refine ⟨77747505010183669079678849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51831670006789112719785899 77747505010183669079678849)
          ·
            refine ⟨58310628757637751809759137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77747505010183669079678849 58310628757637751809759137)
            ·
              refine ⟨43732971568228313857319353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58310628757637751809759137 43732971568228313857319353)
              ·
                refine ⟨32799728676171235392989515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43732971568228313857319353 32799728676171235392989515)
                ·
                  refine ⟨49199593014256853089484273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32799728676171235392989515 49199593014256853089484273)
                  ·
                    refine ⟨36899694760692639817113205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49199593014256853089484273 36899694760692639817113205)
                    ·
                      refine ⟨3459346383814934982854363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36899694760692639817113205 3459346383814934982854363)
                      ·
                        rfl

theorem cell23_6737053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6737053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737053 prefixEnd_6737053 := by exact prefixLift 6737053
  have htrace : WordTrace (prefixWord ++ tailWord_6737053) baseStart_6737053 baseEnd_6737053 := by
    simpa [prefixWord, tailWord_6737053, baseEnd_6737053] using wordTrace_append hprefix tailTrace_6737053
  have hstable : (prefixWord ++ tailWord_6737053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737053).length < 2 ^ (prefixWord ++ tailWord_6737053).sum := by decide
  have hdescent : baseEnd_6737053 < baseStart_6737053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737060 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_6737060 : Nat := 118140960795 + 6737060 * 2 ^ 59
def prefixEnd_6737060 : Nat := 4983230072969 + 3 ^ 40 * 6737060 * 2
def baseEnd_6737060 : Nat := 1153116659393172151822277

theorem tailTrace_6737060 : CollatzResearch.WordTrace tailWord_6737060 prefixEnd_6737060 1153116659393172151822277 := by
  unfold tailWord_6737060
  simp only [CollatzResearch.WordTrace]
  refine ⟨122860382486394846544652317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163813843315193128726203089 122860382486394846544652317)
  ·
    refine ⟨46072643432398067454244619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122860382486394846544652317 46072643432398067454244619)
    ·
      refine ⟨69108965148597101181366929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46072643432398067454244619 69108965148597101181366929)
      ·
        refine ⟨51831723861447825886025197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69108965148597101181366929 51831723861447825886025197)
        ·
          refine ⟨19436896448042934707259449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51831723861447825886025197 19436896448042934707259449)
          ·
            refine ⟨14577672336032201030444587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19436896448042934707259449 14577672336032201030444587)
            ·
              refine ⟨21866508504048301545666881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14577672336032201030444587 21866508504048301545666881)
              ·
                refine ⟨16399881378036226159250161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21866508504048301545666881 16399881378036226159250161)
                ·
                  refine ⟨12299911033527169619437621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16399881378036226159250161 12299911033527169619437621)
                  ·
                    refine ⟨1153116659393172151822277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12299911033527169619437621 1153116659393172151822277)
                    ·
                      rfl

theorem cell23_6737060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_6737060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737060 prefixEnd_6737060 := by exact prefixLift 6737060
  have htrace : WordTrace (prefixWord ++ tailWord_6737060) baseStart_6737060 baseEnd_6737060 := by
    simpa [prefixWord, tailWord_6737060, baseEnd_6737060] using wordTrace_append hprefix tailTrace_6737060
  have hstable : (prefixWord ++ tailWord_6737060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737060).length < 2 ^ (prefixWord ++ tailWord_6737060).sum := by decide
  have hdescent : baseEnd_6737060 < baseStart_6737060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737083 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3]
def baseStart_6737083 : Nat := 118140960795 + 6737083 * 2 ^ 59
def prefixEnd_6737083 : Nat := 4983230072969 + 3 ^ 40 * 6737083 * 2
def baseEnd_6737083 : Nat := 3459361788234569865479225

theorem tailTrace_6737083 : CollatzResearch.WordTrace tailWord_6737083 prefixEnd_6737083 3459361788234569865479225 := by
  unfold tailWord_6737083
  simp only [CollatzResearch.WordTrace]
  refine ⟨245721603851706368017391903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163814402567804245344927935 245721603851706368017391903)
  ·
    refine ⟨368582405777559552026087855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245721603851706368017391903 368582405777559552026087855)
    ·
      refine ⟨552873608666339328039131783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368582405777559552026087855 552873608666339328039131783)
      ·
        refine ⟨829310412999508992058697675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552873608666339328039131783 829310412999508992058697675)
        ·
          refine ⟨1243965619499263488088046513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829310412999508992058697675 1243965619499263488088046513)
          ·
            refine ⟨932974214624447616066034885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243965619499263488088046513 932974214624447616066034885)
            ·
              refine ⟨174932665242083928012381541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 932974214624447616066034885 174932665242083928012381541)
              ·
                refine ⟨32799874732890736502321539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174932665242083928012381541 32799874732890736502321539)
                ·
                  refine ⟨49199812099336104753482309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32799874732890736502321539 49199812099336104753482309)
                  ·
                    refine ⟨9224964768625519641277933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49199812099336104753482309 9224964768625519641277933)
                    ·
                      refine ⟨3459361788234569865479225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9224964768625519641277933 3459361788234569865479225)
                      ·
                        rfl

theorem cell23_6737083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 3].length) (baseStart_6737083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737083 prefixEnd_6737083 := by exact prefixLift 6737083
  have htrace : WordTrace (prefixWord ++ tailWord_6737083) baseStart_6737083 baseEnd_6737083 := by
    simpa [prefixWord, tailWord_6737083, baseEnd_6737083] using wordTrace_append hprefix tailTrace_6737083
  have hstable : (prefixWord ++ tailWord_6737083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737083).length < 2 ^ (prefixWord ++ tailWord_6737083).sum := by decide
  have hdescent : baseEnd_6737083 < baseStart_6737083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737120 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 6]
def baseStart_6737120 : Nat := 118140960795 + 6737120 * 2 ^ 59
def prefixEnd_6737120 : Nat := 4983230072969 + 3 ^ 40 * 6737120 * 2
def baseEnd_6737120 : Nat := 384375643002087357857395

theorem tailTrace_6737120 : CollatzResearch.WordTrace tailWord_6737120 prefixEnd_6737120 384375643002087357857395 := by
  unfold tailWord_6737120
  simp only [CollatzResearch.WordTrace]
  refine ⟨122861476676286161668244407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163815302235048215557659209 122861476676286161668244407)
  ·
    refine ⟨184292215014429242502366611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122861476676286161668244407 184292215014429242502366611)
    ·
      refine ⟨276438322521643863753549917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184292215014429242502366611 276438322521643863753549917)
      ·
        refine ⟨103664370945616448907581219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276438322521643863753549917 103664370945616448907581219)
        ·
          refine ⟨155496556418424673361371829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103664370945616448907581219 155496556418424673361371829)
          ·
            refine ⟨14577802164227313127628609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155496556418424673361371829 14577802164227313127628609)
            ·
              refine ⟨10933351623170484845721457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14577802164227313127628609 10933351623170484845721457)
              ·
                refine ⟨8200013717377863634291093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10933351623170484845721457 8200013717377863634291093)
                ·
                  refine ⟨384375643002087357857395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8200013717377863634291093 384375643002087357857395)
                  ·
                    rfl

theorem cell23_6737120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_6737120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737120 prefixEnd_6737120 := by exact prefixLift 6737120
  have htrace : WordTrace (prefixWord ++ tailWord_6737120) baseStart_6737120 baseEnd_6737120 := by
    simpa [prefixWord, tailWord_6737120, baseEnd_6737120] using wordTrace_append hprefix tailTrace_6737120
  have hstable : (prefixWord ++ tailWord_6737120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737120).length < 2 ^ (prefixWord ++ tailWord_6737120).sum := by decide
  have hdescent : baseEnd_6737120 < baseStart_6737120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737124 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_6737124 : Nat := 118140960795 + 6737124 * 2 ^ 59
def prefixEnd_6737124 : Nat := 4983230072969 + 3 ^ 40 * 6737124 * 2
def baseEnd_6737124 : Nat := 1153127613647134735022179

theorem tailTrace_6737124 : CollatzResearch.WordTrace tailWord_6737124 prefixEnd_6737124 1153127613647134735022179 := by
  unfold tailWord_6737124
  simp only [CollatzResearch.WordTrace]
  refine ⟨122861549622278916009817213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163815399496371888013089617 122861549622278916009817213)
  ·
    refine ⟨46073081108354593503681455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122861549622278916009817213 46073081108354593503681455)
    ·
      refine ⟨69109621662531890255522183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46073081108354593503681455 69109621662531890255522183)
      ·
        refine ⟨103664432493797835383283275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69109621662531890255522183 103664432493797835383283275)
        ·
          refine ⟨155496648740696753074924913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103664432493797835383283275 155496648740696753074924913)
          ·
            refine ⟨116622486555522564806193685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155496648740696753074924913 116622486555522564806193685)
            ·
              refine ⟨5466679057290120225290329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116622486555522564806193685 5466679057290120225290329)
              ·
                refine ⟨4100009292967590168967747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466679057290120225290329 4100009292967590168967747)
                ·
                  refine ⟨6150013939451385253451621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100009292967590168967747 6150013939451385253451621)
                  ·
                    refine ⟨1153127613647134735022179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150013939451385253451621 1153127613647134735022179)
                    ·
                      rfl

theorem cell23_6737124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_6737124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737124 prefixEnd_6737124 := by exact prefixLift 6737124
  have htrace : WordTrace (prefixWord ++ tailWord_6737124) baseStart_6737124 baseEnd_6737124 := by
    simpa [prefixWord, tailWord_6737124, baseEnd_6737124] using wordTrace_append hprefix tailTrace_6737124
  have hstable : (prefixWord ++ tailWord_6737124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737124).length < 2 ^ (prefixWord ++ tailWord_6737124).sum := by decide
  have hdescent : baseEnd_6737124 < baseStart_6737124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737164 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_6737164 : Nat := 118140960795 + 6737164 * 2 ^ 59
def prefixEnd_6737164 : Nat := 4983230072969 + 3 ^ 40 * 6737164 * 2
def baseEnd_6737164 : Nat := 3459403380167584048566353

theorem tailTrace_6737164 : CollatzResearch.WordTrace tailWord_6737164 prefixEnd_6737164 3459403380167584048566353 := by
  unfold tailWord_6737164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122862279082206459425545273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163816372109608612567393697 122862279082206459425545273)
  ·
    refine ⟨92146709311654844569158955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122862279082206459425545273 92146709311654844569158955)
    ·
      refine ⟨138220063967482266853738433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92146709311654844569158955 138220063967482266853738433)
      ·
        refine ⟨103665047975611700140303825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138220063967482266853738433 103665047975611700140303825)
        ·
          refine ⟨77748785981708775105227869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103665047975611700140303825 77748785981708775105227869)
          ·
            refine ⟨29155794743140790664460451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77748785981708775105227869 29155794743140790664460451)
            ·
              refine ⟨43733692114711185996690677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29155794743140790664460451 43733692114711185996690677)
              ·
                refine ⟨4100033635754173687189751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43733692114711185996690677 4100033635754173687189751)
                ·
                  refine ⟨6150050453631260530784627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100033635754173687189751 6150050453631260530784627)
                  ·
                    refine ⟨9225075680446890796176941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150050453631260530784627 9225075680446890796176941)
                    ·
                      refine ⟨3459403380167584048566353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225075680446890796176941 3459403380167584048566353)
                      ·
                        rfl

theorem cell23_6737164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_6737164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737164 prefixEnd_6737164 := by exact prefixLift 6737164
  have htrace : WordTrace (prefixWord ++ tailWord_6737164) baseStart_6737164 baseEnd_6737164 := by
    simpa [prefixWord, tailWord_6737164, baseEnd_6737164] using wordTrace_append hprefix tailTrace_6737164
  have hstable : (prefixWord ++ tailWord_6737164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737164).length < 2 ^ (prefixWord ++ tailWord_6737164).sum := by decide
  have hdescent : baseEnd_6737164 < baseStart_6737164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737181 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6737181 : Nat := 118140960795 + 6737181 * 2 ^ 59
def prefixEnd_6737181 : Nat := 4983230072969 + 3 ^ 40 * 6737181 * 2
def baseEnd_6737181 : Nat := 3459412109338710482053775

theorem tailTrace_6737181 : CollatzResearch.WordTrace tailWord_6737181 prefixEnd_6737181 3459412109338710482053775 := by
  unfold tailWord_6737181
  simp only [CollatzResearch.WordTrace]
  refine ⟨245725178205351330754459397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163816785470234220502972931 245725178205351330754459397)
  ·
    refine ⟨46073470913503374516461137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245725178205351330754459397 46073470913503374516461137)
    ·
      refine ⟨34555103185127530887345853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46073470913503374516461137 34555103185127530887345853)
      ·
        refine ⟨12958163694422824082754695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34555103185127530887345853 12958163694422824082754695)
        ·
          refine ⟨19437245541634236124132043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958163694422824082754695 19437245541634236124132043)
          ·
            refine ⟨29155868312451354186198065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19437245541634236124132043 29155868312451354186198065)
            ·
              refine ⟨21866901234338515639648549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29155868312451354186198065 21866901234338515639648549)
              ·
                refine ⟨4100043981438471682434103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21866901234338515639648549 4100043981438471682434103)
                ·
                  refine ⟨6150065972157707523651155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100043981438471682434103 6150065972157707523651155)
                  ·
                    refine ⟨9225098958236561285476733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150065972157707523651155 9225098958236561285476733)
                    ·
                      refine ⟨3459412109338710482053775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225098958236561285476733 3459412109338710482053775)
                      ·
                        rfl

theorem cell23_6737181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6737181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737181 prefixEnd_6737181 := by exact prefixLift 6737181
  have htrace : WordTrace (prefixWord ++ tailWord_6737181) baseStart_6737181 baseEnd_6737181 := by
    simpa [prefixWord, tailWord_6737181, baseEnd_6737181] using wordTrace_append hprefix tailTrace_6737181
  have hstable : (prefixWord ++ tailWord_6737181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737181).length < 2 ^ (prefixWord ++ tailWord_6737181).sum := by decide
  have hdescent : baseEnd_6737181 < baseStart_6737181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737204 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_6737204 : Nat := 118140960795 + 6737204 * 2 ^ 59
def prefixEnd_6737204 : Nat := 4983230072969 + 3 ^ 40 * 6737204 * 2
def baseEnd_6737204 : Nat := 3459423919393763892066169

theorem tailTrace_6737204 : CollatzResearch.WordTrace tailWord_6737204 prefixEnd_6737204 3459423919393763892066169 := by
  unfold tailWord_6737204
  simp only [CollatzResearch.WordTrace]
  refine ⟨122863008542134002841273333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163817344722845337121697777 122863008542134002841273333)
  ·
    refine ⟨11518407050825062766369375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122863008542134002841273333 11518407050825062766369375)
    ·
      refine ⟨17277610576237594149554063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11518407050825062766369375 17277610576237594149554063)
      ·
        refine ⟨25916415864356391224331095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17277610576237594149554063 25916415864356391224331095)
        ·
          refine ⟨38874623796534586836496643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25916415864356391224331095 38874623796534586836496643)
          ·
            refine ⟨58311935694801880254744965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38874623796534586836496643 58311935694801880254744965)
            ·
              refine ⟨10933487942775352547764681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58311935694801880254744965 10933487942775352547764681)
              ·
                refine ⟨8200115957081514410823511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10933487942775352547764681 8200115957081514410823511)
                ·
                  refine ⟨12300173935622271616235267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200115957081514410823511 12300173935622271616235267)
                  ·
                    refine ⟨18450260903433407424352901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12300173935622271616235267 18450260903433407424352901)
                    ·
                      refine ⟨3459423919393763892066169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18450260903433407424352901 3459423919393763892066169)
                      ·
                        rfl

theorem cell23_6737204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_6737204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737204 prefixEnd_6737204 := by exact prefixLift 6737204
  have htrace : WordTrace (prefixWord ++ tailWord_6737204) baseStart_6737204 baseEnd_6737204 := by
    simpa [prefixWord, tailWord_6737204, baseEnd_6737204] using wordTrace_append hprefix tailTrace_6737204
  have hstable : (prefixWord ++ tailWord_6737204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737204).length < 2 ^ (prefixWord ++ tailWord_6737204).sum := by decide
  have hdescent : baseEnd_6737204 < baseStart_6737204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737247 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 3, 3, 2]
def baseStart_6737247 : Nat := 118140960795 + 6737247 * 2 ^ 59
def prefixEnd_6737247 : Nat := 4983230072969 + 3 ^ 40 * 6737247 * 2
def baseEnd_6737247 : Nat := 3459445999061907223828471

theorem tailTrace_6737247 : CollatzResearch.WordTrace tailWord_6737247 prefixEnd_6737247 3459445999061907223828471 := by
  unfold tailWord_6737247
  simp only [CollatzResearch.WordTrace]
  refine ⟨245727585423112224026361995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163818390282074816017574663 245727585423112224026361995)
  ·
    refine ⟨368591378134668336039542993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245727585423112224026361995 368591378134668336039542993)
    ·
      refine ⟨276443533601001252029657245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368591378134668336039542993 276443533601001252029657245)
      ·
        refine ⟨103666325100375469511121467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276443533601001252029657245 103666325100375469511121467)
        ·
          refine ⟨155499487650563204266682201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103666325100375469511121467 155499487650563204266682201)
          ·
            refine ⟨116624615737922403200011651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155499487650563204266682201 116624615737922403200011651)
            ·
              refine ⟨174936923606883604800017477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116624615737922403200011651 174936923606883604800017477)
              ·
                refine ⟨32800673176290675900003277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174936923606883604800017477 32800673176290675900003277)
                ·
                  refine ⟨12300252441109003462501229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32800673176290675900003277 12300252441109003462501229)
                  ·
                    refine ⟨4612594665415876298437961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12300252441109003462501229 4612594665415876298437961)
                    ·
                      refine ⟨3459445999061907223828471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612594665415876298437961 3459445999061907223828471)
                      ·
                        rfl

theorem cell23_6737247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_6737247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737247 prefixEnd_6737247 := by exact prefixLift 6737247
  have htrace : WordTrace (prefixWord ++ tailWord_6737247) baseStart_6737247 baseEnd_6737247 := by
    simpa [prefixWord, tailWord_6737247, baseEnd_6737247] using wordTrace_append hprefix tailTrace_6737247
  have hstable : (prefixWord ++ tailWord_6737247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737247).length < 2 ^ (prefixWord ++ tailWord_6737247).sum := by decide
  have hdescent : baseEnd_6737247 < baseStart_6737247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737258 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6737258 : Nat := 118140960795 + 6737258 * 2 ^ 59
def prefixEnd_6737258 : Nat := 4983230072969 + 3 ^ 40 * 6737258 * 2
def baseEnd_6737258 : Nat := 3459451647349106680790921

theorem tailTrace_6737258 : CollatzResearch.WordTrace tailWord_6737258 prefixEnd_6737258 3459451647349106680790921 := by
  unfold tailWord_6737258
  simp only [CollatzResearch.WordTrace]
  refine ⟨61431996656518093226253107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163818657750714915270008285 61431996656518093226253107)
  ·
    refine ⟨92147994984777139839379661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61431996656518093226253107 92147994984777139839379661)
    ·
      refine ⟨34555498119291427439767373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92147994984777139839379661 34555498119291427439767373)
      ·
        refine ⟨12958311794734285289912765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34555498119291427439767373 12958311794734285289912765)
        ·
          refine ⟨4859366923025356983717287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12958311794734285289912765 4859366923025356983717287)
          ·
            refine ⟨7289050384538035475575931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859366923025356983717287 7289050384538035475575931)
            ·
              refine ⟨10933575576807053213363897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289050384538035475575931 10933575576807053213363897)
              ·
                refine ⟨8200181682605289910022923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10933575576807053213363897 8200181682605289910022923)
                ·
                  refine ⟨12300272523907934865034385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200181682605289910022923 12300272523907934865034385)
                  ·
                    refine ⟨9225204392930951148775789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12300272523907934865034385 9225204392930951148775789)
                    ·
                      refine ⟨3459451647349106680790921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225204392930951148775789 3459451647349106680790921)
                      ·
                        rfl

theorem cell23_6737258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6737258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737258 prefixEnd_6737258 := by exact prefixLift 6737258
  have htrace : WordTrace (prefixWord ++ tailWord_6737258) baseStart_6737258 baseEnd_6737258 := by
    simpa [prefixWord, tailWord_6737258, baseEnd_6737258] using wordTrace_append hprefix tailTrace_6737258
  have hstable : (prefixWord ++ tailWord_6737258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737258).length < 2 ^ (prefixWord ++ tailWord_6737258).sum := by decide
  have hdescent : baseEnd_6737258 < baseStart_6737258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737280 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_6737280 : Nat := 118140960795 + 6737280 * 2 ^ 59
def prefixEnd_6737280 : Nat := 4983230072969 + 3 ^ 40 * 6737280 * 2
def baseEnd_6737280 : Nat := 3459462943923505594715819

theorem tailTrace_6737280 : CollatzResearch.WordTrace tailWord_6737280 prefixEnd_6737280 3459462943923505594715819 := by
  unfold tailWord_6737280
  simp only [CollatzResearch.WordTrace]
  refine ⟨122864394515996335331156647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163819192687995113774875529 122864394515996335331156647)
  ·
    refine ⟨184296591773994502996734971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122864394515996335331156647 184296591773994502996734971)
    ·
      refine ⟨276444887660991754495102457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184296591773994502996734971 276444887660991754495102457)
      ·
        refine ⟨207333665745743815871326843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276444887660991754495102457 207333665745743815871326843)
        ·
          refine ⟨311000498618615723806990265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207333665745743815871326843 311000498618615723806990265)
          ·
            refine ⟨233250373963961792855242699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311000498618615723806990265 233250373963961792855242699)
            ·
              refine ⟨349875560945942689282864049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233250373963961792855242699 349875560945942689282864049)
              ·
                refine ⟨262406670709457016962148037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349875560945942689282864049 262406670709457016962148037)
                ·
                  refine ⟨49201250758023190680402757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262406670709457016962148037 49201250758023190680402757)
                  ·
                    refine ⟨9225234517129348252575517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49201250758023190680402757 9225234517129348252575517)
                    ·
                      refine ⟨3459462943923505594715819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225234517129348252575517 3459462943923505594715819)
                      ·
                        rfl

theorem cell23_6737280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_6737280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737280 prefixEnd_6737280 := by exact prefixLift 6737280
  have htrace : WordTrace (prefixWord ++ tailWord_6737280) baseStart_6737280 baseEnd_6737280 := by
    simpa [prefixWord, tailWord_6737280, baseEnd_6737280] using wordTrace_append hprefix tailTrace_6737280
  have hstable : (prefixWord ++ tailWord_6737280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737280).length < 2 ^ (prefixWord ++ tailWord_6737280).sum := by decide
  have hdescent : baseEnd_6737280 < baseStart_6737280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737311 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 2, 2, 2]
def baseStart_6737311 : Nat := 118140960795 + 6737311 * 2 ^ 59
def prefixEnd_6737311 : Nat := 4983230072969 + 3 ^ 40 * 6737311 * 2
def baseEnd_6737311 : Nat := 3459478861823794973428177

theorem tailTrace_6737311 : CollatzResearch.WordTrace tailWord_6737311 prefixEnd_6737311 3459478861823794973428177 := by
  unfold tailWord_6737311
  simp only [CollatzResearch.WordTrace]
  refine ⟨245729919694880362956691787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163819946463253575304461191 245729919694880362956691787)
  ·
    refine ⟨368594879542320544435037681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245729919694880362956691787 368594879542320544435037681)
    ·
      refine ⟨276446159656740408326278261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368594879542320544435037681 276446159656740408326278261)
      ·
        refine ⟨25916827467819413280588587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276446159656740408326278261 25916827467819413280588587)
        ·
          refine ⟨38875241201729119920882881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25916827467819413280588587 38875241201729119920882881)
          ·
            refine ⟨29156430901296839940662161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38875241201729119920882881 29156430901296839940662161)
            ·
              refine ⟨21867323175972629955496621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29156430901296839940662161 21867323175972629955496621)
              ·
                refine ⟨8200246190989736233311233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21867323175972629955496621 8200246190989736233311233)
                ·
                  refine ⟨6150184643242302174983425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8200246190989736233311233 6150184643242302174983425)
                  ·
                    refine ⟨4612638482431726631237569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6150184643242302174983425 4612638482431726631237569)
                    ·
                      refine ⟨3459478861823794973428177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612638482431726631237569 3459478861823794973428177)
                      ·
                        rfl

theorem cell23_6737311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_6737311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737311 prefixEnd_6737311 := by exact prefixLift 6737311
  have htrace : WordTrace (prefixWord ++ tailWord_6737311) baseStart_6737311 baseEnd_6737311 := by
    simpa [prefixWord, tailWord_6737311, baseEnd_6737311] using wordTrace_append hprefix tailTrace_6737311
  have hstable : (prefixWord ++ tailWord_6737311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737311).length < 2 ^ (prefixWord ++ tailWord_6737311).sum := by decide
  have hdescent : baseEnd_6737311 < baseStart_6737311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737434 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_6737434 : Nat := 118140960795 + 6737434 * 2 ^ 59
def prefixEnd_6737434 : Nat := 4983230072969 + 3 ^ 40 * 6737434 * 2
def baseEnd_6737434 : Nat := 3459542019944297992190111

theorem tailTrace_6737434 : CollatzResearch.WordTrace tailWord_6737434 prefixEnd_6737434 3459542019944297992190111 := by
  unfold tailWord_6737434
  simp only [CollatzResearch.WordTrace]
  refine ⟨61433601468358688740854839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163822937248956503308946237 61433601468358688740854839)
  ·
    refine ⟨92150402202538033111282259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61433601468358688740854839 92150402202538033111282259)
    ·
      refine ⟨138225603303807049666923389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92150402202538033111282259 138225603303807049666923389)
      ·
        refine ⟨51834601238927643625096271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138225603303807049666923389 51834601238927643625096271)
        ·
          refine ⟨77751901858391465437644407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51834601238927643625096271 77751901858391465437644407)
          ·
            refine ⟨116627852787587198156466611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77751901858391465437644407 116627852787587198156466611)
            ·
              refine ⟨174941779181380797234699917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116627852787587198156466611 174941779181380797234699917)
              ·
                refine ⟨65603167193017798963012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174941779181380797234699917 65603167193017798963012469)
                ·
                  refine ⟨6150296924345418652782419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65603167193017798963012469 6150296924345418652782419)
                  ·
                    refine ⟨9225445386518127979173629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150296924345418652782419 9225445386518127979173629)
                    ·
                      refine ⟨3459542019944297992190111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225445386518127979173629 3459542019944297992190111)
                      ·
                        rfl

theorem cell23_6737434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_6737434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737434 prefixEnd_6737434 := by exact prefixLift 6737434
  have htrace : WordTrace (prefixWord ++ tailWord_6737434) baseStart_6737434 baseEnd_6737434 := by
    simpa [prefixWord, tailWord_6737434, baseEnd_6737434] using wordTrace_append hprefix tailTrace_6737434
  have hstable : (prefixWord ++ tailWord_6737434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737434).length < 2 ^ (prefixWord ++ tailWord_6737434).sum := by decide
  have hdescent : baseEnd_6737434 < baseStart_6737434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737461 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_6737461 : Nat := 118140960795 + 6737461 * 2 ^ 59
def prefixEnd_6737461 : Nat := 4983230072969 + 3 ^ 40 * 6737461 * 2
def baseEnd_6737461 : Nat := 3459555883921969386552487

theorem tailTrace_6737461 : CollatzResearch.WordTrace tailWord_6737461 prefixEnd_6737461 3459555883921969386552487 := by
  unfold tailWord_6737461
  simp only [CollatzResearch.WordTrace]
  refine ⟨245735390644336938574652237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163823593762891292383101491 245735390644336938574652237)
  ·
    refine ⟨92150771491626351965494589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245735390644336938574652237 92150771491626351965494589)
    ·
      refine ⟨34556539309359881987060471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92150771491626351965494589 34556539309359881987060471)
      ·
        refine ⟨51834808964039822980590707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34556539309359881987060471 51834808964039822980590707)
        ·
          refine ⟨77752213446059734470886061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51834808964039822980590707 77752213446059734470886061)
          ·
            refine ⟨29157080042272400426582273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77752213446059734470886061 29157080042272400426582273)
            ·
              refine ⟨21867810031704300319936705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29157080042272400426582273 21867810031704300319936705)
              ·
                refine ⟨16400857523778225239952529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21867810031704300319936705 16400857523778225239952529)
                ·
                  refine ⟨12300643142833668929964397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16400857523778225239952529 12300643142833668929964397)
                  ·
                    refine ⟨4612741178562625848736649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12300643142833668929964397 4612741178562625848736649)
                    ·
                      refine ⟨3459555883921969386552487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612741178562625848736649 3459555883921969386552487)
                      ·
                        rfl

theorem cell23_6737461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_6737461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737461 prefixEnd_6737461 := by exact prefixLift 6737461
  have htrace : WordTrace (prefixWord ++ tailWord_6737461) baseStart_6737461 baseEnd_6737461 := by
    simpa [prefixWord, tailWord_6737461, baseEnd_6737461] using wordTrace_append hprefix tailTrace_6737461
  have hstable : (prefixWord ++ tailWord_6737461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737461).length < 2 ^ (prefixWord ++ tailWord_6737461).sum := by decide
  have hdescent : baseEnd_6737461 < baseStart_6737461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737462 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6737462 : Nat := 118140960795 + 6737462 * 2 ^ 59
def prefixEnd_6737462 : Nat := 4983230072969 + 3 ^ 40 * 6737462 * 2
def baseEnd_6737462 : Nat := 1153185465800874627546661

theorem tailTrace_6737462 : CollatzResearch.WordTrace tailWord_6737462 prefixEnd_6737462 1153185465800874627546661 := by
  unfold tailWord_6737462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358464194833332234089915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163823618078222210496959093 15358464194833332234089915)
  ·
    refine ⟨23037696292249998351134873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15358464194833332234089915 23037696292249998351134873)
    ·
      refine ⟨17278272219187498763351155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23037696292249998351134873 17278272219187498763351155)
      ·
        refine ⟨25917408328781248145026733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17278272219187498763351155 25917408328781248145026733)
        ·
          refine ⟨9719028123292968054385025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25917408328781248145026733 9719028123292968054385025)
          ·
            refine ⟨7289271092469726040788769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719028123292968054385025 7289271092469726040788769)
            ·
              refine ⟨5466953319352294530591577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289271092469726040788769 5466953319352294530591577)
              ·
                refine ⟨4100214989514220897943683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466953319352294530591577 4100214989514220897943683)
                ·
                  refine ⟨6150322484271331346915525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100214989514220897943683 6150322484271331346915525)
                  ·
                    refine ⟨1153185465800874627546661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150322484271331346915525 1153185465800874627546661)
                    ·
                      rfl

theorem cell23_6737462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6737462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737462 prefixEnd_6737462 := by exact prefixLift 6737462
  have htrace : WordTrace (prefixWord ++ tailWord_6737462) baseStart_6737462 baseEnd_6737462 := by
    simpa [prefixWord, tailWord_6737462, baseEnd_6737462] using wordTrace_append hprefix tailTrace_6737462
  have hstable : (prefixWord ++ tailWord_6737462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737462).length < 2 ^ (prefixWord ++ tailWord_6737462).sum := by decide
  have hdescent : baseEnd_6737462 < baseStart_6737462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737477 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_6737477 : Nat := 118140960795 + 6737477 * 2 ^ 59
def prefixEnd_6737477 : Nat := 4983230072969 + 3 ^ 40 * 6737477 * 2
def baseEnd_6737477 : Nat := 3459564099612441323952413

theorem tailTrace_6737477 : CollatzResearch.WordTrace tailWord_6737477 prefixEnd_6737477 3459564099612441323952413 := by
  unfold tailWord_6737477
  simp only [CollatzResearch.WordTrace]
  refine ⟨245735974212278973307234685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163823982808185982204823123 245735974212278973307234685)
  ·
    refine ⟨92150990329604614990213007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245735974212278973307234685 92150990329604614990213007)
    ·
      refine ⟨138226485494406922485319511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92150990329604614990213007 138226485494406922485319511)
      ·
        refine ⟨207339728241610383727979267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138226485494406922485319511 207339728241610383727979267)
        ·
          refine ⟨311009592362415575591968901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207339728241610383727979267 311009592362415575591968901)
          ·
            refine ⟨58314298567952920423494169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311009592362415575591968901 58314298567952920423494169)
            ·
              refine ⟨43735723925964690317620627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58314298567952920423494169 43735723925964690317620627)
              ·
                refine ⟨65603585888947035476430941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43735723925964690317620627 65603585888947035476430941)
                ·
                  refine ⟨24601344708355138303661603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65603585888947035476430941 24601344708355138303661603)
                  ·
                    refine ⟨36902017062532707455492405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24601344708355138303661603 36902017062532707455492405)
                    ·
                      refine ⟨3459564099612441323952413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36902017062532707455492405 3459564099612441323952413)
                      ·
                        rfl

theorem cell23_6737477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_6737477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737477 prefixEnd_6737477 := by exact prefixLift 6737477
  have htrace : WordTrace (prefixWord ++ tailWord_6737477) baseStart_6737477 baseEnd_6737477 := by
    simpa [prefixWord, tailWord_6737477, baseEnd_6737477] using wordTrace_append hprefix tailTrace_6737477
  have hstable : (prefixWord ++ tailWord_6737477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737477).length < 2 ^ (prefixWord ++ tailWord_6737477).sum := by decide
  have hdescent : baseEnd_6737477 < baseStart_6737477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737484 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_6737484 : Nat := 118140960795 + 6737484 * 2 ^ 59
def prefixEnd_6737484 : Nat := 4983230072969 + 3 ^ 40 * 6737484 * 2
def baseEnd_6737484 : Nat := 1153189231325674265521627

theorem tailTrace_6737484 : CollatzResearch.WordTrace tailWord_6737484 prefixEnd_6737484 1153189231325674265521627 := by
  unfold tailWord_6737484
  simp only [CollatzResearch.WordTrace]
  refine ⟨122868114761626806751369753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163824153015502409001826337 122868114761626806751369753)
  ·
    refine ⟨92151086071220105063527315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122868114761626806751369753 92151086071220105063527315)
    ·
      refine ⟨138226629106830157595290973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92151086071220105063527315 138226629106830157595290973)
      ·
        refine ⟨51834985915061309098234115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138226629106830157595290973 51834985915061309098234115)
        ·
          refine ⟨77752478872591963647351173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51834985915061309098234115 77752478872591963647351173)
          ·
            refine ⟨14578589788610993183878345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77752478872591963647351173 14578589788610993183878345)
            ·
              refine ⟨10933942341458244887908759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14578589788610993183878345 10933942341458244887908759)
              ·
                refine ⟨16400913512187367331863139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10933942341458244887908759 16400913512187367331863139)
                ·
                  refine ⟨24601370268281050997794709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16400913512187367331863139 24601370268281050997794709)
                  ·
                    refine ⟨1153189231325674265521627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24601370268281050997794709 1153189231325674265521627)
                    ·
                      rfl

theorem cell23_6737484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_6737484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737484 prefixEnd_6737484 := by exact prefixLift 6737484
  have htrace : WordTrace (prefixWord ++ tailWord_6737484) baseStart_6737484 baseEnd_6737484 := by
    simpa [prefixWord, tailWord_6737484, baseEnd_6737484] using wordTrace_append hprefix tailTrace_6737484
  have hstable : (prefixWord ++ tailWord_6737484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737484).length < 2 ^ (prefixWord ++ tailWord_6737484).sum := by decide
  have hdescent : baseEnd_6737484 < baseStart_6737484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737508 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_6737508 : Nat := 118140960795 + 6737508 * 2 ^ 59
def prefixEnd_6737508 : Nat := 4983230072969 + 3 ^ 40 * 6737508 * 2
def baseEnd_6737508 : Nat := 3459580017512730702664771

theorem tailTrace_6737508 : CollatzResearch.WordTrace tailWord_6737508 prefixEnd_6737508 3459580017512730702664771 := by
  unfold tailWord_6737508
  simp only [CollatzResearch.WordTrace]
  refine ⟨122868552437583332800806589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163824736583444443734408785 122868552437583332800806589)
  ·
    refine ⟨46075707164093749800302471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122868552437583332800806589 46075707164093749800302471)
    ·
      refine ⟨69113560746140624700453707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46075707164093749800302471 69113560746140624700453707)
      ·
        refine ⟨103670341119210937050680561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69113560746140624700453707 103670341119210937050680561)
        ·
          refine ⟨77752755839408202788010421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103670341119210937050680561 77752755839408202788010421)
          ·
            refine ⟨7289320859944519011375977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77752755839408202788010421 7289320859944519011375977)
            ·
              refine ⟨5466990644958389258531983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289320859944519011375977 5466990644958389258531983)
              ·
                refine ⟨8200485967437583887797975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466990644958389258531983 8200485967437583887797975)
                ·
                  refine ⟨12300728951156375831696963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200485967437583887797975 12300728951156375831696963)
                  ·
                    refine ⟨18451093426734563747545445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12300728951156375831696963 18451093426734563747545445)
                    ·
                      refine ⟨3459580017512730702664771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18451093426734563747545445 3459580017512730702664771)
                      ·
                        rfl

theorem cell23_6737508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_6737508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737508 prefixEnd_6737508 := by exact prefixLift 6737508
  have htrace : WordTrace (prefixWord ++ tailWord_6737508) baseStart_6737508 baseEnd_6737508 := by
    simpa [prefixWord, tailWord_6737508, baseEnd_6737508] using wordTrace_append hprefix tailTrace_6737508
  have hstable : (prefixWord ++ tailWord_6737508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737508).length < 2 ^ (prefixWord ++ tailWord_6737508).sum := by decide
  have hdescent : baseEnd_6737508 < baseStart_6737508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737525 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6737525 : Nat := 118140960795 + 6737525 * 2 ^ 59
def prefixEnd_6737525 : Nat := 4983230072969 + 3 ^ 40 * 6737525 * 2
def baseEnd_6737525 : Nat := 3459588746683857136152193

theorem tailTrace_6737525 : CollatzResearch.WordTrace tailWord_6737525 prefixEnd_6737525 3459588746683857136152193 := by
  unfold tailWord_6737525
  simp only [CollatzResearch.WordTrace]
  refine ⟨245737724916105077504982029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163825149944070051669988019 245737724916105077504982029)
  ·
    refine ⟨92151646843539404064368261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245737724916105077504982029 92151646843539404064368261)
    ·
      refine ⟨17278433783163638262069049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92151646843539404064368261 17278433783163638262069049)
      ·
        refine ⟨12958825337372728696551787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17278433783163638262069049 12958825337372728696551787)
        ·
          refine ⟨19438238006059093044827681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958825337372728696551787 19438238006059093044827681)
          ·
            refine ⟨14578678504544319783620761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19438238006059093044827681 14578678504544319783620761)
            ·
              refine ⟨10934008878408239837715571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14578678504544319783620761 10934008878408239837715571)
              ·
                refine ⟨16401013317612359756573357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934008878408239837715571 16401013317612359756573357)
                ·
                  refine ⟨6150379994104634908715009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16401013317612359756573357 6150379994104634908715009)
                  ·
                    refine ⟨4612784995578476181536257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6150379994104634908715009 4612784995578476181536257)
                    ·
                      refine ⟨3459588746683857136152193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612784995578476181536257 3459588746683857136152193)
                      ·
                        rfl

theorem cell23_6737525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6737525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737525 prefixEnd_6737525 := by exact prefixLift 6737525
  have htrace : WordTrace (prefixWord ++ tailWord_6737525) baseStart_6737525 baseEnd_6737525 := by
    simpa [prefixWord, tailWord_6737525, baseEnd_6737525] using wordTrace_append hprefix tailTrace_6737525
  have hstable : (prefixWord ++ tailWord_6737525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737525).length < 2 ^ (prefixWord ++ tailWord_6737525).sum := by decide
  have hdescent : baseEnd_6737525 < baseStart_6737525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737557 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_6737557 : Nat := 118140960795 + 6737557 * 2 ^ 59
def prefixEnd_6737557 : Nat := 4983230072969 + 3 ^ 40 * 6737557 * 2
def baseEnd_6737557 : Nat := 1153201726021600336984015

theorem tailTrace_6737557 : CollatzResearch.WordTrace tailWord_6737557 prefixEnd_6737557 1153201726021600336984015 := by
  unfold tailWord_6737557
  simp only [CollatzResearch.WordTrace]
  refine ⟨245738892051989146970146925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163825928034659431313431283 245738892051989146970146925)
  ·
    refine ⟨92152084519495930113805097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245738892051989146970146925 92152084519495930113805097)
    ·
      refine ⟨69114063389621947585353823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92152084519495930113805097 69114063389621947585353823)
      ·
        refine ⟨103671095084432921378030735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69114063389621947585353823 103671095084432921378030735)
        ·
          refine ⟨155506642626649382067046103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103671095084432921378030735 155506642626649382067046103)
          ·
            refine ⟨233259963939974073100569155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155506642626649382067046103 233259963939974073100569155)
            ·
              refine ⟨349889945909961109650853733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233259963939974073100569155 349889945909961109650853733)
              ·
                refine ⟨65604364858117708059535075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349889945909961109650853733 65604364858117708059535075)
                ·
                  refine ⟨98406547287176562089302613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65604364858117708059535075 98406547287176562089302613)
                  ·
                    refine ⟨1153201726021600336984015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98406547287176562089302613 1153201726021600336984015)
                    ·
                      rfl

theorem cell23_6737557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_6737557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737557 prefixEnd_6737557 := by exact prefixLift 6737557
  have htrace : WordTrace (prefixWord ++ tailWord_6737557) baseStart_6737557 baseEnd_6737557 := by
    simpa [prefixWord, tailWord_6737557, baseEnd_6737557] using wordTrace_append hprefix tailTrace_6737557
  have hstable : (prefixWord ++ tailWord_6737557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737557).length < 2 ^ (prefixWord ++ tailWord_6737557).sum := by decide
  have hdescent : baseEnd_6737557 < baseStart_6737557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737568 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2]
def baseStart_6737568 : Nat := 118140960795 + 6737568 * 2 ^ 59
def prefixEnd_6737568 : Nat := 4983230072969 + 3 ^ 40 * 6737568 * 2
def baseEnd_6737568 : Nat := 3459610826352000467914495

theorem tailTrace_6737568 : CollatzResearch.WordTrace tailWord_6737568 prefixEnd_6737568 3459610826352000467914495 := by
  unfold tailWord_6737568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122869646627474647924398679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163826195503299530565864905 122869646627474647924398679)
  ·
    refine ⟨184304469941211971886598019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122869646627474647924398679 184304469941211971886598019)
    ·
      refine ⟨276456704911817957829897029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184304469941211971886598019 276456704911817957829897029)
      ·
        refine ⟨51835632170965867093105693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276456704911817957829897029 51835632170965867093105693)
        ·
          refine ⟨19438362064112200159914635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51835632170965867093105693 19438362064112200159914635)
          ·
            refine ⟨29157543096168300239871953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19438362064112200159914635 29157543096168300239871953)
            ·
              refine ⟨21868157322126225179903965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29157543096168300239871953 21868157322126225179903965)
              ·
                refine ⟨8200558995797334442463987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21868157322126225179903965 8200558995797334442463987)
                ·
                  refine ⟨12300838493696001663695981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200558995797334442463987 12300838493696001663695981)
                  ·
                    refine ⟨4612814435136000623885993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12300838493696001663695981 4612814435136000623885993)
                    ·
                      refine ⟨3459610826352000467914495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612814435136000623885993 3459610826352000467914495)
                      ·
                        rfl

theorem cell23_6737568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_6737568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737568 prefixEnd_6737568 := by exact prefixLift 6737568
  have htrace : WordTrace (prefixWord ++ tailWord_6737568) baseStart_6737568 baseEnd_6737568 := by
    simpa [prefixWord, tailWord_6737568, baseEnd_6737568] using wordTrace_append hprefix tailTrace_6737568
  have hstable : (prefixWord ++ tailWord_6737568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737568).length < 2 ^ (prefixWord ++ tailWord_6737568).sum := by decide
  have hdescent : baseEnd_6737568 < baseStart_6737568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737576 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6737576 : Nat := 118140960795 + 6737576 * 2 ^ 59
def prefixEnd_6737576 : Nat := 4983230072969 + 3 ^ 40 * 6737576 * 2
def baseEnd_6737576 : Nat := 3459614934197236436614459

theorem tailTrace_6737576 : CollatzResearch.WordTrace tailWord_6737576 prefixEnd_6737576 3459614934197236436614459 := by
  unfold tailWord_6737576
  simp only [CollatzResearch.WordTrace]
  refine ⟨122869792519460156607544291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163826390025946875476725721 122869792519460156607544291)
  ·
    refine ⟨184304688779190234911316437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122869792519460156607544291 184304688779190234911316437)
    ·
      refine ⟨4319641143262271130733979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 184304688779190234911316437 4319641143262271130733979)
      ·
        refine ⟨6479461714893406696100969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319641143262271130733979 6479461714893406696100969)
        ·
          refine ⟨4859596286170055022075727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479461714893406696100969 4859596286170055022075727)
          ·
            refine ⟨7289394429255082533113591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859596286170055022075727 7289394429255082533113591)
            ·
              refine ⟨10934091643882623799670387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289394429255082533113591 10934091643882623799670387)
              ·
                refine ⟨16401137465823935699505581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934091643882623799670387 16401137465823935699505581)
                ·
                  refine ⟨6150426549683975887314593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16401137465823935699505581 6150426549683975887314593)
                  ·
                    refine ⟨4612819912262981915485945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6150426549683975887314593 4612819912262981915485945)
                    ·
                      refine ⟨3459614934197236436614459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612819912262981915485945 3459614934197236436614459)
                      ·
                        rfl

theorem cell23_6737576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6737576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737576 prefixEnd_6737576 := by exact prefixLift 6737576
  have htrace : WordTrace (prefixWord ++ tailWord_6737576) baseStart_6737576 baseEnd_6737576 := by
    simpa [prefixWord, tailWord_6737576, baseEnd_6737576] using wordTrace_append hprefix tailTrace_6737576
  have hstable : (prefixWord ++ tailWord_6737576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737576).length < 2 ^ (prefixWord ++ tailWord_6737576).sum := by decide
  have hdescent : baseEnd_6737576 < baseStart_6737576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737604 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 9]
def baseStart_6737604 : Nat := 118140960795 + 6737604 * 2 ^ 59
def prefixEnd_6737604 : Nat := 4983230072969 + 3 ^ 40 * 6737604 * 2
def baseEnd_6737604 : Nat := 384403256850618036340481

theorem tailTrace_6737604 : CollatzResearch.WordTrace tailWord_6737604 prefixEnd_6737604 384403256850618036340481 := by
  unfold tailWord_6737604
  simp only [CollatzResearch.WordTrace]
  refine ⟨122870303141409436998553933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163827070855212582664738577 122870303141409436998553933)
  ·
    refine ⟨46076363678028538874457725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122870303141409436998553933 46076363678028538874457725)
    ·
      refine ⟨17278636379260702077921647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46076363678028538874457725 17278636379260702077921647)
      ·
        refine ⟨25917954568891053116882471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17278636379260702077921647 25917954568891053116882471)
        ·
          refine ⟨38876931853336579675323707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25917954568891053116882471 38876931853336579675323707)
          ·
            refine ⟨58315397780004869512985561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38876931853336579675323707 58315397780004869512985561)
            ·
              refine ⟨43736548335003652134739171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58315397780004869512985561 43736548335003652134739171)
              ·
                refine ⟨65604822502505478202108757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43736548335003652134739171 65604822502505478202108757)
                ·
                  refine ⟨384403256850618036340481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65604822502505478202108757 384403256850618036340481)
                  ·
                    rfl

theorem cell23_6737604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_6737604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737604 prefixEnd_6737604 := by exact prefixLift 6737604
  have htrace : WordTrace (prefixWord ++ tailWord_6737604) baseStart_6737604 baseEnd_6737604 := by
    simpa [prefixWord, tailWord_6737604, baseEnd_6737604] using wordTrace_append hprefix tailTrace_6737604
  have hstable : (prefixWord ++ tailWord_6737604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737604).length < 2 ^ (prefixWord ++ tailWord_6737604).sum := by decide
  have hdescent : baseEnd_6737604 < baseStart_6737604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737644 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6737644 : Nat := 118140960795 + 6737644 * 2 ^ 59
def prefixEnd_6737644 : Nat := 4983230072969 + 3 ^ 40 * 6737644 * 2
def baseEnd_6737644 : Nat := 3459649850881742170564145

theorem tailTrace_6737644 : CollatzResearch.WordTrace tailWord_6737644 prefixEnd_6737644 3459649850881742170564145 := by
  unfold tailWord_6737644
  simp only [CollatzResearch.WordTrace]
  refine ⟨122871032601336980414281993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163828043468449307219042657 122871032601336980414281993)
  ·
    refine ⟨92153274451002735310711495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122871032601336980414281993 92153274451002735310711495)
    ·
      refine ⟨138229911676504102966067243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92153274451002735310711495 138229911676504102966067243)
      ·
        refine ⟨207344867514756154449100865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138229911676504102966067243 207344867514756154449100865)
        ·
          refine ⟨155508650636067115836825649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207344867514756154449100865 155508650636067115836825649)
          ·
            refine ⟨116631487977050336877619237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155508650636067115836825649 116631487977050336877619237)
            ·
              refine ⟨21868403995696938164553607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116631487977050336877619237 21868403995696938164553607)
              ·
                refine ⟨32802605993545407246830411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21868403995696938164553607 32802605993545407246830411)
                ·
                  refine ⟨49203908990318110870245617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32802605993545407246830411 49203908990318110870245617)
                  ·
                    refine ⟨36902931742738583152684213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49203908990318110870245617 36902931742738583152684213)
                    ·
                      refine ⟨3459649850881742170564145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36902931742738583152684213 3459649850881742170564145)
                      ·
                        rfl

theorem cell23_6737644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6737644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737644 prefixEnd_6737644 := by exact prefixLift 6737644
  have htrace : WordTrace (prefixWord ++ tailWord_6737644) baseStart_6737644 baseEnd_6737644 := by
    simpa [prefixWord, tailWord_6737644, baseEnd_6737644] using wordTrace_append hprefix tailTrace_6737644
  have hstable : (prefixWord ++ tailWord_6737644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737644).length < 2 ^ (prefixWord ++ tailWord_6737644).sum := by decide
  have hdescent : baseEnd_6737644 < baseStart_6737644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737668 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6737668 : Nat := 118140960795 + 6737668 * 2 ^ 59
def prefixEnd_6737668 : Nat := 4983230072969 + 3 ^ 40 * 6737668 * 2
def baseEnd_6737668 : Nat := 1153220724805816692221345

theorem tailTrace_6737668 : CollatzResearch.WordTrace tailWord_6737668 prefixEnd_6737668 1153220724805816692221345 := by
  unfold tailWord_6737668
  simp only [CollatzResearch.WordTrace]
  refine ⟨122871470277293506463718829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163828627036391341951625105 122871470277293506463718829)
  ·
    refine ⟨46076801353985064923894561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122871470277293506463718829 46076801353985064923894561)
    ·
      refine ⟨34557601015488798692920921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46076801353985064923894561 34557601015488798692920921)
      ·
        refine ⟨25918200761616599019690691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34557601015488798692920921 25918200761616599019690691)
        ·
          refine ⟨38877301142424898529536037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25918200761616599019690691 38877301142424898529536037)
          ·
            refine ⟨7289493964204668474288007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38877301142424898529536037 7289493964204668474288007)
            ·
              refine ⟨10934240946307002711432011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289493964204668474288007 10934240946307002711432011)
              ·
                refine ⟨16401361419460504067148017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934240946307002711432011 16401361419460504067148017)
                ·
                  refine ⟨12301021064595378050361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16401361419460504067148017 12301021064595378050361013)
                  ·
                    refine ⟨1153220724805816692221345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12301021064595378050361013 1153220724805816692221345)
                    ·
                      rfl

theorem cell23_6737668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6737668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737668 prefixEnd_6737668 := by exact prefixLift 6737668
  have htrace : WordTrace (prefixWord ++ tailWord_6737668) baseStart_6737668 baseEnd_6737668 := by
    simpa [prefixWord, tailWord_6737668, baseEnd_6737668] using wordTrace_append hprefix tailTrace_6737668
  have hstable : (prefixWord ++ tailWord_6737668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737668).length < 2 ^ (prefixWord ++ tailWord_6737668).sum := by decide
  have hdescent : baseEnd_6737668 < baseStart_6737668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737670 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6737670 : Nat := 118140960795 + 6737670 * 2 ^ 59
def prefixEnd_6737670 : Nat := 4983230072969 + 3 ^ 40 * 6737670 * 2
def baseEnd_6737670 : Nat := 3459663201378759068839027

theorem tailTrace_6737670 : CollatzResearch.WordTrace tailWord_6737670 prefixEnd_6737670 3459663201378759068839027 := by
  unfold tailWord_6737670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679469171893117727156577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163828675667053178179340309 7679469171893117727156577)
  ·
    refine ⟨5759601878919838295367433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7679469171893117727156577 5759601878919838295367433)
    ·
      refine ⟨4319701409189878721525575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5759601878919838295367433 4319701409189878721525575)
      ·
        refine ⟨6479552113784818082288363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319701409189878721525575 6479552113784818082288363)
        ·
          refine ⟨9719328170677227123432545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6479552113784818082288363 9719328170677227123432545)
          ·
            refine ⟨7289496128007920342574409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719328170677227123432545 7289496128007920342574409)
            ·
              refine ⟨5467122096005940256930807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289496128007920342574409 5467122096005940256930807)
              ·
                refine ⟨8200683144008910385396211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467122096005940256930807 8200683144008910385396211)
                ·
                  refine ⟨12301024716013365578094317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200683144008910385396211 12301024716013365578094317)
                  ·
                    refine ⟨4612884268505012091785369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12301024716013365578094317 4612884268505012091785369)
                    ·
                      refine ⟨3459663201378759068839027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4612884268505012091785369 3459663201378759068839027)
                      ·
                        rfl

theorem cell23_6737670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6737670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737670 prefixEnd_6737670 := by exact prefixLift 6737670
  have htrace : WordTrace (prefixWord ++ tailWord_6737670) baseStart_6737670 baseEnd_6737670 := by
    simpa [prefixWord, tailWord_6737670, baseEnd_6737670] using wordTrace_append hprefix tailTrace_6737670
  have hstable : (prefixWord ++ tailWord_6737670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737670).length < 2 ^ (prefixWord ++ tailWord_6737670).sum := by decide
  have hdescent : baseEnd_6737670 < baseStart_6737670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737698 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_6737698 : Nat := 118140960795 + 6737698 * 2 ^ 59
def prefixEnd_6737698 : Nat := 4983230072969 + 3 ^ 40 * 6737698 * 2
def baseEnd_6737698 : Nat := 1153225859612361653096299

theorem tailTrace_6737698 : CollatzResearch.WordTrace tailWord_6737698 prefixEnd_6737698 1153225859612361653096299 := by
  unfold tailWord_6737698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61436008686119582012757437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163829356496318885367353165 61436008686119582012757437)
  ·
    refine ⟨23038503257294843254784039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61436008686119582012757437 23038503257294843254784039)
    ·
      refine ⟨34557754885942264882176059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23038503257294843254784039 34557754885942264882176059)
      ·
        refine ⟨51836632328913397323264089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34557754885942264882176059 51836632328913397323264089)
        ·
          refine ⟨38877474246685047992448067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51836632328913397323264089 38877474246685047992448067)
          ·
            refine ⟨58316211370027571988672101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38877474246685047992448067 58316211370027571988672101)
            ·
              refine ⟨10934289631880169747876019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58316211370027571988672101 10934289631880169747876019)
              ·
                refine ⟨16401434447820254621814029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934289631880169747876019 16401434447820254621814029)
                ·
                  refine ⟨6150537917932595483180261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16401434447820254621814029 6150537917932595483180261)
                  ·
                    refine ⟨1153225859612361653096299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150537917932595483180261 1153225859612361653096299)
                    ·
                      rfl

theorem cell23_6737698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_6737698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737698 prefixEnd_6737698 := by exact prefixLift 6737698
  have htrace : WordTrace (prefixWord ++ tailWord_6737698) baseStart_6737698 baseEnd_6737698 := by
    simpa [prefixWord, tailWord_6737698, baseEnd_6737698] using wordTrace_append hprefix tailTrace_6737698
  have hstable : (prefixWord ++ tailWord_6737698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737698).length < 2 ^ (prefixWord ++ tailWord_6737698).sum := by decide
  have hdescent : baseEnd_6737698 < baseStart_6737698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737761 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6737761 : Nat := 118140960795 + 6737761 * 2 ^ 59
def prefixEnd_6737761 : Nat := 4983230072969 + 3 ^ 40 * 6737761 * 2
def baseEnd_6737761 : Nat := 3459709928118318212801107

theorem tailTrace_6737761 : CollatzResearch.WordTrace tailWord_6737761 prefixEnd_6737761 3459709928118318212801107 := by
  unfold tailWord_6737761
  simp only [CollatzResearch.WordTrace]
  refine ⟨245746332543250089810573137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163830888362166726540382091 245746332543250089810573137)
  ·
    refine ⟨184309749407437567357929853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245746332543250089810573137 184309749407437567357929853)
    ·
      refine ⟨69116156027789087759223695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184309749407437567357929853 69116156027789087759223695)
      ·
        refine ⟨103674234041683631638835543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69116156027789087759223695 103674234041683631638835543)
        ·
          refine ⟨155511351062525447458253315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103674234041683631638835543 155511351062525447458253315)
          ·
            refine ⟨233267026593788171187379973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155511351062525447458253315 233267026593788171187379973)
            ·
              refine ⟨43737567486335282097633745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233267026593788171187379973 43737567486335282097633745)
              ·
                refine ⟨32803175614751461573225309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43737567486335282097633745 32803175614751461573225309)
                ·
                  refine ⟨12301190855531798089959491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32803175614751461573225309 12301190855531798089959491)
                  ·
                    refine ⟨18451786283297697134939237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12301190855531798089959491 18451786283297697134939237)
                    ·
                      refine ⟨3459709928118318212801107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18451786283297697134939237 3459709928118318212801107)
                      ·
                        rfl

theorem cell23_6737761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6737761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737761 prefixEnd_6737761 := by exact prefixLift 6737761
  have htrace : WordTrace (prefixWord ++ tailWord_6737761) baseStart_6737761 baseEnd_6737761 := by
    simpa [prefixWord, tailWord_6737761, baseEnd_6737761] using wordTrace_append hprefix tailTrace_6737761
  have hstable : (prefixWord ++ tailWord_6737761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737761).length < 2 ^ (prefixWord ++ tailWord_6737761).sum := by decide
  have hdescent : baseEnd_6737761 < baseStart_6737761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737795 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 1, 1, 4]
def baseStart_6737795 : Nat := 118140960795 + 6737795 * 2 ^ 59
def prefixEnd_6737795 : Nat := 4983230072969 + 3 ^ 40 * 6737795 * 2
def baseEnd_6737795 : Nat := 3459727386460571079775951

theorem tailTrace_6737795 : CollatzResearch.WordTrace tailWord_6737795 prefixEnd_6737795 3459727386460571079775951 := by
  unfold tailWord_6737795
  simp only [CollatzResearch.WordTrace]
  refine ⟨245747572625126913617310839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163831715083417942411540559 245747572625126913617310839)
  ·
    refine ⟨368621358937690370425966259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245747572625126913617310839 368621358937690370425966259)
    ·
      refine ⟨552932038406535555638949389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368621358937690370425966259 552932038406535555638949389)
      ·
        refine ⟨207349514402450833364606021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552932038406535555638949389 207349514402450833364606021)
        ·
          refine ⟨38878033950459531255863629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207349514402450833364606021 38878033950459531255863629)
          ·
            refine ⟨14579262731422324220948861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38878033950459531255863629 14579262731422324220948861)
            ·
              refine ⟨5467223524283371582855823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14579262731422324220948861 5467223524283371582855823)
              ·
                refine ⟨8200835286425057374283735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467223524283371582855823 8200835286425057374283735)
                ·
                  refine ⟨12301252929637586061425603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200835286425057374283735 12301252929637586061425603)
                  ·
                    refine ⟨18451879394456379092138405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12301252929637586061425603 18451879394456379092138405)
                    ·
                      refine ⟨3459727386460571079775951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18451879394456379092138405 3459727386460571079775951)
                      ·
                        rfl

theorem cell23_6737795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_6737795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737795 prefixEnd_6737795 := by exact prefixLift 6737795
  have htrace : WordTrace (prefixWord ++ tailWord_6737795) baseStart_6737795 baseEnd_6737795 := by
    simpa [prefixWord, tailWord_6737795, baseEnd_6737795] using wordTrace_append hprefix tailTrace_6737795
  have hstable : (prefixWord ++ tailWord_6737795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737795).length < 2 ^ (prefixWord ++ tailWord_6737795).sum := by decide
  have hdescent : baseEnd_6737795 < baseStart_6737795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737818 : List Nat := [3, 1, 1, 4, 2, 3, 1, 8]
def baseStart_6737818 : Nat := 118140960795 + 6737818 * 2 ^ 59
def prefixEnd_6737818 : Nat := 4983230072969 + 3 ^ 40 * 6737818 * 2
def baseEnd_6737818 : Nat := 128138488759837944066235

theorem tailTrace_6737818 : CollatzResearch.WordTrace tailWord_6737818 prefixEnd_6737818 128138488759837944066235 := by
  unfold tailWord_6737818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61437102876010897136349527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163832274336029059030265405 61437102876010897136349527)
  ·
    refine ⟨92155654314016345704524291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61437102876010897136349527 92155654314016345704524291)
    ·
      refine ⟨138233481471024518556786437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92155654314016345704524291 138233481471024518556786437)
      ·
        refine ⟨25918777775817097229397457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138233481471024518556786437 25918777775817097229397457)
        ·
          refine ⟨19439083331862822922048093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25918777775817097229397457 19439083331862822922048093)
          ·
            refine ⟨7289656249448558595768035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19439083331862822922048093 7289656249448558595768035)
            ·
              refine ⟨10934484374172837893652053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7289656249448558595768035 10934484374172837893652053)
              ·
                refine ⟨128138488759837944066235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10934484374172837893652053 128138488759837944066235)
                ·
                  rfl

theorem cell23_6737818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_6737818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737818 prefixEnd_6737818 := by exact prefixLift 6737818
  have htrace : WordTrace (prefixWord ++ tailWord_6737818) baseStart_6737818 baseEnd_6737818 := by
    simpa [prefixWord, tailWord_6737818, baseEnd_6737818] using wordTrace_append hprefix tailTrace_6737818
  have hstable : (prefixWord ++ tailWord_6737818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737818).length < 2 ^ (prefixWord ++ tailWord_6737818).sum := by decide
  have hdescent : baseEnd_6737818 < baseStart_6737818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737822 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6737822 : Nat := 118140960795 + 6737822 * 2 ^ 59
def prefixEnd_6737822 : Nat := 4983230072969 + 3 ^ 40 * 6737822 * 2
def baseEnd_6737822 : Nat := 1153247083479414158046109

theorem tailTrace_6737822 : CollatzResearch.WordTrace tailWord_6737822 prefixEnd_6737822 1153247083479414158046109 := by
  unfold tailWord_6737822
  simp only [CollatzResearch.WordTrace]
  refine ⟨30718569674503637153567965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163832371597352731485695813 30718569674503637153567965)
  ·
    refine ⟨11519463627938863932587987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30718569674503637153567965 11519463627938863932587987)
    ·
      refine ⟨17279195441908295898881981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11519463627938863932587987 17279195441908295898881981)
      ·
        refine ⟨6479698290715610962080743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17279195441908295898881981 6479698290715610962080743)
        ·
          refine ⟨9719547436073416443121115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6479698290715610962080743 9719547436073416443121115)
          ·
            refine ⟨14579321154110124664681673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719547436073416443121115 14579321154110124664681673)
            ·
              refine ⟨10934490865582593498511255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14579321154110124664681673 10934490865582593498511255)
              ·
                refine ⟨16401736298373890247766883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934490865582593498511255 16401736298373890247766883)
                ·
                  refine ⟨24602604447560835371650325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16401736298373890247766883 24602604447560835371650325)
                  ·
                    refine ⟨1153247083479414158046109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24602604447560835371650325 1153247083479414158046109)
                    ·
                      rfl

theorem cell23_6737822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6737822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737822 prefixEnd_6737822 := by exact prefixLift 6737822
  have htrace : WordTrace (prefixWord ++ tailWord_6737822) baseStart_6737822 baseEnd_6737822 := by
    simpa [prefixWord, tailWord_6737822, baseEnd_6737822] using wordTrace_append hprefix tailTrace_6737822
  have hstable : (prefixWord ++ tailWord_6737822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737822).length < 2 ^ (prefixWord ++ tailWord_6737822).sum := by decide
  have hdescent : baseEnd_6737822 < baseStart_6737822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737825 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6737825 : Nat := 118140960795 + 6737825 * 2 ^ 59
def prefixEnd_6737825 : Nat := 4983230072969 + 3 ^ 40 * 6737825 * 2
def baseEnd_6737825 : Nat := 3459742790880205962400813

theorem tailTrace_6737825 : CollatzResearch.WordTrace tailWord_6737825 prefixEnd_6737825 3459742790880205962400813 := by
  unfold tailWord_6737825
  simp only [CollatzResearch.WordTrace]
  refine ⟨245748666815018228740902929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163832444543345485827268619 245748666815018228740902929)
  ·
    refine ⟨184311500111263671555677197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245748666815018228740902929 184311500111263671555677197)
    ·
      refine ⟨69116812541723876833378949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184311500111263671555677197 69116812541723876833378949)
      ·
        refine ⟨12959402351573226906258553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69116812541723876833378949 12959402351573226906258553)
        ·
          refine ⟨9719551763679920179693915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12959402351573226906258553 9719551763679920179693915)
          ·
            refine ⟨14579327645519880269540873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719551763679920179693915 14579327645519880269540873)
            ·
              refine ⟨10934495734139910202155655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14579327645519880269540873 10934495734139910202155655)
              ·
                refine ⟨16401743601209865303233483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934495734139910202155655 16401743601209865303233483)
                ·
                  refine ⟨24602615401814797954850225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16401743601209865303233483 24602615401814797954850225)
                  ·
                    refine ⟨18451961551361098466137669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24602615401814797954850225 18451961551361098466137669)
                    ·
                      refine ⟨3459742790880205962400813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18451961551361098466137669 3459742790880205962400813)
                      ·
                        rfl

theorem cell23_6737825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6737825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737825 prefixEnd_6737825 := by exact prefixLift 6737825
  have htrace : WordTrace (prefixWord ++ tailWord_6737825) baseStart_6737825 baseEnd_6737825 := by
    simpa [prefixWord, tailWord_6737825, baseEnd_6737825] using wordTrace_append hprefix tailTrace_6737825
  have hstable : (prefixWord ++ tailWord_6737825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737825).length < 2 ^ (prefixWord ++ tailWord_6737825).sum := by decide
  have hdescent : baseEnd_6737825 < baseStart_6737825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737828 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_6737828 : Nat := 118140960795 + 6737828 * 2 ^ 59
def prefixEnd_6737828 : Nat := 4983230072969 + 3 ^ 40 * 6737828 * 2
def baseEnd_6737828 : Nat := 3459744331322169450663299

theorem tailTrace_6737828 : CollatzResearch.WordTrace tailWord_6737828 prefixEnd_6737828 3459744331322169450663299 := by
  unfold tailWord_6737828
  simp only [CollatzResearch.WordTrace]
  refine ⟨122874388117003680126631069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163832517489338240168841425 122874388117003680126631069)
  ·
    refine ⟨46077895543876380047486651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122874388117003680126631069 46077895543876380047486651)
    ·
      refine ⟨69116843315814570071229977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46077895543876380047486651 69116843315814570071229977)
      ·
        refine ⟨51837632486860927553422483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69116843315814570071229977 51837632486860927553422483)
        ·
          refine ⟨77756448730291391330133725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51837632486860927553422483 77756448730291391330133725)
          ·
            refine ⟨29158668273859271748800147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77756448730291391330133725 29158668273859271748800147)
            ·
              refine ⟨43738002410788907623200221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29158668273859271748800147 43738002410788907623200221)
              ·
                refine ⟨16401750904045840358700083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43738002410788907623200221 16401750904045840358700083)
                ·
                  refine ⟨24602626356068760538050125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16401750904045840358700083 24602626356068760538050125)
                  ·
                    refine ⟨9225984883525785201768797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24602626356068760538050125 9225984883525785201768797)
                    ·
                      refine ⟨3459744331322169450663299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9225984883525785201768797 3459744331322169450663299)
                      ·
                        rfl

theorem cell23_6737828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_6737828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737828 prefixEnd_6737828 := by exact prefixLift 6737828
  have htrace : WordTrace (prefixWord ++ tailWord_6737828) baseStart_6737828 baseEnd_6737828 := by
    simpa [prefixWord, tailWord_6737828, baseEnd_6737828] using wordTrace_append hprefix tailTrace_6737828
  have hstable : (prefixWord ++ tailWord_6737828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737828).length < 2 ^ (prefixWord ++ tailWord_6737828).sum := by decide
  have hdescent : baseEnd_6737828 < baseStart_6737828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737855 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 1, 3, 2]
def baseStart_6737855 : Nat := 118140960795 + 6737855 * 2 ^ 59
def prefixEnd_6737855 : Nat := 4983230072969 + 3 ^ 40 * 6737855 * 2
def baseEnd_6737855 : Nat := 3459758195299840845025675

theorem tailTrace_6737855 : CollatzResearch.WordTrace tailWord_6737855 prefixEnd_6737855 3459758195299840845025675 := by
  unfold tailWord_6737855
  simp only [CollatzResearch.WordTrace]
  refine ⟨245749761004909543864495019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163833174003273029242996679 245749761004909543864495019)
  ·
    refine ⟨368624641507364315796742529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245749761004909543864495019 368624641507364315796742529)
    ·
      refine ⟨276468481130523236847556897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368624641507364315796742529 276468481130523236847556897)
      ·
        refine ⟨207351360847892427635667673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276468481130523236847556897 207351360847892427635667673)
        ·
          refine ⟨155513520635919320726750755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207351360847892427635667673 155513520635919320726750755)
          ·
            refine ⟨233270280953878981090126133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155513520635919320726750755 233270280953878981090126133)
            ·
              refine ⟨21869088839426154477199325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233270280953878981090126133 21869088839426154477199325)
              ·
                refine ⟨8200908314784807928949747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21869088839426154477199325 8200908314784807928949747)
                ·
                  refine ⟨12301362472177211893424621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200908314784807928949747 12301362472177211893424621)
                  ·
                    refine ⟨4613010927066454460034233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12301362472177211893424621 4613010927066454460034233)
                    ·
                      refine ⟨3459758195299840845025675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613010927066454460034233 3459758195299840845025675)
                      ·
                        rfl

theorem cell23_6737855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_6737855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737855 prefixEnd_6737855 := by exact prefixLift 6737855
  have htrace : WordTrace (prefixWord ++ tailWord_6737855) baseStart_6737855 baseEnd_6737855 := by
    simpa [prefixWord, tailWord_6737855, baseEnd_6737855] using wordTrace_append hprefix tailTrace_6737855
  have hstable : (prefixWord ++ tailWord_6737855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737855).length < 2 ^ (prefixWord ++ tailWord_6737855).sum := by decide
  have hdescent : baseEnd_6737855 < baseStart_6737855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737902 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_6737902 : Nat := 118140960795 + 6737902 * 2 ^ 59
def prefixEnd_6737902 : Nat := 4983230072969 + 3 ^ 40 * 6737902 * 2
def baseEnd_6737902 : Nat := 3459782328890602161137959

theorem tailTrace_6737902 : CollatzResearch.WordTrace tailWord_6737902 prefixEnd_6737902 3459782328890602161137959 := by
  unfold tailWord_6737902
  simp only [CollatzResearch.WordTrace]
  refine ⟨30718934404467408861431995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163834316823826180594303973 30718934404467408861431995)
  ·
    refine ⟨46078401606701113292147993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30718934404467408861431995 46078401606701113292147993)
    ·
      refine ⟨34558801205025834969110995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46078401606701113292147993 34558801205025834969110995)
      ·
        refine ⟨51838201807538752453666493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34558801205025834969110995 51838201807538752453666493)
        ·
          refine ⟨19439325677827032170124935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51838201807538752453666493 19439325677827032170124935)
          ·
            refine ⟨29158988516740548255187403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19439325677827032170124935 29158988516740548255187403)
            ·
              refine ⟨43738482775110822382781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29158988516740548255187403 43738482775110822382781105)
              ·
                refine ⟨32803862081333116787085829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43738482775110822382781105 32803862081333116787085829)
                ·
                  refine ⟨6150724140249959397578593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32803862081333116787085829 6150724140249959397578593)
                  ·
                    refine ⟨4613043105187469548183945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6150724140249959397578593 4613043105187469548183945)
                    ·
                      refine ⟨3459782328890602161137959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613043105187469548183945 3459782328890602161137959)
                      ·
                        rfl

theorem cell23_6737902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_6737902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737902 prefixEnd_6737902 := by exact prefixLift 6737902
  have htrace : WordTrace (prefixWord ++ tailWord_6737902) baseStart_6737902 baseEnd_6737902 := by
    simpa [prefixWord, tailWord_6737902, baseEnd_6737902] using wordTrace_append hprefix tailTrace_6737902
  have hstable : (prefixWord ++ tailWord_6737902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737902).length < 2 ^ (prefixWord ++ tailWord_6737902).sum := by decide
  have hdescent : baseEnd_6737902 < baseStart_6737902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6737978 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_6737978 : Nat := 118140960795 + 6737978 * 2 ^ 59
def prefixEnd_6737978 : Nat := 4983230072969 + 3 ^ 40 * 6737978 * 2
def baseEnd_6737978 : Nat := 3459821353420343863787609

theorem tailTrace_6737978 : CollatzResearch.WordTrace tailWord_6737978 prefixEnd_6737978 3459821353420343863787609 := by
  unfold tailWord_6737978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61438561795865983967805647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163836164788975957247481725 61438561795865983967805647)
  ·
    refine ⟨92157842693798975951708471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61438561795865983967805647 92157842693798975951708471)
    ·
      refine ⟨138236764040698463927562707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92157842693798975951708471 138236764040698463927562707)
      ·
        refine ⟨207355146061047695891344061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138236764040698463927562707 207355146061047695891344061)
        ·
          refine ⟨77758179772892885959254023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207355146061047695891344061 77758179772892885959254023)
          ·
            refine ⟨116637269659339328938881035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77758179772892885959254023 116637269659339328938881035)
            ·
              refine ⟨174955904489008993408321553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116637269659339328938881035 174955904489008993408321553)
              ·
                refine ⟨131216928366756745056241165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174955904489008993408321553 131216928366756745056241165)
                ·
                  refine ⟨49206348137533779396090437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131216928366756745056241165 49206348137533779396090437)
                  ·
                    refine ⟨9226190275787583636766957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49206348137533779396090437 9226190275787583636766957)
                    ·
                      refine ⟨3459821353420343863787609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226190275787583636766957 3459821353420343863787609)
                      ·
                        rfl

theorem cell23_6737978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_6737978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6737978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6737978 prefixEnd_6737978 := by exact prefixLift 6737978
  have htrace : WordTrace (prefixWord ++ tailWord_6737978) baseStart_6737978 baseEnd_6737978 := by
    simpa [prefixWord, tailWord_6737978, baseEnd_6737978] using wordTrace_append hprefix tailTrace_6737978
  have hstable : (prefixWord ++ tailWord_6737978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6737978).length < 2 ^ (prefixWord ++ tailWord_6737978).sum := by decide
  have hdescent : baseEnd_6737978 < baseStart_6737978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6737978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738002 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_6738002 : Nat := 118140960795 + 6738002 * 2 ^ 59
def prefixEnd_6738002 : Nat := 4983230072969 + 3 ^ 40 * 6738002 * 2
def baseEnd_6738002 : Nat := 1153277892318683923295833

theorem tailTrace_6738002 : CollatzResearch.WordTrace tailWord_6738002 prefixEnd_6738002 1153277892318683923295833 := by
  unfold tailWord_6738002
  simp only [CollatzResearch.WordTrace]
  refine ⟨61438780633844246992524065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163836748356917991980064173 61438780633844246992524065)
  ·
    refine ⟨46079085475383185244393049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61438780633844246992524065 46079085475383185244393049)
    ·
      refine ⟨34559314106537388933294787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46079085475383185244393049 34559314106537388933294787)
      ·
        refine ⟨51838971159806083399942181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34559314106537388933294787 51838971159806083399942181)
        ·
          refine ⟨9719807092463640637489159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51838971159806083399942181 9719807092463640637489159)
          ·
            refine ⟨14579710638695460956233739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719807092463640637489159 14579710638695460956233739)
            ·
              refine ⟨21869565958043191434350609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14579710638695460956233739 21869565958043191434350609)
              ·
                refine ⟨16402174468532393575762957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21869565958043191434350609 16402174468532393575762957)
                ·
                  refine ⟨6150815425699647590911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16402174468532393575762957 6150815425699647590911109)
                  ·
                    refine ⟨1153277892318683923295833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6150815425699647590911109 1153277892318683923295833)
                    ·
                      rfl

theorem cell23_6738002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_6738002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738002 prefixEnd_6738002 := by exact prefixLift 6738002
  have htrace : WordTrace (prefixWord ++ tailWord_6738002) baseStart_6738002 baseEnd_6738002 := by
    simpa [prefixWord, tailWord_6738002, baseEnd_6738002] using wordTrace_append hprefix tailTrace_6738002
  have hstable : (prefixWord ++ tailWord_6738002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738002).length < 2 ^ (prefixWord ++ tailWord_6738002).sum := by decide
  have hdescent : baseEnd_6738002 < baseStart_6738002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738012 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6738012 : Nat := 118140960795 + 6738012 * 2 ^ 59
def prefixEnd_6738012 : Nat := 4983230072969 + 3 ^ 40 * 6738012 * 2
def baseEnd_6738012 : Nat := 3459838811762596730762453

theorem tailTrace_6738012 : CollatzResearch.WordTrace tailWord_6738012 prefixEnd_6738012 3459838811762596730762453 := by
  unfold tailWord_6738012
  simp only [CollatzResearch.WordTrace]
  refine ⟨122877743632670379838980145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163836991510227173118640193 122877743632670379838980145)
  ·
    refine ⟨92158307724502784879235109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122877743632670379838980145 92158307724502784879235109)
    ·
      refine ⟨17279682698344272164856583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92158307724502784879235109 17279682698344272164856583)
      ·
        refine ⟨25919524047516408247284875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17279682698344272164856583 25919524047516408247284875)
        ·
          refine ⟨38879286071274612370927313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25919524047516408247284875 38879286071274612370927313)
          ·
            refine ⟨29159464553455959278195485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38879286071274612370927313 29159464553455959278195485)
            ·
              refine ⟨10934799207545984729323307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29159464553455959278195485 10934799207545984729323307)
              ·
                refine ⟨16402198811318977093984961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934799207545984729323307 16402198811318977093984961)
                ·
                  refine ⟨12301649108489232820488721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16402198811318977093984961 12301649108489232820488721)
                  ·
                    refine ⟨9226236831366924615366541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12301649108489232820488721 9226236831366924615366541)
                    ·
                      refine ⟨3459838811762596730762453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226236831366924615366541 3459838811762596730762453)
                      ·
                        rfl

theorem cell23_6738012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6738012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738012 prefixEnd_6738012 := by exact prefixLift 6738012
  have htrace : WordTrace (prefixWord ++ tailWord_6738012) baseStart_6738012 baseEnd_6738012 := by
    simpa [prefixWord, tailWord_6738012, baseEnd_6738012] using wordTrace_append hprefix tailTrace_6738012
  have hstable : (prefixWord ++ tailWord_6738012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738012).length < 2 ^ (prefixWord ++ tailWord_6738012).sum := by decide
  have hdescent : baseEnd_6738012 < baseStart_6738012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738025 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 3]
def baseStart_6738025 : Nat := 118140960795 + 6738025 * 2 ^ 59
def prefixEnd_6738025 : Nat := 4983230072969 + 3 ^ 40 * 6738025 * 2
def baseEnd_6738025 : Nat := 3459845487011105179899893

theorem tailTrace_6738025 : CollatzResearch.WordTrace tailWord_6738025 prefixEnd_6738025 3459845487011105179899893 := by
  unfold tailWord_6738025
  simp only [CollatzResearch.WordTrace]
  refine ⟨245755961414293662898183529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163837307609529108598789019 245755961414293662898183529)
  ·
    refine ⟨184316971060720247173637647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245755961414293662898183529 184316971060720247173637647)
    ·
      refine ⟨276475456591080370760456471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184316971060720247173637647 276475456591080370760456471)
      ·
        refine ⟨414713184886620556140684707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276475456591080370760456471 414713184886620556140684707)
        ·
          refine ⟨622069777329930834211027061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414713184886620556140684707 622069777329930834211027061)
          ·
            refine ⟨58319041624681015707283787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 622069777329930834211027061 58319041624681015707283787)
            ·
              refine ⟨87478562437021523560925681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58319041624681015707283787 87478562437021523560925681)
              ·
                refine ⟨65608921827766142670694261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87478562437021523560925681 65608921827766142670694261)
                ·
                  refine ⟨6150836421353075875377587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65608921827766142670694261 6150836421353075875377587)
                  ·
                    refine ⟨9226254632029613813066381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150836421353075875377587 9226254632029613813066381)
                    ·
                      refine ⟨3459845487011105179899893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226254632029613813066381 3459845487011105179899893)
                      ·
                        rfl

theorem cell23_6738025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 3].length) (baseStart_6738025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738025 prefixEnd_6738025 := by exact prefixLift 6738025
  have htrace : WordTrace (prefixWord ++ tailWord_6738025) baseStart_6738025 baseEnd_6738025 := by
    simpa [prefixWord, tailWord_6738025, baseEnd_6738025] using wordTrace_append hprefix tailTrace_6738025
  have hstable : (prefixWord ++ tailWord_6738025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738025).length < 2 ^ (prefixWord ++ tailWord_6738025).sum := by decide
  have hdescent : baseEnd_6738025 < baseStart_6738025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738085 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_6738085 : Nat := 118140960795 + 6738085 * 2 ^ 59
def prefixEnd_6738085 : Nat := 4983230072969 + 3 ^ 40 * 6738085 * 2
def baseEnd_6738085 : Nat := 3459876295850374945149617

theorem tailTrace_6738085 : CollatzResearch.WordTrace tailWord_6738085 prefixEnd_6738085 3459876295850374945149617 := by
  unfold tailWord_6738085
  simp only [CollatzResearch.WordTrace]
  refine ⟨245758149794076293145367709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163838766529384195430245139 245758149794076293145367709)
  ·
    refine ⟨92159306172778609929512891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245758149794076293145367709 92159306172778609929512891)
    ·
      refine ⟨138238959259167914894269337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92159306172778609929512891 138238959259167914894269337)
      ·
        refine ⟨103679219444375936170702003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138238959259167914894269337 103679219444375936170702003)
        ·
          refine ⟨155518829166563904256053005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103679219444375936170702003 155518829166563904256053005)
          ·
            refine ⟨58319560937461464096019877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155518829166563904256053005 58319560937461464096019877)
            ·
              refine ⟨10934917675774024518003727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58319560937461464096019877 10934917675774024518003727)
              ·
                refine ⟨16402376513661036777005591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934917675774024518003727 16402376513661036777005591)
                ·
                  refine ⟨24603564770491555165508387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16402376513661036777005591 24603564770491555165508387)
                  ·
                    refine ⟨36905347155737332748262581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24603564770491555165508387 36905347155737332748262581)
                    ·
                      refine ⟨3459876295850374945149617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36905347155737332748262581 3459876295850374945149617)
                      ·
                        rfl

theorem cell23_6738085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_6738085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738085 prefixEnd_6738085 := by exact prefixLift 6738085
  have htrace : WordTrace (prefixWord ++ tailWord_6738085) baseStart_6738085 baseEnd_6738085 := by
    simpa [prefixWord, tailWord_6738085, baseEnd_6738085] using wordTrace_append hprefix tailTrace_6738085
  have hstable : (prefixWord ++ tailWord_6738085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738085).length < 2 ^ (prefixWord ++ tailWord_6738085).sum := by decide
  have hdescent : baseEnd_6738085 < baseStart_6738085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738093 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_6738093 : Nat := 118140960795 + 6738093 * 2 ^ 59
def prefixEnd_6738093 : Nat := 4983230072969 + 3 ^ 40 * 6738093 * 2
def baseEnd_6738093 : Nat := 3459880403695610913849581

theorem tailTrace_6738093 : CollatzResearch.WordTrace tailWord_6738093 prefixEnd_6738093 3459880403695610913849581 := by
  unfold tailWord_6738093
  simp only [CollatzResearch.WordTrace]
  refine ⟨245758441578047310511658933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163838961052031540341105955 245758441578047310511658933)
  ·
    refine ⟨23039853897941935360468025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 245758441578047310511658933 23039853897941935360468025)
    ·
      refine ⟨17279890423456451520351019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23039853897941935360468025 17279890423456451520351019)
      ·
        refine ⟨25919835635184677280526529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17279890423456451520351019 25919835635184677280526529)
        ·
          refine ⟨19439876726388507960394897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25919835635184677280526529 19439876726388507960394897)
          ·
            refine ⟨14579907544791380970296173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19439876726388507960394897 14579907544791380970296173)
            ·
              refine ⟨5467465329296767863861065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14579907544791380970296173 5467465329296767863861065)
              ·
                refine ⟨4100598996972575897895799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467465329296767863861065 4100598996972575897895799)
                ·
                  refine ⟨6150898495458863846843699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100598996972575897895799 6150898495458863846843699)
                  ·
                    refine ⟨9226347743188295770265549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150898495458863846843699 9226347743188295770265549)
                    ·
                      refine ⟨3459880403695610913849581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226347743188295770265549 3459880403695610913849581)
                      ·
                        rfl

theorem cell23_6738093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_6738093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738093 prefixEnd_6738093 := by exact prefixLift 6738093
  have htrace : WordTrace (prefixWord ++ tailWord_6738093) baseStart_6738093 baseEnd_6738093 := by
    simpa [prefixWord, tailWord_6738093, baseEnd_6738093] using wordTrace_append hprefix tailTrace_6738093
  have hstable : (prefixWord ++ tailWord_6738093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738093).length < 2 ^ (prefixWord ++ tailWord_6738093).sum := by decide
  have hdescent : baseEnd_6738093 < baseStart_6738093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738100 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 6]
def baseStart_6738100 : Nat := 118140960795 + 6738100 * 2 ^ 59
def prefixEnd_6738100 : Nat := 4983230072969 + 3 ^ 40 * 6738100 * 2
def baseEnd_6738100 : Nat := 384431555340021376273561

theorem tailTrace_6738100 : CollatzResearch.WordTrace tailWord_6738100 prefixEnd_6738100 384431555340021376273561 := by
  unfold tailWord_6738100
  simp only [CollatzResearch.WordTrace]
  refine ⟨122879348444510975353581877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163839131259347967138109169 122879348444510975353581877)
  ·
    refine ⟨11519938916672903939398301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122879348444510975353581877 11519938916672903939398301)
    ·
      refine ⟨4319977093752338977274363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11519938916672903939398301 4319977093752338977274363)
      ·
        refine ⟨6479965640628508465911545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319977093752338977274363 6479965640628508465911545)
        ·
          refine ⟨4859974230471381349433659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479965640628508465911545 4859974230471381349433659)
          ·
            refine ⟨7289961345707072024150489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859974230471381349433659 7289961345707072024150489)
            ·
              refine ⟨5467471009280304018112867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289961345707072024150489 5467471009280304018112867)
              ·
                refine ⟨8201206513920456027169301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467471009280304018112867 8201206513920456027169301)
                ·
                  refine ⟨384431555340021376273561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8201206513920456027169301 384431555340021376273561)
                  ·
                    rfl

theorem cell23_6738100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_6738100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738100 prefixEnd_6738100 := by exact prefixLift 6738100
  have htrace : WordTrace (prefixWord ++ tailWord_6738100) baseStart_6738100 baseEnd_6738100 := by
    simpa [prefixWord, tailWord_6738100, baseEnd_6738100] using wordTrace_append hprefix tailTrace_6738100
  have hstable : (prefixWord ++ tailWord_6738100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738100).length < 2 ^ (prefixWord ++ tailWord_6738100).sum := by decide
  have hdescent : baseEnd_6738100 < baseStart_6738100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738149 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6738149 : Nat := 118140960795 + 6738149 * 2 ^ 59
def prefixEnd_6738149 : Nat := 4983230072969 + 3 ^ 40 * 6738149 * 2
def baseEnd_6738149 : Nat := 3459909158612262694749323

theorem tailTrace_6738149 : CollatzResearch.WordTrace tailWord_6738149 prefixEnd_6738149 3459909158612262694749323 := by
  unfold tailWord_6738149
  simp only [CollatzResearch.WordTrace]
  refine ⟨245760484065844432075697501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163840322710562954717131667 245760484065844432075697501)
  ·
    refine ⟨92160181524691662028386563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245760484065844432075697501 92160181524691662028386563)
    ·
      refine ⟨138240272287037493042579845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92160181524691662028386563 138240272287037493042579845)
      ·
        refine ⟨25920051053819529945483721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138240272287037493042579845 25920051053819529945483721)
        ·
          refine ⟨19440038290364647459112791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25920051053819529945483721 19440038290364647459112791)
          ·
            refine ⟨29160057435546971188669187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19440038290364647459112791 29160057435546971188669187)
            ·
              refine ⟨43740086153320456783003781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29160057435546971188669187 43740086153320456783003781)
              ·
                refine ⟨8201266153747585646813209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43740086153320456783003781 8201266153747585646813209)
                ·
                  refine ⟨6150949615310689235109907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8201266153747585646813209 6150949615310689235109907)
                  ·
                    refine ⟨9226424422966033852664861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150949615310689235109907 9226424422966033852664861)
                    ·
                      refine ⟨3459909158612262694749323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226424422966033852664861 3459909158612262694749323)
                      ·
                        rfl

theorem cell23_6738149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6738149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738149 prefixEnd_6738149 := by exact prefixLift 6738149
  have htrace : WordTrace (prefixWord ++ tailWord_6738149) baseStart_6738149 baseEnd_6738149 := by
    simpa [prefixWord, tailWord_6738149, baseEnd_6738149] using wordTrace_append hprefix tailTrace_6738149
  have hstable : (prefixWord ++ tailWord_6738149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738149).length < 2 ^ (prefixWord ++ tailWord_6738149).sum := by decide
  have hdescent : baseEnd_6738149 < baseStart_6738149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738175 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_6738175 : Nat := 118140960795 + 6738175 * 2 ^ 59
def prefixEnd_6738175 : Nat := 4983230072969 + 3 ^ 40 * 6738175 * 2
def baseEnd_6738175 : Nat := 3459922509109279593024203

theorem tailTrace_6738175 : CollatzResearch.WordTrace tailWord_6738175 prefixEnd_6738175 3459922509109279593024203 := by
  unfold tailWord_6738175
  simp only [CollatzResearch.WordTrace]
  refine ⟨245761432363750238516143979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163840954909166825677429319 245761432363750238516143979)
  ·
    refine ⟨368642148545625357774215969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245761432363750238516143979 368642148545625357774215969)
    ·
      refine ⟨276481611409219018330661977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368642148545625357774215969 276481611409219018330661977)
      ·
        refine ⟨207361208556914263747996483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276481611409219018330661977 207361208556914263747996483)
        ·
          refine ⟨311041812835371395621994725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207361208556914263747996483 311041812835371395621994725)
          ·
            refine ⟨58320339906632136679124011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311041812835371395621994725 58320339906632136679124011)
            ·
              refine ⟨87480509859948205018686017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58320339906632136679124011 87480509859948205018686017)
              ·
                refine ⟨65610382394961153764014513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87480509859948205018686017 65610382394961153764014513)
                ·
                  refine ⟨49207786796220865323010885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65610382394961153764014513 49207786796220865323010885)
                  ·
                    refine ⟨9226460024291412248064541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49207786796220865323010885 9226460024291412248064541)
                    ·
                      refine ⟨3459922509109279593024203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226460024291412248064541 3459922509109279593024203)
                      ·
                        rfl

theorem cell23_6738175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_6738175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738175 prefixEnd_6738175 := by exact prefixLift 6738175
  have htrace : WordTrace (prefixWord ++ tailWord_6738175) baseStart_6738175 baseEnd_6738175 := by
    simpa [prefixWord, tailWord_6738175, baseEnd_6738175] using wordTrace_append hprefix tailTrace_6738175
  have hstable : (prefixWord ++ tailWord_6738175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738175).length < 2 ^ (prefixWord ++ tailWord_6738175).sum := by decide
  have hdescent : baseEnd_6738175 < baseStart_6738175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738212 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 7]
def baseStart_6738212 : Nat := 118140960795 + 6738212 * 2 ^ 59
def prefixEnd_6738212 : Nat := 4983230072969 + 3 ^ 40 * 6738212 * 2
def baseEnd_6738212 : Nat := 384437945321499549806837

theorem tailTrace_6738212 : CollatzResearch.WordTrace tailWord_6738212 prefixEnd_6738212 384437945321499549806837 := by
  unfold tailWord_6738212
  simp only [CollatzResearch.WordTrace]
  refine ⟨122881390932308096917620445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163841854576410795890160593 122881390932308096917620445)
  ·
    refine ⟨46080521599615536344107667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122881390932308096917620445 46080521599615536344107667)
    ·
      refine ⟨69120782399423304516161501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46080521599615536344107667 69120782399423304516161501)
      ·
        refine ⟨25920293399783739193560563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69120782399423304516161501 25920293399783739193560563)
        ·
          refine ⟨38880440099675608790340845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25920293399783739193560563 38880440099675608790340845)
          ·
            refine ⟨14580165037378353296377817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38880440099675608790340845 14580165037378353296377817)
            ·
              refine ⟨10935123778033764972283363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580165037378353296377817 10935123778033764972283363)
              ·
                refine ⟨16402685667050647458425045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935123778033764972283363 16402685667050647458425045)
                ·
                  refine ⟨384437945321499549806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16402685667050647458425045 384437945321499549806837)
                  ·
                    rfl

theorem cell23_6738212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_6738212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738212 prefixEnd_6738212 := by exact prefixLift 6738212
  have htrace : WordTrace (prefixWord ++ tailWord_6738212) baseStart_6738212 baseEnd_6738212 := by
    simpa [prefixWord, tailWord_6738212, baseEnd_6738212] using wordTrace_append hprefix tailTrace_6738212
  have hstable : (prefixWord ++ tailWord_6738212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738212).length < 2 ^ (prefixWord ++ tailWord_6738212).sum := by decide
  have hdescent : baseEnd_6738212 < baseStart_6738212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738232 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_6738232 : Nat := 118140960795 + 6738232 * 2 ^ 59
def prefixEnd_6738232 : Nat := 4983230072969 + 3 ^ 40 * 6738232 * 2
def baseEnd_6738232 : Nat := 3459951777506585870011441

theorem tailTrace_6738232 : CollatzResearch.WordTrace tailWord_6738232 prefixEnd_6738232 3459951777506585870011441 := by
  unfold tailWord_6738232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122881755662271868625484475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163842340883029158167312633 122881755662271868625484475)
  ·
    refine ⟨184322633493407802938226713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122881755662271868625484475 184322633493407802938226713)
    ·
      refine ⟨138241975120055852203670035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184322633493407802938226713 138241975120055852203670035)
      ·
        refine ⟨207362962680083778305505053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138241975120055852203670035 207362962680083778305505053)
        ·
          refine ⟨77761111005031416864564395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207362962680083778305505053 77761111005031416864564395)
          ·
            refine ⟨116641666507547125296846593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77761111005031416864564395 116641666507547125296846593)
            ·
              refine ⟨87481249880660343972634945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116641666507547125296846593 87481249880660343972634945)
              ·
                refine ⟨65610937410495257979476209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87481249880660343972634945 65610937410495257979476209)
                ·
                  refine ⟨49208203057871443484607157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65610937410495257979476209 49208203057871443484607157)
                  ·
                    refine ⟨4613269036675447826681921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49208203057871443484607157 4613269036675447826681921)
                    ·
                      refine ⟨3459951777506585870011441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613269036675447826681921 3459951777506585870011441)
                      ·
                        rfl

theorem cell23_6738232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_6738232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738232 prefixEnd_6738232 := by exact prefixLift 6738232
  have htrace : WordTrace (prefixWord ++ tailWord_6738232) baseStart_6738232 baseEnd_6738232 := by
    simpa [prefixWord, tailWord_6738232, baseEnd_6738232] using wordTrace_append hprefix tailTrace_6738232
  have hstable : (prefixWord ++ tailWord_6738232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738232).length < 2 ^ (prefixWord ++ tailWord_6738232).sum := by decide
  have hdescent : baseEnd_6738232 < baseStart_6738232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738299 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3]
def baseStart_6738299 : Nat := 118140960795 + 6738299 * 2 ^ 59
def prefixEnd_6738299 : Nat := 4983230072969 + 3 ^ 40 * 6738299 * 2
def baseEnd_6738299 : Nat := 3459986180710437107873633

theorem tailTrace_6738299 : CollatzResearch.WordTrace tailWord_6738299 prefixEnd_6738299 3459986180710437107873633 := by
  unfold tailWord_6738299
  simp only [CollatzResearch.WordTrace]
  refine ⟨245765955015301007693657951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163843970010200671795771967 245765955015301007693657951)
  ·
    refine ⟨368648932522951511540486927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245765955015301007693657951 368648932522951511540486927)
    ·
      refine ⟨552973398784427267310730391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368648932522951511540486927 552973398784427267310730391)
      ·
        refine ⟨829460098176640900966095587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552973398784427267310730391 829460098176640900966095587)
        ·
          refine ⟨1244190147264961351449143381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829460098176640900966095587 1244190147264961351449143381)
          ·
            refine ⟨14580353288261265837294649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1244190147264961351449143381 14580353288261265837294649)
            ·
              refine ⟨10935264966195949377970987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580353288261265837294649 10935264966195949377970987)
              ·
                refine ⟨16402897449293924066956481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935264966195949377970987 16402897449293924066956481)
                ·
                  refine ⟨12302173086970443050217361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16402897449293924066956481 12302173086970443050217361)
                  ·
                    refine ⟨9226629815227832287663021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12302173086970443050217361 9226629815227832287663021)
                    ·
                      refine ⟨3459986180710437107873633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226629815227832287663021 3459986180710437107873633)
                      ·
                        rfl

theorem cell23_6738299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 3].length) (baseStart_6738299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738299 prefixEnd_6738299 := by exact prefixLift 6738299
  have htrace : WordTrace (prefixWord ++ tailWord_6738299) baseStart_6738299 baseEnd_6738299 := by
    simpa [prefixWord, tailWord_6738299, baseEnd_6738299] using wordTrace_append hprefix tailTrace_6738299
  have hstable : (prefixWord ++ tailWord_6738299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738299).length < 2 ^ (prefixWord ++ tailWord_6738299).sum := by decide
  have hdescent : baseEnd_6738299 < baseStart_6738299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738329 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 3]
def baseStart_6738329 : Nat := 118140960795 + 6738329 * 2 ^ 59
def prefixEnd_6738329 : Nat := 4983230072969 + 3 ^ 40 * 6738329 * 2
def baseEnd_6738329 : Nat := 3460001585130071990498495

theorem tailTrace_6738329 : CollatzResearch.WordTrace tailWord_6738329 prefixEnd_6738329 3460001585130071990498495 := by
  unfold tailWord_6738329
  simp only [CollatzResearch.WordTrace]
  refine ⟨245767049205192322817250041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163844699470128215211500027 245767049205192322817250041)
  ·
    refine ⟨184325286903894242112937531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245767049205192322817250041 184325286903894242112937531)
    ·
      refine ⟨276487930355841363169406297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184325286903894242112937531 276487930355841363169406297)
      ·
        refine ⟨207365947766881022377054723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276487930355841363169406297 207365947766881022377054723)
        ·
          refine ⟨311048921650321533565582085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207365947766881022377054723 311048921650321533565582085)
          ·
            refine ⟨58321672809435287543546641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311048921650321533565582085 58321672809435287543546641)
            ·
              refine ⟨43741254607076465657659981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58321672809435287543546641 43741254607076465657659981)
              ·
                refine ⟨16402970477653674621622493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43741254607076465657659981 16402970477653674621622493)
                ·
                  refine ⟨6151113929120127983108435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16402970477653674621622493 6151113929120127983108435)
                  ·
                    refine ⟨9226670893680191974662653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151113929120127983108435 9226670893680191974662653)
                    ·
                      refine ⟨3460001585130071990498495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226670893680191974662653 3460001585130071990498495)
                      ·
                        rfl

theorem cell23_6738329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_6738329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738329 prefixEnd_6738329 := by exact prefixLift 6738329
  have htrace : WordTrace (prefixWord ++ tailWord_6738329) baseStart_6738329 baseEnd_6738329 := by
    simpa [prefixWord, tailWord_6738329, baseEnd_6738329] using wordTrace_append hprefix tailTrace_6738329
  have hstable : (prefixWord ++ tailWord_6738329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738329).length < 2 ^ (prefixWord ++ tailWord_6738329).sum := by decide
  have hdescent : baseEnd_6738329 < baseStart_6738329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738366 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_6738366 : Nat := 118140960795 + 6738366 * 2 ^ 59
def prefixEnd_6738366 : Nat := 4983230072969 + 3 ^ 40 * 6738366 * 2
def baseEnd_6738366 : Nat := 1153340194638096115245275

theorem tailTrace_6738366 : CollatzResearch.WordTrace tailWord_6738366 prefixEnd_6738366 1153340194638096115245275 := by
  unfold tailWord_6738366
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721049838257284767043369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163845599137372185424231301 30721049838257284767043369)
  ·
    refine ⟨23040787378692963575282527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30721049838257284767043369 23040787378692963575282527)
    ·
      refine ⟨34561181068039445362923791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23040787378692963575282527 34561181068039445362923791)
      ·
        refine ⟨51841771602059168044385687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34561181068039445362923791 51841771602059168044385687)
        ·
          refine ⟨77762657403088752066578531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51841771602059168044385687 77762657403088752066578531)
          ·
            refine ⟨116643986104633128099867797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77762657403088752066578531 116643986104633128099867797)
            ·
              refine ⟨5467686848654677879681303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116643986104633128099867797 5467686848654677879681303)
              ·
                refine ⟨8201530272982016819521955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467686848654677879681303 8201530272982016819521955)
                ·
                  refine ⟨12302295409473025229282933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8201530272982016819521955 12302295409473025229282933)
                  ·
                    refine ⟨1153340194638096115245275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12302295409473025229282933 1153340194638096115245275)
                    ·
                      rfl

theorem cell23_6738366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_6738366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738366 prefixEnd_6738366 := by exact prefixLift 6738366
  have htrace : WordTrace (prefixWord ++ tailWord_6738366) baseStart_6738366 baseEnd_6738366 := by
    simpa [prefixWord, tailWord_6738366, baseEnd_6738366] using wordTrace_append hprefix tailTrace_6738366
  have hstable : (prefixWord ++ tailWord_6738366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738366).length < 2 ^ (prefixWord ++ tailWord_6738366).sum := by decide
  have hdescent : baseEnd_6738366 < baseStart_6738366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738382 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6738382 : Nat := 118140960795 + 6738382 * 2 ^ 59
def prefixEnd_6738382 : Nat := 4983230072969 + 3 ^ 40 * 6738382 * 2
def baseEnd_6738382 : Nat := 3460028799604760283135751

theorem tailTrace_6738382 : CollatzResearch.WordTrace tailWord_6738382 prefixEnd_6738382 3460028799604760283135751 := by
  unfold tailWord_6738382
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721122784250039108616175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163845988182666875245952933 30721122784250039108616175)
  ·
    refine ⟨46081684176375058662924263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721122784250039108616175 46081684176375058662924263)
    ·
      refine ⟨69122526264562587994386395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46081684176375058662924263 69122526264562587994386395)
      ·
        refine ⟨103683789396843881991579593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69122526264562587994386395 103683789396843881991579593)
        ·
          refine ⟨77762842047632911493684695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103683789396843881991579593 77762842047632911493684695)
          ·
            refine ⟨116644263071449367240527043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77762842047632911493684695 116644263071449367240527043)
            ·
              refine ⟨174966394607174050860790565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116644263071449367240527043 174966394607174050860790565)
              ·
                refine ⟨32806198988845134536398231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174966394607174050860790565 32806198988845134536398231)
                ·
                  refine ⟨49209298483267701804597347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32806198988845134536398231 49209298483267701804597347)
                  ·
                    refine ⟨73813947724901552706896021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49209298483267701804597347 73813947724901552706896021)
                    ·
                      refine ⟨3460028799604760283135751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73813947724901552706896021 3460028799604760283135751)
                      ·
                        rfl

theorem cell23_6738382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6738382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738382 prefixEnd_6738382 := by exact prefixLift 6738382
  have htrace : WordTrace (prefixWord ++ tailWord_6738382) baseStart_6738382 baseEnd_6738382 := by
    simpa [prefixWord, tailWord_6738382, baseEnd_6738382] using wordTrace_append hprefix tailTrace_6738382
  have hstable : (prefixWord ++ tailWord_6738382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738382).length < 2 ^ (prefixWord ++ tailWord_6738382).sum := by decide
  have hdescent : baseEnd_6738382 < baseStart_6738382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738389 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6738389 : Nat := 118140960795 + 6738389 * 2 ^ 59
def prefixEnd_6738389 : Nat := 4983230072969 + 3 ^ 40 * 6738389 * 2
def baseEnd_6738389 : Nat := 3460032393969341755748219

theorem tailTrace_6738389 : CollatzResearch.WordTrace tailWord_6738389 prefixEnd_6738389 3460032393969341755748219 := by
  unfold tailWord_6738389
  simp only [CollatzResearch.WordTrace]
  refine ⟨245769237584974953064434221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163846158389983302042956147 245769237584974953064434221)
  ·
    refine ⟨92163464094365607399162833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245769237584974953064434221 92163464094365607399162833)
    ·
      refine ⟨69122598070774205549372125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92163464094365607399162833 69122598070774205549372125)
      ·
        refine ⟨25920974276540327081014547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69122598070774205549372125 25920974276540327081014547)
        ·
          refine ⟨38881461414810490621521821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25920974276540327081014547 38881461414810490621521821)
          ·
            refine ⟨14580548030553933983070683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38881461414810490621521821 14580548030553933983070683)
            ·
              refine ⟨21870822045830900974606025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14580548030553933983070683 21870822045830900974606025)
              ·
                refine ⟨16403116534373175730954519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21870822045830900974606025 16403116534373175730954519)
                ·
                  refine ⟨24604674801559763596431779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16403116534373175730954519 24604674801559763596431779)
                  ·
                    refine ⟨36907012202339645394647669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24604674801559763596431779 36907012202339645394647669)
                    ·
                      refine ⟨3460032393969341755748219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36907012202339645394647669 3460032393969341755748219)
                      ·
                        rfl

theorem cell23_6738389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6738389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738389 prefixEnd_6738389 := by exact prefixLift 6738389
  have htrace : WordTrace (prefixWord ++ tailWord_6738389) baseStart_6738389 baseEnd_6738389 := by
    simpa [prefixWord, tailWord_6738389, baseEnd_6738389] using wordTrace_append hprefix tailTrace_6738389
  have hstable : (prefixWord ++ tailWord_6738389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738389).length < 2 ^ (prefixWord ++ tailWord_6738389).sum := by decide
  have hdescent : baseEnd_6738389 < baseStart_6738389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738399 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_6738399 : Nat := 118140960795 + 6738399 * 2 ^ 59
def prefixEnd_6738399 : Nat := 4983230072969 + 3 ^ 40 * 6738399 * 2
def baseEnd_6738399 : Nat := 3460037528775886716623173

theorem tailTrace_6738399 : CollatzResearch.WordTrace tailWord_6738399 prefixEnd_6738399 3460037528775886716623173 := by
  unfold tailWord_6738399
  simp only [CollatzResearch.WordTrace]
  refine ⟨245769602314938724772298251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163846401543292483181532167 245769602314938724772298251)
  ·
    refine ⟨368654403472408087158447377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245769602314938724772298251 368654403472408087158447377)
    ·
      refine ⟨276490802604306065368835533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368654403472408087158447377 276490802604306065368835533)
      ·
        refine ⟨103684050976614774513313325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276490802604306065368835533 103684050976614774513313325)
        ·
          refine ⟨38881519116230540442492497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103684050976614774513313325 38881519116230540442492497)
          ·
            refine ⟨29161139337172905331869373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38881519116230540442492497 29161139337172905331869373)
            ·
              refine ⟨10935427251439839499451015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29161139337172905331869373 10935427251439839499451015)
              ·
                refine ⟨16403140877159759249176523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935427251439839499451015 16403140877159759249176523)
                ·
                  refine ⟨24604711315739638873764785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16403140877159759249176523 24604711315739638873764785)
                  ·
                    refine ⟨18453533486804729155323589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24604711315739638873764785 18453533486804729155323589)
                    ·
                      refine ⟨3460037528775886716623173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18453533486804729155323589 3460037528775886716623173)
                      ·
                        rfl

theorem cell23_6738399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_6738399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738399 prefixEnd_6738399 := by exact prefixLift 6738399
  have htrace : WordTrace (prefixWord ++ tailWord_6738399) baseStart_6738399 baseEnd_6738399 := by
    simpa [prefixWord, tailWord_6738399, baseEnd_6738399] using wordTrace_append hprefix tailTrace_6738399
  have hstable : (prefixWord ++ tailWord_6738399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738399).length < 2 ^ (prefixWord ++ tailWord_6738399).sum := by decide
  have hdescent : baseEnd_6738399 < baseStart_6738399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738419 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 3]
def baseStart_6738419 : Nat := 118140960795 + 6738419 * 2 ^ 59
def prefixEnd_6738419 : Nat := 4983230072969 + 3 ^ 40 * 6738419 * 2
def baseEnd_6738419 : Nat := 3460047798388976638373081

theorem tailTrace_6738419 : CollatzResearch.WordTrace tailWord_6738419 prefixEnd_6738419 3460047798388976638373081 := by
  unfold tailWord_6738419
  simp only [CollatzResearch.WordTrace]
  refine ⟨245770331774866268188026311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163846887849910845458684207 245770331774866268188026311)
  ·
    refine ⟨368655497662299402282039467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245770331774866268188026311 368655497662299402282039467)
    ·
      refine ⟨552983246493449103423059201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368655497662299402282039467 552983246493449103423059201)
      ·
        refine ⟨414737434870086827567294401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 552983246493449103423059201 414737434870086827567294401)
        ·
          refine ⟨311053076152565120675470801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414737434870086827567294401 311053076152565120675470801)
          ·
            refine ⟨233289807114423840506603101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311053076152565120675470801 233289807114423840506603101)
            ·
              refine ⟨87483677667908940189976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233289807114423840506603101 87483677667908940189976163)
              ·
                refine ⟨131225516501863410284964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87483677667908940189976163 131225516501863410284964245)
                ·
                  refine ⟨6151196086024847357107699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131225516501863410284964245 6151196086024847357107699)
                  ·
                    refine ⟨9226794129037271035661549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151196086024847357107699 9226794129037271035661549)
                    ·
                      refine ⟨3460047798388976638373081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9226794129037271035661549 3460047798388976638373081)
                      ·
                        rfl

theorem cell23_6738419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_6738419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738419 prefixEnd_6738419 := by exact prefixLift 6738419
  have htrace : WordTrace (prefixWord ++ tailWord_6738419) baseStart_6738419 baseEnd_6738419 := by
    simpa [prefixWord, tailWord_6738419, baseEnd_6738419] using wordTrace_append hprefix tailTrace_6738419
  have hstable : (prefixWord ++ tailWord_6738419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738419).length < 2 ^ (prefixWord ++ tailWord_6738419).sum := by decide
  have hdescent : baseEnd_6738419 < baseStart_6738419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738459 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 4, 2]
def baseStart_6738459 : Nat := 118140960795 + 6738459 * 2 ^ 59
def prefixEnd_6738459 : Nat := 4983230072969 + 3 ^ 40 * 6738459 * 2
def baseEnd_6738459 : Nat := 3460068337615156481872897

theorem tailTrace_6738459 : CollatzResearch.WordTrace tailWord_6738459 prefixEnd_6738459 3460068337615156481872897 := by
  unfold tailWord_6738459
  simp only [CollatzResearch.WordTrace]
  refine ⟨245771790694721355019482431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163847860463147570012988287 245771790694721355019482431)
  ·
    refine ⟨368657686042082032529223647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245771790694721355019482431 368657686042082032529223647)
    ·
      refine ⟨552986529063123048793835471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368657686042082032529223647 552986529063123048793835471)
      ·
        refine ⟨829479793594684573190753207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552986529063123048793835471 829479793594684573190753207)
        ·
          refine ⟨1244219690392026859786129811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829479793594684573190753207 1244219690392026859786129811)
          ·
            refine ⟨1866329535588040289679194717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244219690392026859786129811 1866329535588040289679194717)
            ·
              refine ⟨699873575845515108629698019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1866329535588040289679194717 699873575845515108629698019)
              ·
                refine ⟨1049810363768272662944547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699873575845515108629698019 1049810363768272662944547029)
                ·
                  refine ⟨24604930400818890537762821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1049810363768272662944547029 24604930400818890537762821)
                  ·
                    refine ⟨4613424450153541975830529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24604930400818890537762821 4613424450153541975830529)
                    ·
                      refine ⟨3460068337615156481872897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613424450153541975830529 3460068337615156481872897)
                      ·
                        rfl

theorem cell23_6738459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4, 2].length) (baseStart_6738459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738459 prefixEnd_6738459 := by exact prefixLift 6738459
  have htrace : WordTrace (prefixWord ++ tailWord_6738459) baseStart_6738459 baseEnd_6738459 := by
    simpa [prefixWord, tailWord_6738459, baseEnd_6738459] using wordTrace_append hprefix tailTrace_6738459
  have hstable : (prefixWord ++ tailWord_6738459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738459).length < 2 ^ (prefixWord ++ tailWord_6738459).sum := by decide
  have hdescent : baseEnd_6738459 < baseStart_6738459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738476 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_6738476 : Nat := 118140960795 + 6738476 * 2 ^ 59
def prefixEnd_6738476 : Nat := 4983230072969 + 3 ^ 40 * 6738476 * 2
def baseEnd_6738476 : Nat := 3460077066786282915360319

theorem tailTrace_6738476 : CollatzResearch.WordTrace tailWord_6738476 prefixEnd_6738476 3460077066786282915360319 := by
  unfold tailWord_6738476
  simp only [CollatzResearch.WordTrace]
  refine ⟨122886205367829883461425641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163848273823773177948567521 122886205367829883461425641)
  ·
    refine ⟨92164654025872412596069231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122886205367829883461425641 92164654025872412596069231)
    ·
      refine ⟨138246981038808618894103847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92164654025872412596069231 138246981038808618894103847)
      ·
        refine ⟨207370471558212928341155771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138246981038808618894103847 207370471558212928341155771)
        ·
          refine ⟨311055707337319392511733657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207370471558212928341155771 311055707337319392511733657)
          ·
            refine ⟨233291780502989544383800243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311055707337319392511733657 233291780502989544383800243)
            ·
              refine ⟨349937670754484316575700365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233291780502989544383800243 349937670754484316575700365)
              ·
                refine ⟨131226626532931618715887637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349937670754484316575700365 131226626532931618715887637)
                ·
                  refine ⟨6151248118731169627307233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131226626532931618715887637 6151248118731169627307233)
                  ·
                    refine ⟨4613436089048377220480425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6151248118731169627307233 4613436089048377220480425)
                    ·
                      refine ⟨3460077066786282915360319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613436089048377220480425 3460077066786282915360319)
                      ·
                        rfl

theorem cell23_6738476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_6738476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738476 prefixEnd_6738476 := by exact prefixLift 6738476
  have htrace : WordTrace (prefixWord ++ tailWord_6738476) baseStart_6738476 baseEnd_6738476 := by
    simpa [prefixWord, tailWord_6738476, baseEnd_6738476] using wordTrace_append hprefix tailTrace_6738476
  have hstable : (prefixWord ++ tailWord_6738476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738476).length < 2 ^ (prefixWord ++ tailWord_6738476).sum := by decide
  have hdescent : baseEnd_6738476 < baseStart_6738476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738489 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6738489 : Nat := 118140960795 + 6738489 * 2 ^ 59
def prefixEnd_6738489 : Nat := 4983230072969 + 3 ^ 40 * 6738489 * 2
def baseEnd_6738489 : Nat := 3460083742034791364497759

theorem tailTrace_6738489 : CollatzResearch.WordTrace tailWord_6738489 prefixEnd_6738489 3460083742034791364497759 := by
  unfold tailWord_6738489
  simp only [CollatzResearch.WordTrace]
  refine ⟨245772884884612670143074521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163848589923075113428716347 245772884884612670143074521)
  ·
    refine ⟨184329663663459502607305891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245772884884612670143074521 184329663663459502607305891)
    ·
      refine ⟨276494495495189253910958837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184329663663459502607305891 276494495495189253910958837)
      ·
        refine ⟨25921358952673992554152391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276494495495189253910958837 25921358952673992554152391)
        ·
          refine ⟨38882038429010988831228587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25921358952673992554152391 38882038429010988831228587)
          ·
            refine ⟨58323057643516483246842881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38882038429010988831228587 58323057643516483246842881)
            ·
              refine ⟨43742293232637362435132161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58323057643516483246842881 43742293232637362435132161)
              ·
                refine ⟨32806719924478021826349121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43742293232637362435132161 32806719924478021826349121)
                ·
                  refine ⟨24605039943358516369761841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32806719924478021826349121 24605039943358516369761841)
                  ·
                    refine ⟨18453779957518887277321381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24605039943358516369761841 18453779957518887277321381)
                    ·
                      refine ⟨3460083742034791364497759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18453779957518887277321381 3460083742034791364497759)
                      ·
                        rfl

theorem cell23_6738489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6738489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738489 prefixEnd_6738489 := by exact prefixLift 6738489
  have htrace : WordTrace (prefixWord ++ tailWord_6738489) baseStart_6738489 baseEnd_6738489 := by
    simpa [prefixWord, tailWord_6738489, baseEnd_6738489] using wordTrace_append hprefix tailTrace_6738489
  have hstable : (prefixWord ++ tailWord_6738489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738489).length < 2 ^ (prefixWord ++ tailWord_6738489).sum := by decide
  have hdescent : baseEnd_6738489 < baseStart_6738489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738529 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_6738529 : Nat := 118140960795 + 6738529 * 2 ^ 59
def prefixEnd_6738529 : Nat := 4983230072969 + 3 ^ 40 * 6738529 * 2
def baseEnd_6738529 : Nat := 1153368093753657069332525

theorem tailTrace_6738529 : CollatzResearch.WordTrace tailWord_6738529 prefixEnd_6738529 1153368093753657069332525 := by
  unfold tailWord_6738529
  simp only [CollatzResearch.WordTrace]
  refine ⟨245774343804467756974530641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163849562536311837983020427 245774343804467756974530641)
  ·
    refine ⟨184330757853350817730897981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245774343804467756974530641 184330757853350817730897981)
    ·
      refine ⟨69124034195006556649086743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184330757853350817730897981 69124034195006556649086743)
      ·
        refine ⟨103686051292509834973630115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69124034195006556649086743 103686051292509834973630115)
        ·
          refine ⟨155529076938764752460445173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103686051292509834973630115 155529076938764752460445173)
          ·
            refine ⟨14580850963009195543166735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155529076938764752460445173 14580850963009195543166735)
            ·
              refine ⟨21871276444513793314750103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14580850963009195543166735 21871276444513793314750103)
              ·
                refine ⟨32806914666770689972125155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21871276444513793314750103 32806914666770689972125155)
                ·
                  refine ⟨49210372000156034958187733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32806914666770689972125155 49210372000156034958187733)
                  ·
                    refine ⟨1153368093753657069332525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49210372000156034958187733 1153368093753657069332525)
                    ·
                      rfl

theorem cell23_6738529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_6738529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738529 prefixEnd_6738529 := by exact prefixLift 6738529
  have htrace : WordTrace (prefixWord ++ tailWord_6738529) baseStart_6738529 baseEnd_6738529 := by
    simpa [prefixWord, tailWord_6738529, baseEnd_6738529] using wordTrace_append hprefix tailTrace_6738529
  have hstable : (prefixWord ++ tailWord_6738529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738529).length < 2 ^ (prefixWord ++ tailWord_6738529).sum := by decide
  have hdescent : baseEnd_6738529 < baseStart_6738529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738533 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 5]
def baseStart_6738533 : Nat := 118140960795 + 6738533 * 2 ^ 59
def prefixEnd_6738533 : Nat := 4983230072969 + 3 ^ 40 * 6738533 * 2
def baseEnd_6738533 : Nat := 384456259464843243594173

theorem tailTrace_6738533 : CollatzResearch.WordTrace tailWord_6738533 prefixEnd_6738533 384456259464843243594173 := by
  unfold tailWord_6738533
  simp only [CollatzResearch.WordTrace]
  refine ⟨245774489696453265657676253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163849659797635510438450835 245774489696453265657676253)
  ·
    refine ⟨92165433636169974621628595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245774489696453265657676253 92165433636169974621628595)
    ·
      refine ⟨138248150454254961932442893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92165433636169974621628595 138248150454254961932442893)
      ·
        refine ⟨51843056420345610724666085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138248150454254961932442893 51843056420345610724666085)
        ·
          refine ⟨9720573078814802010874891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51843056420345610724666085 9720573078814802010874891)
          ·
            refine ⟨14580859618222203016312337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720573078814802010874891 14580859618222203016312337)
            ·
              refine ⟨10935644713666652262234253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14580859618222203016312337 10935644713666652262234253)
              ·
                refine ⟨4100866767624994598337845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10935644713666652262234253 4100866767624994598337845)
                ·
                  refine ⟨384456259464843243594173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4100866767624994598337845 384456259464843243594173)
                  ·
                    rfl

theorem cell23_6738533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_6738533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738533 prefixEnd_6738533 := by exact prefixLift 6738533
  have htrace : WordTrace (prefixWord ++ tailWord_6738533) baseStart_6738533 baseEnd_6738533 := by
    simpa [prefixWord, tailWord_6738533, baseEnd_6738533] using wordTrace_append hprefix tailTrace_6738533
  have hstable : (prefixWord ++ tailWord_6738533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738533).length < 2 ^ (prefixWord ++ tailWord_6738533).sum := by decide
  have hdescent : baseEnd_6738533 < baseStart_6738533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738589 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 8]
def baseStart_6738589 : Nat := 118140960795 + 6738589 * 2 ^ 59
def prefixEnd_6738589 : Nat := 4983230072969 + 3 ^ 40 * 6738589 * 2
def baseEnd_6738589 : Nat := 384459454455582330360811

theorem tailTrace_6738589 : CollatzResearch.WordTrace tailWord_6738589 prefixEnd_6738589 384459454455582330360811 := by
  unfold tailWord_6738589
  simp only [CollatzResearch.WordTrace]
  refine ⟨245776532184250387221714821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163851021456166924814476547 245776532184250387221714821)
  ·
    refine ⟨46083099784546947604071529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245776532184250387221714821 46083099784546947604071529)
    ·
      refine ⟨34562324838410210703053647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46083099784546947604071529 34562324838410210703053647)
      ·
        refine ⟨51843487257615316054580471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34562324838410210703053647 51843487257615316054580471)
        ·
          refine ⟨77765230886422974081870707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51843487257615316054580471 77765230886422974081870707)
          ·
            refine ⟨116647846329634461122806061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77765230886422974081870707 116647846329634461122806061)
            ·
              refine ⟨43742942373612922921052273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116647846329634461122806061 43742942373612922921052273)
              ·
                refine ⟨32807206780209692190789205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43742942373612922921052273 32807206780209692190789205)
                ·
                  refine ⟨384459454455582330360811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32807206780209692190789205 384459454455582330360811)
                  ·
                    rfl

theorem cell23_6738589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_6738589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738589 prefixEnd_6738589 := by exact prefixLift 6738589
  have htrace : WordTrace (prefixWord ++ tailWord_6738589) baseStart_6738589 baseEnd_6738589 := by
    simpa [prefixWord, tailWord_6738589, baseEnd_6738589] using wordTrace_append hprefix tailTrace_6738589
  have hstable : (prefixWord ++ tailWord_6738589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738589).length < 2 ^ (prefixWord ++ tailWord_6738589).sum := by decide
  have hdescent : baseEnd_6738589 < baseStart_6738589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738623 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 6]
def baseStart_6738623 : Nat := 118140960795 + 6738623 * 2 ^ 59
def prefixEnd_6738623 : Nat := 4983230072969 + 3 ^ 40 * 6738623 * 2
def baseEnd_6738623 : Nat := 384461394271388204469127

theorem tailTrace_6738623 : CollatzResearch.WordTrace tailWord_6738623 prefixEnd_6738623 384461394271388204469127 := by
  unfold tailWord_6738623
  simp only [CollatzResearch.WordTrace]
  refine ⟨245777772266127211028452523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163851848177418140685635015 245777772266127211028452523)
  ·
    refine ⟨368666658399190816542678785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245777772266127211028452523 368666658399190816542678785)
    ·
      refine ⟨276499993799393112407009089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368666658399190816542678785 276499993799393112407009089)
      ·
        refine ⟨207374995349544834305256817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276499993799393112407009089 207374995349544834305256817)
        ·
          refine ⟨155531246512158625728942613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207374995349544834305256817 155531246512158625728942613)
          ·
            refine ⟨7290527180257435581044185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155531246512158625728942613 7290527180257435581044185)
            ·
              refine ⟨5467895385193076685783139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290527180257435581044185 5467895385193076685783139)
              ·
                refine ⟨8201843077789615028674709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467895385193076685783139 8201843077789615028674709)
                ·
                  refine ⟨384461394271388204469127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8201843077789615028674709 384461394271388204469127)
                  ·
                    rfl

theorem cell23_6738623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 6].length) (baseStart_6738623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738623 prefixEnd_6738623 := by exact prefixLift 6738623
  have htrace : WordTrace (prefixWord ++ tailWord_6738623) baseStart_6738623 baseEnd_6738623 := by
    simpa [prefixWord, tailWord_6738623, baseEnd_6738623] using wordTrace_append hprefix tailTrace_6738623
  have hstable : (prefixWord ++ tailWord_6738623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738623).length < 2 ^ (prefixWord ++ tailWord_6738623).sum := by decide
  have hdescent : baseEnd_6738623 < baseStart_6738623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738637 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6738637 : Nat := 118140960795 + 6738637 * 2 ^ 59
def prefixEnd_6738637 : Nat := 4983230072969 + 3 ^ 40 * 6738637 * 2
def baseEnd_6738637 : Nat := 3460159737171656785447079

theorem tailTrace_6738637 : CollatzResearch.WordTrace tailWord_6738637 prefixEnd_6738637 3460159737171656785447079 := by
  unfold tailWord_6738637
  simp only [CollatzResearch.WordTrace]
  refine ⟨245778282888076491419462165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163852188592050994279641443 245778282888076491419462165)
  ·
    refine ⟨11520857010378585535287289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 245778282888076491419462165 11520857010378585535287289)
    ·
      refine ⟨8640642757783939151465467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520857010378585535287289 8640642757783939151465467)
      ·
        refine ⟨12960964136675908727198201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640642757783939151465467 12960964136675908727198201)
        ·
          refine ⟨9720723102506931545398651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12960964136675908727198201 9720723102506931545398651)
          ·
            refine ⟨14581084653760397318097977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720723102506931545398651 14581084653760397318097977)
            ·
              refine ⟨10935813490320297988573483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14581084653760397318097977 10935813490320297988573483)
              ·
                refine ⟨16403720235480446982860225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935813490320297988573483 16403720235480446982860225)
                ·
                  refine ⟨12302790176610335237145169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16403720235480446982860225 12302790176610335237145169)
                  ·
                    refine ⟨9227092632457751427858877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12302790176610335237145169 9227092632457751427858877)
                    ·
                      refine ⟨3460159737171656785447079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227092632457751427858877 3460159737171656785447079)
                      ·
                        rfl

theorem cell23_6738637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6738637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738637 prefixEnd_6738637 := by exact prefixLift 6738637
  have htrace : WordTrace (prefixWord ++ tailWord_6738637) baseStart_6738637 baseEnd_6738637 := by
    simpa [prefixWord, tailWord_6738637, baseEnd_6738637] using wordTrace_append hprefix tailTrace_6738637
  have hstable : (prefixWord ++ tailWord_6738637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738637).length < 2 ^ (prefixWord ++ tailWord_6738637).sum := by decide
  have hdescent : baseEnd_6738637 < baseStart_6738637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738650 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_6738650 : Nat := 118140960795 + 6738650 * 2 ^ 59
def prefixEnd_6738650 : Nat := 4983230072969 + 3 ^ 40 * 6738650 * 2
def baseEnd_6738650 : Nat := 3460166412420165234584519

theorem tailTrace_6738650 : CollatzResearch.WordTrace tailWord_6738650 prefixEnd_6738650 3460166412420165234584519 := by
  unfold tailWord_6738650
  simp only [CollatzResearch.WordTrace]
  refine ⟨61444689259257348659921351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163852504691352929759790269 61444689259257348659921351)
  ·
    refine ⟨92167033888886022989882027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61444689259257348659921351 92167033888886022989882027)
    ·
      refine ⟨138250550833329034484823041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92167033888886022989882027 138250550833329034484823041)
      ·
        refine ⟨103687913124996775863617281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138250550833329034484823041 103687913124996775863617281)
        ·
          refine ⟨77765934843747581897712961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103687913124996775863617281 77765934843747581897712961)
          ·
            refine ⟨58324451132810686423284721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77765934843747581897712961 58324451132810686423284721)
            ·
              refine ⟨43743338349608014817463541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58324451132810686423284721 43743338349608014817463541)
              ·
                refine ⟨4100937970275751389137207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43743338349608014817463541 4100937970275751389137207)
                ·
                  refine ⟨6151406955413627083705811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100937970275751389137207 6151406955413627083705811)
                  ·
                    refine ⟨9227110433120440625558717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151406955413627083705811 9227110433120440625558717)
                    ·
                      refine ⟨3460166412420165234584519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227110433120440625558717 3460166412420165234584519)
                      ·
                        rfl

theorem cell23_6738650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_6738650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738650 prefixEnd_6738650 := by exact prefixLift 6738650
  have htrace : WordTrace (prefixWord ++ tailWord_6738650) baseStart_6738650 baseEnd_6738650 := by
    simpa [prefixWord, tailWord_6738650, baseEnd_6738650] using wordTrace_append hprefix tailTrace_6738650
  have hstable : (prefixWord ++ tailWord_6738650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738650).length < 2 ^ (prefixWord ++ tailWord_6738650).sum := by decide
  have hdescent : baseEnd_6738650 < baseStart_6738650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738707 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 1, 2, 2]
def baseStart_6738707 : Nat := 118140960795 + 6738707 * 2 ^ 59
def prefixEnd_6738707 : Nat := 4983230072969 + 3 ^ 40 * 6738707 * 2
def baseEnd_6738707 : Nat := 3460195680817471511571757

theorem tailTrace_6738707 : CollatzResearch.WordTrace tailWord_6738707 prefixEnd_6738707 3460195680817471511571757 := by
  unfold tailWord_6738707
  simp only [CollatzResearch.WordTrace]
  refine ⟨245780835997822893374510375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163853890665215262249673583 245780835997822893374510375)
  ·
    refine ⟨368671253996734340061765563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245780835997822893374510375 368671253996734340061765563)
    ·
      refine ⟨553006880995101510092648345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368671253996734340061765563 553006880995101510092648345)
      ·
        refine ⟨414755160746326132569486259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553006880995101510092648345 414755160746326132569486259)
        ·
          refine ⟨622132741119489198854229389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414755160746326132569486259 622132741119489198854229389)
          ·
            refine ⟨233299777919808449570336021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622132741119489198854229389 233299777919808449570336021)
            ·
              refine ⟨10935927089991021073609501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233299777919808449570336021 10935927089991021073609501)
              ·
                refine ⟨4100972658746632902603563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10935927089991021073609501 4100972658746632902603563)
                ·
                  refine ⟨6151458988119949353905345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100972658746632902603563 6151458988119949353905345)
                  ·
                    refine ⟨4613594241089962015429009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6151458988119949353905345 4613594241089962015429009)
                    ·
                      refine ⟨3460195680817471511571757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613594241089962015429009 3460195680817471511571757)
                      ·
                        rfl

theorem cell23_6738707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 2, 2].length) (baseStart_6738707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738707 prefixEnd_6738707 := by exact prefixLift 6738707
  have htrace : WordTrace (prefixWord ++ tailWord_6738707) baseStart_6738707 baseEnd_6738707 := by
    simpa [prefixWord, tailWord_6738707, baseEnd_6738707] using wordTrace_append hprefix tailTrace_6738707
  have hstable : (prefixWord ++ tailWord_6738707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738707).length < 2 ^ (prefixWord ++ tailWord_6738707).sum := by decide
  have hdescent : baseEnd_6738707 < baseStart_6738707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738776 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6738776 : Nat := 118140960795 + 6738776 * 2 ^ 59
def prefixEnd_6738776 : Nat := 4983230072969 + 3 ^ 40 * 6738776 * 2
def baseEnd_6738776 : Nat := 3460231110982631741608939

theorem tailTrace_6738776 : CollatzResearch.WordTrace tailWord_6738776 prefixEnd_6738776 3460231110982631741608939 := by
  unfold tailWord_6738776
  simp only [CollatzResearch.WordTrace]
  refine ⟨122891676317286459079386091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163855568423048612105848121 122891676317286459079386091)
  ·
    refine ⟨184337514475929688619079137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122891676317286459079386091 184337514475929688619079137)
    ·
      refine ⟨138253135856947266464309353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184337514475929688619079137 138253135856947266464309353)
      ·
        refine ⟨103689851892710449848232015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138253135856947266464309353 103689851892710449848232015)
        ·
          refine ⟨155534777839065674772348023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103689851892710449848232015 155534777839065674772348023)
          ·
            refine ⟨233302166758598512158522035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155534777839065674772348023 233302166758598512158522035)
            ·
              refine ⟨349953250137897768237783053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233302166758598512158522035 349953250137897768237783053)
              ·
                refine ⟨131232468801711663089168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349953250137897768237783053 131232468801711663089168645)
                ·
                  refine ⟨24606087900320936829219121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131232468801711663089168645 24606087900320936829219121)
                  ·
                    refine ⟨18454565925240702621914341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24606087900320936829219121 18454565925240702621914341)
                    ·
                      refine ⟨3460231110982631741608939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18454565925240702621914341 3460231110982631741608939)
                      ·
                        rfl

theorem cell23_6738776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6738776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738776 prefixEnd_6738776 := by exact prefixLift 6738776
  have htrace : WordTrace (prefixWord ++ tailWord_6738776) baseStart_6738776 baseEnd_6738776 := by
    simpa [prefixWord, tailWord_6738776, baseEnd_6738776] using wordTrace_append hprefix tailTrace_6738776
  have hstable : (prefixWord ++ tailWord_6738776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738776).length < 2 ^ (prefixWord ++ tailWord_6738776).sum := by decide
  have hdescent : baseEnd_6738776 < baseStart_6738776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738814 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6738814 : Nat := 118140960795 + 6738814 * 2 ^ 59
def prefixEnd_6738814 : Nat := 4983230072969 + 3 ^ 40 * 6738814 * 2
def baseEnd_6738814 : Nat := 3460250623247502592933765

theorem tailTrace_6738814 : CollatzResearch.WordTrace tailWord_6738814 prefixEnd_6738814 3460250623247502592933765 := by
  unfold tailWord_6738814
  simp only [CollatzResearch.WordTrace]
  refine ⟨30723092326054406331081937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163856492405623500432436997 30723092326054406331081937)
  ·
    refine ⟨23042319244540804748311453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30723092326054406331081937 23042319244540804748311453)
    ·
      refine ⟨8640869716702801780616795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23042319244540804748311453 8640869716702801780616795)
      ·
        refine ⟨12961304575054202670925193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640869716702801780616795 12961304575054202670925193)
        ·
          refine ⟨9720978431290652003193895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12961304575054202670925193 9720978431290652003193895)
          ·
            refine ⟨14581467646935978004790843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720978431290652003193895 14581467646935978004790843)
            ·
              refine ⟨21872201470403967007186265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14581467646935978004790843 21872201470403967007186265)
              ·
                refine ⟨16404151102802975255389699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21872201470403967007186265 16404151102802975255389699)
                ·
                  refine ⟨24606226654204462883084549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16404151102802975255389699 24606226654204462883084549)
                  ·
                    refine ⟨4613667497663336790578353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24606226654204462883084549 4613667497663336790578353)
                    ·
                      refine ⟨3460250623247502592933765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613667497663336790578353 3460250623247502592933765)
                      ·
                        rfl

theorem cell23_6738814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6738814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738814 prefixEnd_6738814 := by exact prefixLift 6738814
  have htrace : WordTrace (prefixWord ++ tailWord_6738814) baseStart_6738814 baseEnd_6738814 := by
    simpa [prefixWord, tailWord_6738814, baseEnd_6738814] using wordTrace_append hprefix tailTrace_6738814
  have hstable : (prefixWord ++ tailWord_6738814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738814).length < 2 ^ (prefixWord ++ tailWord_6738814).sum := by decide
  have hdescent : baseEnd_6738814 < baseStart_6738814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738818 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6738818 : Nat := 118140960795 + 6738818 * 2 ^ 59
def prefixEnd_6738818 : Nat := 4983230072969 + 3 ^ 40 * 6738818 * 2
def baseEnd_6738818 : Nat := 3460252677170120577283747

theorem tailTrace_6738818 : CollatzResearch.WordTrace tailWord_6738818 prefixEnd_6738818 3460252677170120577283747 := by
  unfold tailWord_6738818
  simp only [CollatzResearch.WordTrace]
  refine ⟨61446221125105189832950277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163856589666947172887867405 61446221125105189832950277)
  ·
    refine ⟨11521166460957223093678177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61446221125105189832950277 11521166460957223093678177)
    ·
      refine ⟨8640874845717917320258633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11521166460957223093678177 8640874845717917320258633)
      ·
        refine ⟨6480656134288437990193975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8640874845717917320258633 6480656134288437990193975)
        ·
          refine ⟨9720984201432656985290963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480656134288437990193975 9720984201432656985290963)
          ·
            refine ⟨14581476302148985477936445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720984201432656985290963 14581476302148985477936445)
            ·
              refine ⟨5468053613305869554226167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14581476302148985477936445 5468053613305869554226167)
              ·
                refine ⟨8202080419958804331339251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468053613305869554226167 8202080419958804331339251)
                ·
                  refine ⟨12303120629938206497008877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202080419958804331339251 12303120629938206497008877)
                  ·
                    refine ⟨4613670236226827436378329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12303120629938206497008877 4613670236226827436378329)
                    ·
                      refine ⟨3460252677170120577283747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613670236226827436378329 3460252677170120577283747)
                      ·
                        rfl

theorem cell23_6738818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6738818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738818 prefixEnd_6738818 := by exact prefixLift 6738818
  have htrace : WordTrace (prefixWord ++ tailWord_6738818) baseStart_6738818 baseEnd_6738818 := by
    simpa [prefixWord, tailWord_6738818, baseEnd_6738818] using wordTrace_append hprefix tailTrace_6738818
  have hstable : (prefixWord ++ tailWord_6738818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738818).length < 2 ^ (prefixWord ++ tailWord_6738818).sum := by decide
  have hdescent : baseEnd_6738818 < baseStart_6738818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738837 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 5]
def baseStart_6738837 : Nat := 118140960795 + 6738837 * 2 ^ 59
def prefixEnd_6738837 : Nat := 4983230072969 + 3 ^ 40 * 6738837 * 2
def baseEnd_6738837 : Nat := 384473603700284000327351

theorem tailTrace_6738837 : CollatzResearch.WordTrace tailWord_6738837 prefixEnd_6738837 384473603700284000327351 := by
  unfold tailWord_6738837
  simp only [CollatzResearch.WordTrace]
  refine ⟨245785577487351925576742765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163857051658234617051161843 245785577487351925576742765)
  ·
    refine ⟨92169591557756972091278537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245785577487351925576742765 92169591557756972091278537)
    ·
      refine ⟨69127193668317729068458903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92169591557756972091278537 69127193668317729068458903)
      ·
        refine ⟨103690790502476593602688355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69127193668317729068458903 103690790502476593602688355)
        ·
          refine ⟨155536185753714890404032533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103690790502476593602688355 155536185753714890404032533)
          ·
            refine ⟨7290758707205385487689025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155536185753714890404032533 7290758707205385487689025)
            ·
              refine ⟨5468069030404039115766769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290758707205385487689025 5468069030404039115766769)
              ·
                refine ⟨4101051772803029336825077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468069030404039115766769 4101051772803029336825077)
                ·
                  refine ⟨384473603700284000327351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101051772803029336825077 384473603700284000327351)
                  ·
                    rfl

theorem cell23_6738837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_6738837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738837 prefixEnd_6738837 := by exact prefixLift 6738837
  have htrace : WordTrace (prefixWord ++ tailWord_6738837) baseStart_6738837 baseEnd_6738837 := by
    simpa [prefixWord, tailWord_6738837, baseEnd_6738837] using wordTrace_append hprefix tailTrace_6738837
  have hstable : (prefixWord ++ tailWord_6738837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738837).length < 2 ^ (prefixWord ++ tailWord_6738837).sum := by decide
  have hdescent : baseEnd_6738837 < baseStart_6738837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738940 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_6738940 : Nat := 118140960795 + 6738940 * 2 ^ 59
def prefixEnd_6738940 : Nat := 4983230072969 + 3 ^ 40 * 6738940 * 2
def baseEnd_6738940 : Nat := 1153438440603323033319395

theorem tailTrace_6738940 : CollatzResearch.WordTrace tailWord_6738940 prefixEnd_6738940 1153438440603323033319395 := by
  unfold tailWord_6738940
  simp only [CollatzResearch.WordTrace]
  refine ⟨122894667102989387083871137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163859556137319182778494849 122894667102989387083871137)
  ·
    refine ⟨92171000327242040312903353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122894667102989387083871137 92171000327242040312903353)
    ·
      refine ⟨69128250245431530234677515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92171000327242040312903353 69128250245431530234677515)
      ·
        refine ⟨103692375368147295352016273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69128250245431530234677515 103692375368147295352016273)
        ·
          refine ⟨77769281526110471514012205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103692375368147295352016273 77769281526110471514012205)
          ·
            refine ⟨29163480572291426817754577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77769281526110471514012205 29163480572291426817754577)
            ·
              refine ⟨21872610429218570113315933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29163480572291426817754577 21872610429218570113315933)
              ·
                refine ⟨8202228910956963792493475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21872610429218570113315933 8202228910956963792493475)
                ·
                  refine ⟨12303343366435445688740213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202228910956963792493475 12303343366435445688740213)
                  ·
                    refine ⟨1153438440603323033319395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12303343366435445688740213 1153438440603323033319395)
                    ·
                      rfl

theorem cell23_6738940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_6738940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738940 prefixEnd_6738940 := by exact prefixLift 6738940
  have htrace : WordTrace (prefixWord ++ tailWord_6738940) baseStart_6738940 baseEnd_6738940 := by
    simpa [prefixWord, tailWord_6738940, baseEnd_6738940] using wordTrace_append hprefix tailTrace_6738940
  have hstable : (prefixWord ++ tailWord_6738940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738940).length < 2 ^ (prefixWord ++ tailWord_6738940).sum := by decide
  have hdescent : baseEnd_6738940 < baseStart_6738940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738943 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_6738943 : Nat := 118140960795 + 6738943 * 2 ^ 59
def prefixEnd_6738943 : Nat := 4983230072969 + 3 ^ 40 * 6738943 * 2
def baseEnd_6738943 : Nat := 3460316862251932588220671

theorem tailTrace_6738943 : CollatzResearch.WordTrace tailWord_6738943 prefixEnd_6738943 3460316862251932588220671 := by
  unfold tailWord_6738943
  simp only [CollatzResearch.WordTrace]
  refine ⟨245789443624967905680101483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163859629083311937120067655 245789443624967905680101483)
  ·
    refine ⟨368684165437451858520152225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245789443624967905680101483 368684165437451858520152225)
    ·
      refine ⟨276513124078088893890114169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368684165437451858520152225 276513124078088893890114169)
      ·
        refine ⟨207384843058566670417585627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276513124078088893890114169 207384843058566670417585627)
        ·
          refine ⟨311077264587850005626378441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207384843058566670417585627 311077264587850005626378441)
          ·
            refine ⟨233307948440887504219783831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311077264587850005626378441 233307948440887504219783831)
            ·
              refine ⟨349961922661331256329675747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233307948440887504219783831 349961922661331256329675747)
              ·
                refine ⟨524942883991996884494513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349961922661331256329675747 524942883991996884494513621)
                ·
                  refine ⟨12303348843562426980340163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 524942883991996884494513621 12303348843562426980340163)
                  ·
                    refine ⟨18455023265343640470510245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12303348843562426980340163 18455023265343640470510245)
                    ·
                      refine ⟨3460316862251932588220671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18455023265343640470510245 3460316862251932588220671)
                      ·
                        rfl

theorem cell23_6738943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_6738943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738943 prefixEnd_6738943 := by exact prefixLift 6738943
  have htrace : WordTrace (prefixWord ++ tailWord_6738943) baseStart_6738943 baseEnd_6738943 := by
    simpa [prefixWord, tailWord_6738943, baseEnd_6738943] using wordTrace_append hprefix tailTrace_6738943
  have hstable : (prefixWord ++ tailWord_6738943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738943).length < 2 ^ (prefixWord ++ tailWord_6738943).sum := by decide
  have hdescent : baseEnd_6738943 < baseStart_6738943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738954 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_6738954 : Nat := 118140960795 + 6738954 * 2 ^ 59
def prefixEnd_6738954 : Nat := 4983230072969 + 3 ^ 40 * 6738954 * 2
def baseEnd_6738954 : Nat := 3460322510539132045183121

theorem tailTrace_6738954 : CollatzResearch.WordTrace tailWord_6738954 prefixEnd_6738954 3460322510539132045183121 := by
  unfold tailWord_6738954
  simp only [CollatzResearch.WordTrace]
  refine ⟨61447461206982013639687979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163859896551952036372501277 61447461206982013639687979)
  ·
    refine ⟨92171191810473020459531969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61447461206982013639687979 92171191810473020459531969)
    ·
      refine ⟨69128393857854765344648977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92171191810473020459531969 69128393857854765344648977)
      ·
        refine ⟨51846295393391074008486733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69128393857854765344648977 51846295393391074008486733)
        ·
          refine ⟨19442360772521652753182525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51846295393391074008486733 19442360772521652753182525)
          ·
            refine ⟨7290885289695619782443447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19442360772521652753182525 7290885289695619782443447)
            ·
              refine ⟨10936327934543429673665171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290885289695619782443447 10936327934543429673665171)
              ·
                refine ⟨16404491901815144510497757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936327934543429673665171 16404491901815144510497757)
                ·
                  refine ⟨6151684463180679191436659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16404491901815144510497757 6151684463180679191436659)
                  ·
                    refine ⟨9227526694771018787154989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151684463180679191436659 9227526694771018787154989)
                    ·
                      refine ⟨3460322510539132045183121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227526694771018787154989 3460322510539132045183121)
                      ·
                        rfl

theorem cell23_6738954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_6738954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738954 prefixEnd_6738954 := by exact prefixLift 6738954
  have htrace : WordTrace (prefixWord ++ tailWord_6738954) baseStart_6738954 baseEnd_6738954 := by
    simpa [prefixWord, tailWord_6738954, baseEnd_6738954] using wordTrace_append hprefix tailTrace_6738954
  have hstable : (prefixWord ++ tailWord_6738954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738954).length < 2 ^ (prefixWord ++ tailWord_6738954).sum := by decide
  have hdescent : baseEnd_6738954 < baseStart_6738954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738963 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3]
def baseStart_6738963 : Nat := 118140960795 + 6738963 * 2 ^ 59
def prefixEnd_6738963 : Nat := 4983230072969 + 3 ^ 40 * 6738963 * 2
def baseEnd_6738963 : Nat := 3460327131865022509970579

theorem tailTrace_6738963 : CollatzResearch.WordTrace tailWord_6738963 prefixEnd_6738963 3460327131865022509970579 := by
  unfold tailWord_6738963
  simp only [CollatzResearch.WordTrace]
  refine ⟨245790173084895449095829543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163860115389930299397219695 245790173084895449095829543)
  ·
    refine ⟨368685259627343173643744315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245790173084895449095829543 368685259627343173643744315)
    ·
      refine ⟨553027889441014760465616473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368685259627343173643744315 553027889441014760465616473)
      ·
        refine ⟨414770917080761070349212355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553027889441014760465616473 414770917080761070349212355)
        ·
          refine ⟨622156375621141605523818533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414770917080761070349212355 622156375621141605523818533)
          ·
            refine ⟨116654320428964051035715975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 622156375621141605523818533 116654320428964051035715975)
            ·
              refine ⟨174981480643446076553573963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116654320428964051035715975 174981480643446076553573963)
              ·
                refine ⟨262472220965169114830360945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174981480643446076553573963 262472220965169114830360945)
                ·
                  refine ⟨196854165723876836122770709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262472220965169114830360945 196854165723876836122770709)
                  ·
                    refine ⟨9227539018306726693254877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 196854165723876836122770709 9227539018306726693254877)
                    ·
                      refine ⟨3460327131865022509970579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227539018306726693254877 3460327131865022509970579)
                      ·
                        rfl

theorem cell23_6738963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_6738963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738963 prefixEnd_6738963 := by exact prefixLift 6738963
  have htrace : WordTrace (prefixWord ++ tailWord_6738963) baseStart_6738963 baseEnd_6738963 := by
    simpa [prefixWord, tailWord_6738963, baseEnd_6738963] using wordTrace_append hprefix tailTrace_6738963
  have hstable : (prefixWord ++ tailWord_6738963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738963).length < 2 ^ (prefixWord ++ tailWord_6738963).sum := by decide
  have hdescent : baseEnd_6738963 < baseStart_6738963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6738977 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6738977 : Nat := 118140960795 + 6738977 * 2 ^ 59
def prefixEnd_6738977 : Nat := 4983230072969 + 3 ^ 40 * 6738977 * 2
def baseEnd_6738977 : Nat := 3460334320594185455195515

theorem tailTrace_6738977 : CollatzResearch.WordTrace tailWord_6738977 prefixEnd_6738977 3460334320594185455195515 := by
  unfold tailWord_6738977
  simp only [CollatzResearch.WordTrace]
  refine ⟨245790683706844729486839185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163860455804563152991226123 245790683706844729486839185)
  ·
    refine ⟨184343012780133547115129389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245790683706844729486839185 184343012780133547115129389)
    ·
      refine ⟨69128629792550080168173521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184343012780133547115129389 69128629792550080168173521)
      ·
        refine ⟨51846472344412560126130141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69128629792550080168173521 51846472344412560126130141)
        ·
          refine ⟨19442427129154710047298803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51846472344412560126130141 19442427129154710047298803)
          ·
            refine ⟨29163640693732065070948205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19442427129154710047298803 29163640693732065070948205)
            ·
              refine ⟨10936365260149524401605577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29163640693732065070948205 10936365260149524401605577)
              ·
                refine ⟨8202273945112143301204183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936365260149524401605577 8202273945112143301204183)
                ·
                  refine ⟨12303410917668214951806275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202273945112143301204183 12303410917668214951806275)
                  ·
                    refine ⟨18455116376502322427709413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12303410917668214951806275 18455116376502322427709413)
                    ·
                      refine ⟨3460334320594185455195515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18455116376502322427709413 3460334320594185455195515)
                      ·
                        rfl

theorem cell23_6738977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6738977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6738977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6738977 prefixEnd_6738977 := by exact prefixLift 6738977
  have htrace : WordTrace (prefixWord ++ tailWord_6738977) baseStart_6738977 baseEnd_6738977 := by
    simpa [prefixWord, tailWord_6738977, baseEnd_6738977] using wordTrace_append hprefix tailTrace_6738977
  have hstable : (prefixWord ++ tailWord_6738977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6738977).length < 2 ^ (prefixWord ++ tailWord_6738977).sum := by decide
  have hdescent : baseEnd_6738977 < baseStart_6738977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6738977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739013 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_6739013 : Nat := 118140960795 + 6739013 * 2 ^ 59
def prefixEnd_6739013 : Nat := 4983230072969 + 3 ^ 40 * 6739013 * 2
def baseEnd_6739013 : Nat := 1153450935299249104781783

theorem tailTrace_6739013 : CollatzResearch.WordTrace tailWord_6739013 prefixEnd_6739013 1153450935299249104781783 := by
  unfold tailWord_6739013
  simp only [CollatzResearch.WordTrace]
  refine ⟨245791996734714307635149693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163861331156476205090099795 245791996734714307635149693)
  ·
    refine ⟨92171998775517865363181135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245791996734714307635149693 92171998775517865363181135)
    ·
      refine ⟨138257998163276798044771703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92171998775517865363181135 138257998163276798044771703)
      ·
        refine ⟨207386997244915197067157555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138257998163276798044771703 207386997244915197067157555)
        ·
          refine ⟨311080495867372795600736333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207386997244915197067157555 311080495867372795600736333)
          ·
            refine ⟨116655185950264798350276125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311080495867372795600736333 116655185950264798350276125)
            ·
              refine ⟨43745694731349299381353547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116655185950264798350276125 43745694731349299381353547)
              ·
                refine ⟨65618542097023949072030321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43745694731349299381353547 65618542097023949072030321)
                ·
                  refine ⟨49213906572767961804022741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65618542097023949072030321 49213906572767961804022741)
                  ·
                    refine ⟨1153450935299249104781783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49213906572767961804022741 1153450935299249104781783)
                    ·
                      rfl

theorem cell23_6739013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_6739013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739013 prefixEnd_6739013 := by exact prefixLift 6739013
  have htrace : WordTrace (prefixWord ++ tailWord_6739013) baseStart_6739013 baseEnd_6739013 := by
    simpa [prefixWord, tailWord_6739013, baseEnd_6739013] using wordTrace_append hprefix tailTrace_6739013
  have hstable : (prefixWord ++ tailWord_6739013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739013).length < 2 ^ (prefixWord ++ tailWord_6739013).sum := by decide
  have hdescent : baseEnd_6739013 < baseStart_6739013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739014 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6739014 : Nat := 118140960795 + 6739014 * 2 ^ 59
def prefixEnd_6739014 : Nat := 4983230072969 + 3 ^ 40 * 6739014 * 2
def baseEnd_6739014 : Nat := 3460353319378401810432845

theorem tailTrace_6739014 : CollatzResearch.WordTrace tailWord_6739014 prefixEnd_6739014 3460353319378401810432845 := by
  unfold tailWord_6739014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681001037740958900185503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163861355471807123203957397 7681001037740958900185503)
  ·
    refine ⟨11521501556611438350278255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681001037740958900185503 11521501556611438350278255)
    ·
      refine ⟨17282252334917157525417383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521501556611438350278255 17282252334917157525417383)
      ·
        refine ⟨25923378502375736288126075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17282252334917157525417383 25923378502375736288126075)
        ·
          refine ⟨38885067753563604432189113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25923378502375736288126075 38885067753563604432189113)
          ·
            refine ⟨29163800815172703324141835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38885067753563604432189113 29163800815172703324141835)
            ·
              refine ⟨43745701222759054986212753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29163800815172703324141835 43745701222759054986212753)
              ·
                refine ⟨32809275917069291239659565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43745701222759054986212753 32809275917069291239659565)
                ·
                  refine ⟨12303478468900984214872337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32809275917069291239659565 12303478468900984214872337)
                  ·
                    refine ⟨9227608851675738161154253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12303478468900984214872337 9227608851675738161154253)
                    ·
                      refine ⟨3460353319378401810432845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227608851675738161154253 3460353319378401810432845)
                      ·
                        rfl

theorem cell23_6739014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6739014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739014 prefixEnd_6739014 := by exact prefixLift 6739014
  have htrace : WordTrace (prefixWord ++ tailWord_6739014) baseStart_6739014 baseEnd_6739014 := by
    simpa [prefixWord, tailWord_6739014, baseEnd_6739014] using wordTrace_append hprefix tailTrace_6739014
  have hstable : (prefixWord ++ tailWord_6739014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739014).length < 2 ^ (prefixWord ++ tailWord_6739014).sum := by decide
  have hdescent : baseEnd_6739014 < baseStart_6739014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739043 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 8]
def baseStart_6739043 : Nat := 118140960795 + 6739043 * 2 ^ 59
def prefixEnd_6739043 : Nat := 4983230072969 + 3 ^ 40 * 6739043 * 2
def baseEnd_6739043 : Nat := 1153456070105794065656737

theorem tailTrace_6739043 : CollatzResearch.WordTrace tailWord_6739043 prefixEnd_6739043 1153456070105794065656737 := by
  unfold tailWord_6739043
  simp only [CollatzResearch.WordTrace]
  refine ⟨245793090924605622758741783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163862060616403748505827855 245793090924605622758741783)
  ·
    refine ⟨368689636386908434138112675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245793090924605622758741783 368689636386908434138112675)
    ·
      refine ⟨553034454580362651207169013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368689636386908434138112675 553034454580362651207169013)
      ·
        refine ⟨51846980116908998550672095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 553034454580362651207169013 51846980116908998550672095)
        ·
          refine ⟨77770470175363497826008143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51846980116908998550672095 77770470175363497826008143)
          ·
            refine ⟨116655705263045246739012215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77770470175363497826008143 116655705263045246739012215)
            ·
              refine ⟨174983557894567870108518323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116655705263045246739012215 174983557894567870108518323)
              ·
                refine ⟨262475336841851805162777485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174983557894567870108518323 262475336841851805162777485)
                ·
                  refine ⟨98428251315694426936041557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262475336841851805162777485 98428251315694426936041557)
                  ·
                    refine ⟨1153456070105794065656737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98428251315694426936041557 1153456070105794065656737)
                    ·
                      rfl

theorem cell23_6739043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_6739043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739043 prefixEnd_6739043 := by exact prefixLift 6739043
  have htrace : WordTrace (prefixWord ++ tailWord_6739043) baseStart_6739043 baseEnd_6739043 := by
    simpa [prefixWord, tailWord_6739043, baseEnd_6739043] using wordTrace_append hprefix tailTrace_6739043
  have hstable : (prefixWord ++ tailWord_6739043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739043).length < 2 ^ (prefixWord ++ tailWord_6739043).sum := by decide
  have hdescent : baseEnd_6739043 < baseStart_6739043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739048 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6739048 : Nat := 118140960795 + 6739048 * 2 ^ 59
def prefixEnd_6739048 : Nat := 4983230072969 + 3 ^ 40 * 6739048 * 2
def baseEnd_6739048 : Nat := 3460370777720654677407689

theorem tailTrace_6739048 : CollatzResearch.WordTrace tailWord_6739048 prefixEnd_6739048 3460370777720654677407689 := by
  unfold tailWord_6739048
  simp only [CollatzResearch.WordTrace]
  refine ⟨122896636644793754306336899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163862182193058339075115865 122896636644793754306336899)
  ·
    refine ⟨184344954967190631459505349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122896636644793754306336899 184344954967190631459505349)
    ·
      refine ⟨34564679056348243398657253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184344954967190631459505349 34564679056348243398657253)
      ·
        refine ⟨6480877323065295637248235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34564679056348243398657253 6480877323065295637248235)
        ·
          refine ⟨9721315984597943455872353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480877323065295637248235 9721315984597943455872353)
          ·
            refine ⟨7290986988448457591904265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9721315984597943455872353 7290986988448457591904265)
            ·
              refine ⟨5468240241336343193928199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290986988448457591904265 5468240241336343193928199)
              ·
                refine ⟨8202360362004514790892299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468240241336343193928199 8202360362004514790892299)
                ·
                  refine ⟨12303540543006772186338449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202360362004514790892299 12303540543006772186338449)
                  ·
                    refine ⟨9227655407255079139753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12303540543006772186338449 9227655407255079139753837)
                    ·
                      refine ⟨3460370777720654677407689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227655407255079139753837 3460370777720654677407689)
                      ·
                        rfl

theorem cell23_6739048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6739048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739048 prefixEnd_6739048 := by exact prefixLift 6739048
  have htrace : WordTrace (prefixWord ++ tailWord_6739048) baseStart_6739048 baseEnd_6739048 := by
    simpa [prefixWord, tailWord_6739048, baseEnd_6739048] using wordTrace_append hprefix tailTrace_6739048
  have hstable : (prefixWord ++ tailWord_6739048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739048).length < 2 ^ (prefixWord ++ tailWord_6739048).sum := by decide
  have hdescent : baseEnd_6739048 < baseStart_6739048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739061 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6739061 : Nat := 118140960795 + 6739061 * 2 ^ 59
def prefixEnd_6739061 : Nat := 4983230072969 + 3 ^ 40 * 6739061 * 2
def baseEnd_6739061 : Nat := 3460377452969163126545129

theorem tailTrace_6739061 : CollatzResearch.WordTrace tailWord_6739061 prefixEnd_6739061 3460377452969163126545129 := by
  unfold tailWord_6739061
  simp only [CollatzResearch.WordTrace]
  refine ⟨245793747438540411832897037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163862498292360274555264691 245793747438540411832897037)
  ·
    refine ⟨92172655289452654437336389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245793747438540411832897037 92172655289452654437336389)
    ·
      refine ⟨17282372866772372707000573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92172655289452654437336389 17282372866772372707000573)
      ·
        refine ⟨6480889825039639765125215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17282372866772372707000573 6480889825039639765125215)
        ·
          refine ⟨9721334737559459647687823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480889825039639765125215 9721334737559459647687823)
          ·
            refine ⟨14582002106339189471531735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721334737559459647687823 14582002106339189471531735)
            ·
              refine ⟨21873003159508784207297603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582002106339189471531735 21873003159508784207297603)
              ·
                refine ⟨32809504739263176310946405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21873003159508784207297603 32809504739263176310946405)
                ·
                  refine ⟨6151782138611845558302451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32809504739263176310946405 6151782138611845558302451)
                  ·
                    refine ⟨9227673207917768337453677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151782138611845558302451 9227673207917768337453677)
                    ·
                      refine ⟨3460377452969163126545129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9227673207917768337453677 3460377452969163126545129)
                      ·
                        rfl

theorem cell23_6739061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6739061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739061 prefixEnd_6739061 := by exact prefixLift 6739061
  have htrace : WordTrace (prefixWord ++ tailWord_6739061) baseStart_6739061 baseEnd_6739061 := by
    simpa [prefixWord, tailWord_6739061, baseEnd_6739061] using wordTrace_append hprefix tailTrace_6739061
  have hstable : (prefixWord ++ tailWord_6739061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739061).length < 2 ^ (prefixWord ++ tailWord_6739061).sum := by decide
  have hdescent : baseEnd_6739061 < baseStart_6739061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739083 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_6739083 : Nat := 118140960795 + 6739083 * 2 ^ 59
def prefixEnd_6739083 : Nat := 4983230072969 + 3 ^ 40 * 6739083 * 2
def baseEnd_6739083 : Nat := 3460388749543562040470027

theorem tailTrace_6739083 : CollatzResearch.WordTrace tailWord_6739083 prefixEnd_6739083 3460388749543562040470027 := by
  unfold tailWord_6739083
  simp only [CollatzResearch.WordTrace]
  refine ⟨245794549844460709590197903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163863033229640473060131935 245794549844460709590197903)
  ·
    refine ⟨368691824766691064385296855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245794549844460709590197903 368691824766691064385296855)
    ·
      refine ⟨553037737150036596577945283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368691824766691064385296855 553037737150036596577945283)
      ·
        refine ⟨829556605725054894866917925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553037737150036596577945283 829556605725054894866917925)
        ·
          refine ⟨155541863573447792787547111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 829556605725054894866917925 155541863573447792787547111)
          ·
            refine ⟨233312795360171689181320667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155541863573447792787547111 233312795360171689181320667)
            ·
              refine ⟨349969193040257533771981001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233312795360171689181320667 349969193040257533771981001)
              ·
                refine ⟨262476894780193150328985751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349969193040257533771981001 262476894780193150328985751)
                ·
                  refine ⟨393715342170289725493478627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262476894780193150328985751 393715342170289725493478627)
                  ·
                    refine ⟨590573013255434588240217941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 393715342170289725493478627 590573013255434588240217941)
                    ·
                      refine ⟨3460388749543562040470027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 590573013255434588240217941 3460388749543562040470027)
                      ·
                        rfl

theorem cell23_6739083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_6739083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739083 prefixEnd_6739083 := by exact prefixLift 6739083
  have htrace : WordTrace (prefixWord ++ tailWord_6739083) baseStart_6739083 baseEnd_6739083 := by
    simpa [prefixWord, tailWord_6739083, baseEnd_6739083] using wordTrace_append hprefix tailTrace_6739083
  have hstable : (prefixWord ++ tailWord_6739083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739083).length < 2 ^ (prefixWord ++ tailWord_6739083).sum := by decide
  have hdescent : baseEnd_6739083 < baseStart_6739083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739084 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_6739084 : Nat := 118140960795 + 6739084 * 2 ^ 59
def prefixEnd_6739084 : Nat := 4983230072969 + 3 ^ 40 * 6739084 * 2
def baseEnd_6739084 : Nat := 3460389263024216536557523

theorem tailTrace_6739084 : CollatzResearch.WordTrace tailWord_6739084 prefixEnd_6739084 3460389263024216536557523 := by
  unfold tailWord_6739084
  simp only [CollatzResearch.WordTrace]
  refine ⟨122897293158728543380492153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163863057544971391173989537 122897293158728543380492153)
  ·
    refine ⟨92172969869046407535369115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122897293158728543380492153 92172969869046407535369115)
    ·
      refine ⟨138259454803569611303053673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92172969869046407535369115 138259454803569611303053673)
      ·
        refine ⟨103694591102677208477290255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138259454803569611303053673 103694591102677208477290255)
        ·
          refine ⟨155541886654015812715935383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103694591102677208477290255 155541886654015812715935383)
          ·
            refine ⟨233312829981023719073903075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155541886654015812715935383 233312829981023719073903075)
            ·
              refine ⟨349969244971535578610854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233312829981023719073903075 349969244971535578610854613)
              ·
                refine ⟨8202404179020365123691905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 349969244971535578610854613 8202404179020365123691905)
                ·
                  refine ⟨6151803134265273842768929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202404179020365123691905 6151803134265273842768929)
                  ·
                    refine ⟨4613852350698955382076697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6151803134265273842768929 4613852350698955382076697)
                    ·
                      refine ⟨3460389263024216536557523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613852350698955382076697 3460389263024216536557523)
                      ·
                        rfl

theorem cell23_6739084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_6739084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739084 prefixEnd_6739084 := by exact prefixLift 6739084
  have htrace : WordTrace (prefixWord ++ tailWord_6739084) baseStart_6739084 baseEnd_6739084 := by
    simpa [prefixWord, tailWord_6739084, baseEnd_6739084] using wordTrace_append hprefix tailTrace_6739084
  have hstable : (prefixWord ++ tailWord_6739084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739084).length < 2 ^ (prefixWord ++ tailWord_6739084).sum := by decide
  have hdescent : baseEnd_6739084 < baseStart_6739084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739120 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_6739120 : Nat := 118140960795 + 6739120 * 2 ^ 59
def prefixEnd_6739120 : Nat := 4983230072969 + 3 ^ 40 * 6739120 * 2
def baseEnd_6739120 : Nat := 1153469249442592798569119

theorem tailTrace_6739120 : CollatzResearch.WordTrace tailWord_6739120 prefixEnd_6739120 1153469249442592798569119 := by
  unfold tailWord_6739120
  simp only [CollatzResearch.WordTrace]
  refine ⟨122897949672663332454647407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163863932896884443272863209 122897949672663332454647407)
  ·
    refine ⟨184346924508994998681971111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122897949672663332454647407 184346924508994998681971111)
    ·
      refine ⟨276520386763492498022956667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184346924508994998681971111 276520386763492498022956667)
      ·
        refine ⟨414780580145238747034435001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276520386763492498022956667 414780580145238747034435001)
        ·
          refine ⟨311085435108929060275826251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414780580145238747034435001 311085435108929060275826251)
          ·
            refine ⟨466628152663393590413739377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311085435108929060275826251 466628152663393590413739377)
            ·
              refine ⟨349971114497545192810304533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466628152663393590413739377 349971114497545192810304533)
              ·
                refine ⟨16404895992072430912983025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349971114497545192810304533 16404895992072430912983025)
                ·
                  refine ⟨12303671994054323184737269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16404895992072430912983025 12303671994054323184737269)
                  ·
                    refine ⟨1153469249442592798569119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12303671994054323184737269 1153469249442592798569119)
                    ·
                      rfl

theorem cell23_6739120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_6739120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739120 prefixEnd_6739120 := by exact prefixLift 6739120
  have htrace : WordTrace (prefixWord ++ tailWord_6739120) baseStart_6739120 baseEnd_6739120 := by
    simpa [prefixWord, tailWord_6739120, baseEnd_6739120] using wordTrace_append hprefix tailTrace_6739120
  have hstable : (prefixWord ++ tailWord_6739120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739120).length < 2 ^ (prefixWord ++ tailWord_6739120).sum := by decide
  have hdescent : baseEnd_6739120 < baseStart_6739120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739127 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 5, 2]
def baseStart_6739127 : Nat := 118140960795 + 6739127 * 2 ^ 59
def prefixEnd_6739127 : Nat := 4983230072969 + 3 ^ 40 * 6739127 * 2
def baseEnd_6739127 : Nat := 3460411342692359868319825

theorem tailTrace_6739127 : CollatzResearch.WordTrace tailWord_6739127 prefixEnd_6739127 3460411342692359868319825 := by
  unfold tailWord_6739127
  simp only [CollatzResearch.WordTrace]
  refine ⟨245796154656301305104799635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163864103104200870069866423 245796154656301305104799635)
  ·
    refine ⟨368694231984451957657199453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245796154656301305104799635 368694231984451957657199453)
    ·
      refine ⟨138260336994169484121449795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368694231984451957657199453 138260336994169484121449795)
      ·
        refine ⟨207390505491254226182174693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138260336994169484121449795 207390505491254226182174693)
        ·
          refine ⟨38885719779610167409157755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207390505491254226182174693 38885719779610167409157755)
          ·
            refine ⟨58328579669415251113736633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38885719779610167409157755 58328579669415251113736633)
            ·
              refine ⟨43746434752061438335302475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58328579669415251113736633 43746434752061438335302475)
              ·
                refine ⟨65619652128092157502953713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43746434752061438335302475 65619652128092157502953713)
                ·
                  refine ⟨49214739096069118127215285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65619652128092157502953713 49214739096069118127215285)
                  ·
                    refine ⟨4613881790256479824426433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49214739096069118127215285 4613881790256479824426433)
                    ·
                      refine ⟨3460411342692359868319825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4613881790256479824426433 3460411342692359868319825)
                      ·
                        rfl

theorem cell23_6739127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_6739127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739127 prefixEnd_6739127 := by exact prefixLift 6739127
  have htrace : WordTrace (prefixWord ++ tailWord_6739127) baseStart_6739127 baseEnd_6739127 := by
    simpa [prefixWord, tailWord_6739127, baseEnd_6739127] using wordTrace_append hprefix tailTrace_6739127
  have hstable : (prefixWord ++ tailWord_6739127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739127).length < 2 ^ (prefixWord ++ tailWord_6739127).sum := by decide
  have hdescent : baseEnd_6739127 < baseStart_6739127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739231 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 6]
def baseStart_6739231 : Nat := 118140960795 + 6739231 * 2 ^ 59
def prefixEnd_6739231 : Nat := 4983230072969 + 3 ^ 40 * 6739231 * 2
def baseEnd_6739231 : Nat := 384496082742269717935483

theorem tailTrace_6739231 : CollatzResearch.WordTrace tailWord_6739231 prefixEnd_6739231 384496082742269717935483 := by
  unfold tailWord_6739231
  simp only [CollatzResearch.WordTrace]
  refine ⟨245799947847924530866585547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163866631898616353911057031 245799947847924530866585547)
  ·
    refine ⟨368699921771886796299878321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245799947847924530866585547 368699921771886796299878321)
    ·
      refine ⟨276524941328915097224908741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368699921771886796299878321 276524941328915097224908741)
      ·
        refine ⟨51848426499171580729670389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276524941328915097224908741 51848426499171580729670389)
        ·
          refine ⟨4860789984297335693406599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51848426499171580729670389 4860789984297335693406599)
          ·
            refine ⟨7291184976446003540109899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860789984297335693406599 7291184976446003540109899)
            ·
              refine ⟨10936777464669005310164849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291184976446003540109899 10936777464669005310164849)
              ·
                refine ⟨8202583098501753982623637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936777464669005310164849 8202583098501753982623637)
                ·
                  refine ⟨384496082742269717935483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8202583098501753982623637 384496082742269717935483)
                  ·
                    rfl

theorem cell23_6739231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 6].length) (baseStart_6739231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739231 prefixEnd_6739231 := by exact prefixLift 6739231
  have htrace : WordTrace (prefixWord ++ tailWord_6739231) baseStart_6739231 baseEnd_6739231 := by
    simpa [prefixWord, tailWord_6739231, baseEnd_6739231] using wordTrace_append hprefix tailTrace_6739231
  have hstable : (prefixWord ++ tailWord_6739231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739231).length < 2 ^ (prefixWord ++ tailWord_6739231).sum := by decide
  have hdescent : baseEnd_6739231 < baseStart_6739231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739264 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_6739264 : Nat := 118140960795 + 6739264 * 2 ^ 59
def prefixEnd_6739264 : Nat := 4983230072969 + 3 ^ 40 * 6739264 * 2
def baseEnd_6739264 : Nat := 3460481689542025832306695

theorem tailTrace_6739264 : CollatzResearch.WordTrace tailWord_6739264 prefixEnd_6739264 3460481689542025832306695 := by
  unfold tailWord_6739264
  simp only [CollatzResearch.WordTrace]
  refine ⟨122900575728402488751268423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163867434304536651668357897 122900575728402488751268423)
  ·
    refine ⟨184350863592603733126902635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122900575728402488751268423 184350863592603733126902635)
    ·
      refine ⟨276526295388905599690353953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184350863592603733126902635 276526295388905599690353953)
      ·
        refine ⟨207394721541679199767765465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276526295388905599690353953 207394721541679199767765465)
        ·
          refine ⟨155546041156259399825824099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207394721541679199767765465 155546041156259399825824099)
          ·
            refine ⟨233319061734389099738736149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155546041156259399825824099 233319061734389099738736149)
            ·
              refine ⟨10936831018799489050253257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233319061734389099738736149 10936831018799489050253257)
              ·
                refine ⟨8202623264099616787689943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936831018799489050253257 8202623264099616787689943)
                ·
                  refine ⟨12303934896149425181534915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202623264099616787689943 12303934896149425181534915)
                  ·
                    refine ⟨18455902344224137772302373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12303934896149425181534915 18455902344224137772302373)
                    ·
                      refine ⟨3460481689542025832306695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18455902344224137772302373 3460481689542025832306695)
                      ·
                        rfl

theorem cell23_6739264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_6739264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739264 prefixEnd_6739264 := by exact prefixLift 6739264
  have htrace : WordTrace (prefixWord ++ tailWord_6739264) baseStart_6739264 baseEnd_6739264 := by
    simpa [prefixWord, tailWord_6739264, baseEnd_6739264] using wordTrace_append hprefix tailTrace_6739264
  have hstable : (prefixWord ++ tailWord_6739264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739264).length < 2 ^ (prefixWord ++ tailWord_6739264).sum := by decide
  have hdescent : baseEnd_6739264 < baseStart_6739264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739284 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_6739284 : Nat := 118140960795 + 6739284 * 2 ^ 59
def prefixEnd_6739284 : Nat := 4983230072969 + 3 ^ 40 * 6739284 * 2
def baseEnd_6739284 : Nat := 3460491959155115754056603

theorem tailTrace_6739284 : CollatzResearch.WordTrace tailWord_6739284 prefixEnd_6739284 3460491959155115754056603 := by
  unfold tailWord_6739284
  simp only [CollatzResearch.WordTrace]
  refine ⟨122900940458366260459132453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163867920611155013945509937 122900940458366260459132453)
  ·
    refine ⟨23043926335943673836087335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122900940458366260459132453 23043926335943673836087335)
    ·
      refine ⟨34565889503915510754131003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23043926335943673836087335 34565889503915510754131003)
      ·
        refine ⟨51848834255873266131196505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34565889503915510754131003 51848834255873266131196505)
        ·
          refine ⟨38886625691904949598397379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51848834255873266131196505 38886625691904949598397379)
          ·
            refine ⟨58329938537857424397596069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38886625691904949598397379 58329938537857424397596069)
            ·
              refine ⟨10936863475848267074549263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58329938537857424397596069 10936863475848267074549263)
              ·
                refine ⟨16405295213772400611823895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936863475848267074549263 16405295213772400611823895)
                ·
                  refine ⟨24607942820658600917735843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16405295213772400611823895 24607942820658600917735843)
                  ·
                    refine ⟨36911914230987901376603765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24607942820658600917735843 36911914230987901376603765)
                    ·
                      refine ⟨3460491959155115754056603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36911914230987901376603765 3460491959155115754056603)
                      ·
                        rfl

theorem cell23_6739284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_6739284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739284 prefixEnd_6739284 := by exact prefixLift 6739284
  have htrace : WordTrace (prefixWord ++ tailWord_6739284) baseStart_6739284 baseEnd_6739284 := by
    simpa [prefixWord, tailWord_6739284, baseEnd_6739284] using wordTrace_append hprefix tailTrace_6739284
  have hstable : (prefixWord ++ tailWord_6739284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739284).length < 2 ^ (prefixWord ++ tailWord_6739284).sum := by decide
  have hdescent : baseEnd_6739284 < baseStart_6739284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739287 : List Nat := [1, 1, 3, 2, 3, 4, 9]
def baseStart_6739287 : Nat := 118140960795 + 6739287 * 2 ^ 59
def prefixEnd_6739287 : Nat := 4983230072969 + 3 ^ 40 * 6739287 * 2
def baseEnd_6739287 : Nat := 42722141970334311633569

theorem tailTrace_6739287 : CollatzResearch.WordTrace tailWord_6739287 prefixEnd_6739287 42722141970334311633569 := by
  unfold tailWord_6739287
  simp only [CollatzResearch.WordTrace]
  refine ⟨245801990335721652430624115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163867993557147768287082743 245801990335721652430624115)
  ·
    refine ⟨368702985503582478645936173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245801990335721652430624115 368702985503582478645936173)
    ·
      refine ⟨138263619563843429492226065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368702985503582478645936173 138263619563843429492226065)
      ·
        refine ⟨103697714672882572119169549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138263619563843429492226065 103697714672882572119169549)
        ·
          refine ⟨38886643002330964544688581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103697714672882572119169549 38886643002330964544688581)
          ·
            refine ⟨7291245562937055852129109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38886643002330964544688581 7291245562937055852129109)
            ·
              refine ⟨42722141970334311633569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7291245562937055852129109 42722141970334311633569)
              ·
                rfl

theorem cell23_6739287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 9].length) (baseStart_6739287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739287 prefixEnd_6739287 := by exact prefixLift 6739287
  have htrace : WordTrace (prefixWord ++ tailWord_6739287) baseStart_6739287 baseEnd_6739287 := by
    simpa [prefixWord, tailWord_6739287, baseEnd_6739287] using wordTrace_append hprefix tailTrace_6739287
  have hstable : (prefixWord ++ tailWord_6739287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739287).length < 2 ^ (prefixWord ++ tailWord_6739287).sum := by decide
  have hdescent : baseEnd_6739287 < baseStart_6739287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739304 : List Nat := [2, 1, 4, 2, 3, 1, 2, 8]
def baseStart_6739304 : Nat := 118140960795 + 6739304 * 2 ^ 59
def prefixEnd_6739304 : Nat := 4983230072969 + 3 ^ 40 * 6739304 * 2
def baseEnd_6739304 : Nat := 128166749213637247252093

theorem tailTrace_6739304 : CollatzResearch.WordTrace tailWord_6739304 prefixEnd_6739304 128166749213637247252093 := by
  unfold tailWord_6739304
  simp only [CollatzResearch.WordTrace]
  refine ⟨122901305188330032166996483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163868406917773376222661977 122901305188330032166996483)
  ·
    refine ⟨184351957782495048250494725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122901305188330032166996483 184351957782495048250494725)
    ·
      refine ⟨34565992084217821546967761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184351957782495048250494725 34565992084217821546967761)
      ·
        refine ⟨25924494063163366160225821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34565992084217821546967761 25924494063163366160225821)
        ·
          refine ⟨9721685273686262310084683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25924494063163366160225821 9721685273686262310084683)
          ·
            refine ⟨14582527910529393465127025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721685273686262310084683 14582527910529393465127025)
            ·
              refine ⟨10936895932897045098845269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14582527910529393465127025 10936895932897045098845269)
              ·
                refine ⟨128166749213637247252093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10936895932897045098845269 128166749213637247252093)
                ·
                  rfl

theorem cell23_6739304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 8].length) (baseStart_6739304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739304 prefixEnd_6739304 := by exact prefixLift 6739304
  have htrace : WordTrace (prefixWord ++ tailWord_6739304) baseStart_6739304 baseEnd_6739304 := by
    simpa [prefixWord, tailWord_6739304, baseEnd_6739304] using wordTrace_append hprefix tailTrace_6739304
  have hstable : (prefixWord ++ tailWord_6739304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739304).length < 2 ^ (prefixWord ++ tailWord_6739304).sum := by decide
  have hdescent : baseEnd_6739304 < baseStart_6739304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739308 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_6739308 : Nat := 118140960795 + 6739308 * 2 ^ 59
def prefixEnd_6739308 : Nat := 4983230072969 + 3 ^ 40 * 6739308 * 2
def baseEnd_6739308 : Nat := 1153501427563607886718831

theorem tailTrace_6739308 : CollatzResearch.WordTrace tailWord_6739308 prefixEnd_6739308 1153501427563607886718831 := by
  unfold tailWord_6739308
  simp only [CollatzResearch.WordTrace]
  refine ⟨122901378134322786508569289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163868504179097048678092385 122901378134322786508569289)
  ·
    refine ⟨92176033600742089881426967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122901378134322786508569289 92176033600742089881426967)
    ·
      refine ⟨138264050401113134822140451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92176033600742089881426967 138264050401113134822140451)
      ·
        refine ⟨207396075601669702233210677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138264050401113134822140451 207396075601669702233210677)
        ·
          refine ⟨19443382087656534584363501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207396075601669702233210677 19443382087656534584363501)
          ·
            refine ⟨7291268282871200469136313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19443382087656534584363501 7291268282871200469136313)
            ·
              refine ⟨5468451212153400351852235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291268282871200469136313 5468451212153400351852235)
              ·
                refine ⟨8202676818230100527778353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468451212153400351852235 8202676818230100527778353)
                ·
                  refine ⟨6152007613672575395833765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202676818230100527778353 6152007613672575395833765)
                  ·
                    refine ⟨1153501427563607886718831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152007613672575395833765 1153501427563607886718831)
                    ·
                      rfl

theorem cell23_6739308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_6739308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739308 prefixEnd_6739308 := by exact prefixLift 6739308
  have htrace : WordTrace (prefixWord ++ tailWord_6739308) baseStart_6739308 baseEnd_6739308 := by
    simpa [prefixWord, tailWord_6739308, baseEnd_6739308] using wordTrace_append hprefix tailTrace_6739308
  have hstable : (prefixWord ++ tailWord_6739308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739308).length < 2 ^ (prefixWord ++ tailWord_6739308).sum := by decide
  have hdescent : baseEnd_6739308 < baseStart_6739308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739314 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_6739314 : Nat := 118140960795 + 6739314 * 2 ^ 59
def prefixEnd_6739314 : Nat := 4983230072969 + 3 ^ 40 * 6739314 * 2
def baseEnd_6739314 : Nat := 3460507363574750636681465

theorem tailTrace_6739314 : CollatzResearch.WordTrace tailWord_6739314 prefixEnd_6739314 3460507363574750636681465 := by
  unfold tailWord_6739314
  simp only [CollatzResearch.WordTrace]
  refine ⟨61450743776655959010464249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163868650071082557361237997 61450743776655959010464249)
  ·
    refine ⟨46088057832491969257848187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61450743776655959010464249 46088057832491969257848187)
    ·
      refine ⟨69132086748737953886772281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46088057832491969257848187 69132086748737953886772281)
      ·
        refine ⟨51849065061553465415079211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69132086748737953886772281 51849065061553465415079211)
        ·
          refine ⟨77773597592330198122618817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51849065061553465415079211 77773597592330198122618817)
          ·
            refine ⟨58330198194247648591964113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77773597592330198122618817 58330198194247648591964113)
            ·
              refine ⟨43747648645685736443973085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58330198194247648591964113 43747648645685736443973085)
              ·
                refine ⟨16405368242132151166489907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43747648645685736443973085 16405368242132151166489907)
                ·
                  refine ⟨24608052363198226749734861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16405368242132151166489907 24608052363198226749734861)
                  ·
                    refine ⟨9228019636199335031150573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24608052363198226749734861 9228019636199335031150573)
                    ·
                      refine ⟨3460507363574750636681465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228019636199335031150573 3460507363574750636681465)
                      ·
                        rfl

theorem cell23_6739314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_6739314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739314 prefixEnd_6739314 := by exact prefixLift 6739314
  have htrace : WordTrace (prefixWord ++ tailWord_6739314) baseStart_6739314 baseEnd_6739314 := by
    simpa [prefixWord, tailWord_6739314, baseEnd_6739314] using wordTrace_append hprefix tailTrace_6739314
  have hstable : (prefixWord ++ tailWord_6739314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739314).length < 2 ^ (prefixWord ++ tailWord_6739314).sum := by decide
  have hdescent : baseEnd_6739314 < baseStart_6739314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739348 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6739348 : Nat := 118140960795 + 6739348 * 2 ^ 59
def prefixEnd_6739348 : Nat := 4983230072969 + 3 ^ 40 * 6739348 * 2
def baseEnd_6739348 : Nat := 3460524821917003503656309

theorem tailTrace_6739348 : CollatzResearch.WordTrace tailWord_6739348 prefixEnd_6739348 3460524821917003503656309 := by
  unfold tailWord_6739348
  simp only [CollatzResearch.WordTrace]
  refine ⟨122902107594250329924297349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163869476792333773232396465 122902107594250329924297349)
  ·
    refine ⟨23044145173921936860805753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122902107594250329924297349 23044145173921936860805753)
    ·
      refine ⟨17283108880441452645604315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23044145173921936860805753 17283108880441452645604315)
      ·
        refine ⟨25924663320662178968406473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17283108880441452645604315 25924663320662178968406473)
        ·
          refine ⟨19443497490496634226304855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25924663320662178968406473 19443497490496634226304855)
          ·
            refine ⟨29165246235744951339457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19443497490496634226304855 29165246235744951339457283)
            ·
              refine ⟨43747869353617427009185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29165246235744951339457283 43747869353617427009185925)
              ·
                refine ⟨8202725503803267564222361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43747869353617427009185925 8202725503803267564222361)
                ·
                  refine ⟨6152044127852450673166771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202725503803267564222361 6152044127852450673166771)
                  ·
                    refine ⟨9228066191778676009750157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152044127852450673166771 9228066191778676009750157)
                    ·
                      refine ⟨3460524821917003503656309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228066191778676009750157 3460524821917003503656309)
                      ·
                        rfl

theorem cell23_6739348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6739348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739348 prefixEnd_6739348 := by exact prefixLift 6739348
  have htrace : WordTrace (prefixWord ++ tailWord_6739348) baseStart_6739348 baseEnd_6739348 := by
    simpa [prefixWord, tailWord_6739348, baseEnd_6739348] using wordTrace_append hprefix tailTrace_6739348
  have hstable : (prefixWord ++ tailWord_6739348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739348).length < 2 ^ (prefixWord ++ tailWord_6739348).sum := by decide
  have hdescent : baseEnd_6739348 < baseStart_6739348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739421 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6739421 : Nat := 118140960795 + 6739421 * 2 ^ 59
def prefixEnd_6739421 : Nat := 4983230072969 + 3 ^ 40 * 6739421 * 2
def baseEnd_6739421 : Nat := 3460562306004781718043473

theorem tailTrace_6739421 : CollatzResearch.WordTrace tailWord_6739421 prefixEnd_6739421 3460562306004781718043473 := by
  unfold tailWord_6739421
  simp only [CollatzResearch.WordTrace]
  refine ⟨245806877717236193316002117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163871251811490795544001411 245806877717236193316002117)
  ·
    refine ⟨46088789571981786246750397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245806877717236193316002117 46088789571981786246750397)
    ·
      refine ⟨17283296089493169842531399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46088789571981786246750397 17283296089493169842531399)
      ·
        refine ⟨25924944134239754763797099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17283296089493169842531399 25924944134239754763797099)
        ·
          refine ⟨38887416201359632145695649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25924944134239754763797099 38887416201359632145695649)
          ·
            refine ⟨29165562151019724109271737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38887416201359632145695649 29165562151019724109271737)
            ·
              refine ⟨21874171613264793081953803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29165562151019724109271737 21874171613264793081953803)
              ·
                refine ⟨32811257419897189622930705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21874171613264793081953803 32811257419897189622930705)
                ·
                  refine ⟨24608443064922892217198029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32811257419897189622930705 24608443064922892217198029)
                  ·
                    refine ⟨9228166149346084581449261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24608443064922892217198029 9228166149346084581449261)
                    ·
                      refine ⟨3460562306004781718043473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228166149346084581449261 3460562306004781718043473)
                      ·
                        rfl

theorem cell23_6739421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6739421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739421 prefixEnd_6739421 := by exact prefixLift 6739421
  have htrace : WordTrace (prefixWord ++ tailWord_6739421) baseStart_6739421 baseEnd_6739421 := by
    simpa [prefixWord, tailWord_6739421, baseEnd_6739421] using wordTrace_append hprefix tailTrace_6739421
  have hstable : (prefixWord ++ tailWord_6739421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739421).length < 2 ^ (prefixWord ++ tailWord_6739421).sum := by decide
  have hdescent : baseEnd_6739421 < baseStart_6739421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739445 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 5]
def baseStart_6739445 : Nat := 118140960795 + 6739445 * 2 ^ 59
def prefixEnd_6739445 : Nat := 4983230072969 + 3 ^ 40 * 6739445 * 2
def baseEnd_6739445 : Nat := 384508292171165513793707

theorem tailTrace_6739445 : CollatzResearch.WordTrace tailWord_6739445 prefixEnd_6739445 384508292171165513793707 := by
  unfold tailWord_6739445
  simp only [CollatzResearch.WordTrace]
  refine ⟨245807753069149245414875789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163871835379432830276583859 245807753069149245414875789)
  ·
    refine ⟨92177907400930967030578421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245807753069149245414875789 92177907400930967030578421)
    ·
      refine ⟨8641678818837278159116727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92177907400930967030578421 8641678818837278159116727)
      ·
        refine ⟨12962518228255917238675091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8641678818837278159116727 12962518228255917238675091)
        ·
          refine ⟨19443777342383875858012637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12962518228255917238675091 19443777342383875858012637)
          ·
            refine ⟨7291416503393953446754739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19443777342383875858012637 7291416503393953446754739)
            ·
              refine ⟨10937124755090930170132109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291416503393953446754739 10937124755090930170132109)
              ·
                refine ⟨4101421783159098813799541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10937124755090930170132109 4101421783159098813799541)
                ·
                  refine ⟨384508292171165513793707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101421783159098813799541 384508292171165513793707)
                  ·
                    rfl

theorem cell23_6739445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_6739445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739445 prefixEnd_6739445 := by exact prefixLift 6739445
  have htrace : WordTrace (prefixWord ++ tailWord_6739445) baseStart_6739445 baseEnd_6739445 := by
    simpa [prefixWord, tailWord_6739445, baseEnd_6739445] using wordTrace_append hprefix tailTrace_6739445
  have hstable : (prefixWord ++ tailWord_6739445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739445).length < 2 ^ (prefixWord ++ tailWord_6739445).sum := by decide
  have hdescent : baseEnd_6739445 < baseStart_6739445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739458 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6739458 : Nat := 118140960795 + 6739458 * 2 ^ 59
def prefixEnd_6739458 : Nat := 4983230072969 + 3 ^ 40 * 6739458 * 2
def baseEnd_6739458 : Nat := 1153527101596332691093601

theorem tailTrace_6739458 : CollatzResearch.WordTrace tailWord_6739458 prefixEnd_6739458 1153527101596332691093601 := by
  unfold tailWord_6739458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61452056804525537158774757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163872151478734765756732685 61452056804525537158774757)
  ·
    refine ⟨11522260650848538217270267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61452056804525537158774757 11522260650848538217270267)
    ·
      refine ⟨17283390976272807325905401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522260650848538217270267 17283390976272807325905401)
      ·
        refine ⟨12962543232204605494429051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17283390976272807325905401 12962543232204605494429051)
        ·
          refine ⟨19443814848306908241643577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12962543232204605494429051 19443814848306908241643577)
          ·
            refine ⟨14582861136230181181232683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19443814848306908241643577 14582861136230181181232683)
            ·
              refine ⟨21874291704345271771849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582861136230181181232683 21874291704345271771849025)
              ·
                refine ⟨16405718778258953828886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21874291704345271771849025 16405718778258953828886769)
                ·
                  refine ⟨12304289083694215371665077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16405718778258953828886769 12304289083694215371665077)
                  ·
                    refine ⟨1153527101596332691093601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12304289083694215371665077 1153527101596332691093601)
                    ·
                      rfl

theorem cell23_6739458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6739458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739458 prefixEnd_6739458 := by exact prefixLift 6739458
  have htrace : WordTrace (prefixWord ++ tailWord_6739458) baseStart_6739458 baseEnd_6739458 := by
    simpa [prefixWord, tailWord_6739458, baseEnd_6739458] using wordTrace_append hprefix tailTrace_6739458
  have hstable : (prefixWord ++ tailWord_6739458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739458).length < 2 ^ (prefixWord ++ tailWord_6739458).sum := by decide
  have hdescent : baseEnd_6739458 < baseStart_6739458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739462 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6739462 : Nat := 118140960795 + 6739462 * 2 ^ 59
def prefixEnd_6739462 : Nat := 4983230072969 + 3 ^ 40 * 6739462 * 2
def baseEnd_6739462 : Nat := 384509262079068450847865

theorem tailTrace_6739462 : CollatzResearch.WordTrace tailWord_6739462 prefixEnd_6739462 384509262079068450847865 := by
  unfold tailWord_6739462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681511659690239291195145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163872248740058438212163093 7681511659690239291195145)
  ·
    refine ⟨5761133744767679468396359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7681511659690239291195145 5761133744767679468396359)
    ·
      refine ⟨8641700617151519202594539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761133744767679468396359 8641700617151519202594539)
      ·
        refine ⟨12962550925727278803891809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8641700617151519202594539 12962550925727278803891809)
        ·
          refine ⟨9721913194295459102918857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12962550925727278803891809 9721913194295459102918857)
          ·
            refine ⟨7291434895721594327189143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9721913194295459102918857 7291434895721594327189143)
            ·
              refine ⟨10937152343582391490783715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291434895721594327189143 10937152343582391490783715)
              ·
                refine ⟨16405728515373587236175573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937152343582391490783715 16405728515373587236175573)
                ·
                  refine ⟨384509262079068450847865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16405728515373587236175573 384509262079068450847865)
                  ·
                    rfl

theorem cell23_6739462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6739462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739462 prefixEnd_6739462 := by exact prefixLift 6739462
  have htrace : WordTrace (prefixWord ++ tailWord_6739462) baseStart_6739462 baseEnd_6739462 := by
    simpa [prefixWord, tailWord_6739462, baseEnd_6739462] using wordTrace_append hprefix tailTrace_6739462
  have hstable : (prefixWord ++ tailWord_6739462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739462).length < 2 ^ (prefixWord ++ tailWord_6739462).sum := by decide
  have hdescent : baseEnd_6739462 < baseStart_6739462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739498 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6739498 : Nat := 118140960795 + 6739498 * 2 ^ 59
def prefixEnd_6739498 : Nat := 4983230072969 + 3 ^ 40 * 6739498 * 2
def baseEnd_6739498 : Nat := 3460601844015177916780619

theorem tailTrace_6739498 : CollatzResearch.WordTrace tailWord_6739498 prefixEnd_6739498 3460601844015177916780619 := by
  unfold tailWord_6739498
  simp only [CollatzResearch.WordTrace]
  refine ⟨61452421534489308866638787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163873124091971490311036765 61452421534489308866638787)
  ·
    refine ⟨92178632301733963299958181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61452421534489308866638787 92178632301733963299958181)
    ·
      refine ⟨17283493556575118118742159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92178632301733963299958181 17283493556575118118742159)
      ·
        refine ⟨25925240334862677178113239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17283493556575118118742159 25925240334862677178113239)
        ·
          refine ⟨38887860502294015767169859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925240334862677178113239 38887860502294015767169859)
          ·
            refine ⟨58331790753441023650754789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38887860502294015767169859 58331790753441023650754789)
            ·
              refine ⟨10937210766270191934516523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58331790753441023650754789 10937210766270191934516523)
              ·
                refine ⟨16405816149405287901774785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937210766270191934516523 16405816149405287901774785)
                ·
                  refine ⟨12304362112053965926331089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16405816149405287901774785 12304362112053965926331089)
                  ·
                    refine ⟨9228271584040474444748317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12304362112053965926331089 9228271584040474444748317)
                    ·
                      refine ⟨3460601844015177916780619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228271584040474444748317 3460601844015177916780619)
                      ·
                        rfl

theorem cell23_6739498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6739498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739498 prefixEnd_6739498 := by exact prefixLift 6739498
  have htrace : WordTrace (prefixWord ++ tailWord_6739498) baseStart_6739498 baseEnd_6739498 := by
    simpa [prefixWord, tailWord_6739498, baseEnd_6739498] using wordTrace_append hprefix tailTrace_6739498
  have hstable : (prefixWord ++ tailWord_6739498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739498).length < 2 ^ (prefixWord ++ tailWord_6739498).sum := by decide
  have hdescent : baseEnd_6739498 < baseStart_6739498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739549 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6739549 : Nat := 118140960795 + 6739549 * 2 ^ 59
def prefixEnd_6739549 : Nat := 4983230072969 + 3 ^ 40 * 6739549 * 2
def baseEnd_6739549 : Nat := 3460628031528557217242885

theorem tailTrace_6739549 : CollatzResearch.WordTrace tailWord_6739549 prefixEnd_6739549 3460628031528557217242885 := by
  unfold tailWord_6739549
  simp only [CollatzResearch.WordTrace]
  refine ⟨245811546260772471176661701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163874364173848314117774467 245811546260772471176661701)
  ·
    refine ⟨46089664923894838345624069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245811546260772471176661701 46089664923894838345624069)
    ·
      refine ⟨8641812173230282189804513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46089664923894838345624069 8641812173230282189804513)
      ·
        refine ⟨6481359129922711642353385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8641812173230282189804513 6481359129922711642353385)
        ·
          refine ⟨4861019347442033731765039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6481359129922711642353385 4861019347442033731765039)
          ·
            refine ⟨7291529021163050597647559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861019347442033731765039 7291529021163050597647559)
            ·
              refine ⟨10937293531744575896471339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291529021163050597647559 10937293531744575896471339)
              ·
                refine ⟨16405940297616863844707009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937293531744575896471339 16405940297616863844707009)
                ·
                  refine ⟨12304455223212647883530257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16405940297616863844707009 12304455223212647883530257)
                  ·
                    refine ⟨9228341417409485912647693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12304455223212647883530257 9228341417409485912647693)
                    ·
                      refine ⟨3460628031528557217242885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228341417409485912647693 3460628031528557217242885)
                      ·
                        rfl

theorem cell23_6739549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6739549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739549 prefixEnd_6739549 := by exact prefixLift 6739549
  have htrace : WordTrace (prefixWord ++ tailWord_6739549) baseStart_6739549 baseEnd_6739549 := by
    simpa [prefixWord, tailWord_6739549, baseEnd_6739549] using wordTrace_append hprefix tailTrace_6739549
  have hstable : (prefixWord ++ tailWord_6739549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739549).length < 2 ^ (prefixWord ++ tailWord_6739549).sum := by decide
  have hdescent : baseEnd_6739549 < baseStart_6739549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739555 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6739555 : Nat := 118140960795 + 6739555 * 2 ^ 59
def prefixEnd_6739555 : Nat := 4983230072969 + 3 ^ 40 * 6739555 * 2
def baseEnd_6739555 : Nat := 3460631112412484193767857

theorem tailTrace_6739555 : CollatzResearch.WordTrace tailWord_6739555 prefixEnd_6739555 3460631112412484193767857 := by
  unfold tailWord_6739555
  simp only [CollatzResearch.WordTrace]
  refine ⟨245811765098750734201380119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163874510065833822800920079 245811765098750734201380119)
  ·
    refine ⟨368717647648126101302070179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245811765098750734201380119 368717647648126101302070179)
    ·
      refine ⟨553076471472189151953105269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368717647648126101302070179 553076471472189151953105269)
      ·
        refine ⟨51850919200517732995603619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 553076471472189151953105269 51850919200517732995603619)
        ·
          refine ⟨77776378800776599493405429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51850919200517732995603619 77776378800776599493405429)
          ·
            refine ⟨7291535512572806202506759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77776378800776599493405429 7291535512572806202506759)
            ·
              refine ⟨10937303268859209303760139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291535512572806202506759 10937303268859209303760139)
              ·
                refine ⟨16405954903288813955640209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937303268859209303760139 16405954903288813955640209)
                ·
                  refine ⟨12304466177466610466730157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16405954903288813955640209 12304466177466610466730157)
                  ·
                    refine ⟨4614174816549978925023809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12304466177466610466730157 4614174816549978925023809)
                    ·
                      refine ⟨3460631112412484193767857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614174816549978925023809 3460631112412484193767857)
                      ·
                        rfl

theorem cell23_6739555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6739555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739555 prefixEnd_6739555 := by exact prefixLift 6739555
  have htrace : WordTrace (prefixWord ++ tailWord_6739555) baseStart_6739555 baseEnd_6739555 := by
    simpa [prefixWord, tailWord_6739555, baseEnd_6739555] using wordTrace_append hprefix tailTrace_6739555
  have hstable : (prefixWord ++ tailWord_6739555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739555).length < 2 ^ (prefixWord ++ tailWord_6739555).sum := by decide
  have hdescent : baseEnd_6739555 < baseStart_6739555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739562 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6739562 : Nat := 118140960795 + 6739562 * 2 ^ 59
def prefixEnd_6739562 : Nat := 4983230072969 + 3 ^ 40 * 6739562 * 2
def baseEnd_6739562 : Nat := 3460634706777065666380325

theorem tailTrace_6739562 : CollatzResearch.WordTrace tailWord_6739562 prefixEnd_6739562 3460634706777065666380325 := by
  unfold tailWord_6739562
  simp only [CollatzResearch.WordTrace]
  refine ⟨61453005102431343599221235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163874680273150249597923293 61453005102431343599221235)
  ·
    refine ⟨92179507653647015398831853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61453005102431343599221235 92179507653647015398831853)
    ·
      refine ⟨34567315370117630774561945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92179507653647015398831853 34567315370117630774561945)
      ·
        refine ⟨25925486527588223080921459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34567315370117630774561945 25925486527588223080921459)
        ·
          refine ⟨38888229791382334621382189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925486527588223080921459 38888229791382334621382189)
          ·
            refine ⟨14583086171768375483018321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38888229791382334621382189 14583086171768375483018321)
            ·
              refine ⟨10937314628826281612263741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14583086171768375483018321 10937314628826281612263741)
              ·
                refine ⟨4101492985809855604598903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10937314628826281612263741 4101492985809855604598903)
                ·
                  refine ⟨6152239478714783406898355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101492985809855604598903 6152239478714783406898355)
                  ·
                    refine ⟨9228359218072175110347533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152239478714783406898355 9228359218072175110347533)
                    ·
                      refine ⟨3460634706777065666380325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228359218072175110347533 3460634706777065666380325)
                      ·
                        rfl

theorem cell23_6739562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6739562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739562 prefixEnd_6739562 := by exact prefixLift 6739562
  have htrace : WordTrace (prefixWord ++ tailWord_6739562) baseStart_6739562 baseEnd_6739562 := by
    simpa [prefixWord, tailWord_6739562, baseEnd_6739562] using wordTrace_append hprefix tailTrace_6739562
  have hstable : (prefixWord ++ tailWord_6739562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739562).length < 2 ^ (prefixWord ++ tailWord_6739562).sum := by decide
  have hdescent : baseEnd_6739562 < baseStart_6739562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739564 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6739564 : Nat := 118140960795 + 6739564 * 2 ^ 59
def prefixEnd_6739564 : Nat := 4983230072969 + 3 ^ 40 * 6739564 * 2
def baseEnd_6739564 : Nat := 3460635733738374658555315

theorem tailTrace_6739564 : CollatzResearch.WordTrace tailWord_6739564 prefixEnd_6739564 3460635733738374658555315 := by
  unfold tailWord_6739564
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906046677859064369228873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163874728903812085825638497 122906046677859064369228873)
  ·
    refine ⟨92179535008394298276921655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122906046677859064369228873 92179535008394298276921655)
    ·
      refine ⟨138269302512591447415382483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92179535008394298276921655 138269302512591447415382483)
      ·
        refine ⟨207403953768887171123073725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138269302512591447415382483 207403953768887171123073725)
        ·
          refine ⟨77776482663332689171152647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207403953768887171123073725 77776482663332689171152647)
          ·
            refine ⟨116664723994999033756728971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77776482663332689171152647 116664723994999033756728971)
            ·
              refine ⟨174997085992498550635093457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116664723994999033756728971 174997085992498550635093457)
              ·
                refine ⟨131247814494373912976320093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174997085992498550635093457 131247814494373912976320093)
                ·
                  refine ⟨49217930435390217366120035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131247814494373912976320093 49217930435390217366120035)
                  ·
                    refine ⟨73826895653085326049180053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49217930435390217366120035 73826895653085326049180053)
                    ·
                      refine ⟨3460635733738374658555315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73826895653085326049180053 3460635733738374658555315)
                      ·
                        rfl

theorem cell23_6739564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6739564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739564 prefixEnd_6739564 := by exact prefixLift 6739564
  have htrace : WordTrace (prefixWord ++ tailWord_6739564) baseStart_6739564 baseEnd_6739564 := by
    simpa [prefixWord, tailWord_6739564, baseEnd_6739564] using wordTrace_append hprefix tailTrace_6739564
  have hstable : (prefixWord ++ tailWord_6739564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739564).length < 2 ^ (prefixWord ++ tailWord_6739564).sum := by decide
  have hdescent : baseEnd_6739564 < baseStart_6739564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739568 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_6739568 : Nat := 118140960795 + 6739568 * 2 ^ 59
def prefixEnd_6739568 : Nat := 4983230072969 + 3 ^ 40 * 6739568 * 2
def baseEnd_6739568 : Nat := 3460637787660992642905297

theorem tailTrace_6739568 : CollatzResearch.WordTrace tailWord_6739568 prefixEnd_6739568 3460637787660992642905297 := by
  unfold tailWord_6739568
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906119623851818710801679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163874826165135758281068905 122906119623851818710801679)
  ·
    refine ⟨184359179435777728066202519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122906119623851818710801679 184359179435777728066202519)
    ·
      refine ⟨276538769153666592099303779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184359179435777728066202519 276538769153666592099303779)
      ·
        refine ⟨414808153730499888148955669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276538769153666592099303779 414808153730499888148955669)
        ·
          refine ⟨19444132206117182256982297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 414808153730499888148955669 19444132206117182256982297)
          ·
            refine ⟨14583099154587886692736723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19444132206117182256982297 14583099154587886692736723)
            ·
              refine ⟨21874648731881830039105085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14583099154587886692736723 21874648731881830039105085)
              ·
                refine ⟨8202993274455686264664407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21874648731881830039105085 8202993274455686264664407)
                ·
                  refine ⟨12304489911683529396996611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8202993274455686264664407 12304489911683529396996611)
                  ·
                    refine ⟨18456734867525294095494917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12304489911683529396996611 18456734867525294095494917)
                    ·
                      refine ⟨3460637787660992642905297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18456734867525294095494917 3460637787660992642905297)
                      ·
                        rfl

theorem cell23_6739568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_6739568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739568 prefixEnd_6739568 := by exact prefixLift 6739568
  have htrace : WordTrace (prefixWord ++ tailWord_6739568) baseStart_6739568 baseEnd_6739568 := by
    simpa [prefixWord, tailWord_6739568, baseEnd_6739568] using wordTrace_append hprefix tailTrace_6739568
  have hstable : (prefixWord ++ tailWord_6739568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739568).length < 2 ^ (prefixWord ++ tailWord_6739568).sum := by decide
  have hdescent : baseEnd_6739568 < baseStart_6739568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739585 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6739585 : Nat := 118140960795 + 6739585 * 2 ^ 59
def prefixEnd_6739585 : Nat := 4983230072969 + 3 ^ 40 * 6739585 * 2
def baseEnd_6739585 : Nat := 3460646516832119076392719

theorem tailTrace_6739585 : CollatzResearch.WordTrace tailWord_6739585 prefixEnd_6739585 3460646516832119076392719 := by
  unfold tailWord_6739585
  simp only [CollatzResearch.WordTrace]
  refine ⟨245812859288642049324972209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163875239525761366216648139 245812859288642049324972209)
  ·
    refine ⟨184359644466481536993729157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245812859288642049324972209 184359644466481536993729157)
    ·
      refine ⟨34567433337465288186324217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184359644466481536993729157 34567433337465288186324217)
      ·
        refine ⟨25925575003098966139743163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34567433337465288186324217 25925575003098966139743163)
        ·
          refine ⟨38888362504648449209614745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925575003098966139743163 38888362504648449209614745)
          ·
            refine ⟨29166271878486336907211059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38888362504648449209614745 29166271878486336907211059)
            ·
              refine ⟨43749407817729505360816589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29166271878486336907211059 43749407817729505360816589)
              ·
                refine ⟨16406027931648564510306221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43749407817729505360816589 16406027931648564510306221)
                ·
                  refine ⟨6152260474368211691364833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16406027931648564510306221 6152260474368211691364833)
                  ·
                    refine ⟨4614195355776158768523625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152260474368211691364833 4614195355776158768523625)
                    ·
                      refine ⟨3460646516832119076392719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614195355776158768523625 3460646516832119076392719)
                      ·
                        rfl

theorem cell23_6739585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6739585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739585 prefixEnd_6739585 := by exact prefixLift 6739585
  have htrace : WordTrace (prefixWord ++ tailWord_6739585) baseStart_6739585 baseEnd_6739585 := by
    simpa [prefixWord, tailWord_6739585, baseEnd_6739585] using wordTrace_append hprefix tailTrace_6739585
  have hstable : (prefixWord ++ tailWord_6739585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739585).length < 2 ^ (prefixWord ++ tailWord_6739585).sum := by decide
  have hdescent : baseEnd_6739585 < baseStart_6739585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739588 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6739588 : Nat := 118140960795 + 6739588 * 2 ^ 59
def prefixEnd_6739588 : Nat := 4983230072969 + 3 ^ 40 * 6739588 * 2
def baseEnd_6739588 : Nat := 3460648057274082564655205

theorem tailTrace_6739588 : CollatzResearch.WordTrace tailWord_6739588 prefixEnd_6739588 3460648057274082564655205 := by
  unfold tailWord_6739588
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906484353815590418665709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163875312471754120558220945 122906484353815590418665709)
  ·
    refine ⟨46089931632680846406999641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122906484353815590418665709 46089931632680846406999641)
    ·
      refine ⟨34567448724510634805249731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46089931632680846406999641 34567448724510634805249731)
      ·
        refine ⟨51851173086765952207874597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34567448724510634805249731 51851173086765952207874597)
        ·
          refine ⟨9722094953768616038976487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51851173086765952207874597 9722094953768616038976487)
          ·
            refine ⟨14583142430652924058464731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9722094953768616038976487 14583142430652924058464731)
            ·
              refine ⟨21874713645979386087697097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14583142430652924058464731 21874713645979386087697097)
              ·
                refine ⟨16406035234484539565772823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21874713645979386087697097 16406035234484539565772823)
                ·
                  refine ⟨24609052851726809348659235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16406035234484539565772823 24609052851726809348659235)
                  ·
                    refine ⟨36913579277590214022988853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24609052851726809348659235 36913579277590214022988853)
                    ·
                      refine ⟨3460648057274082564655205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36913579277590214022988853 3460648057274082564655205)
                      ·
                        rfl

theorem cell23_6739588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6739588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739588 prefixEnd_6739588 := by exact prefixLift 6739588
  have htrace : WordTrace (prefixWord ++ tailWord_6739588) baseStart_6739588 baseEnd_6739588 := by
    simpa [prefixWord, tailWord_6739588, baseEnd_6739588] using wordTrace_append hprefix tailTrace_6739588
  have hstable : (prefixWord ++ tailWord_6739588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739588).length < 2 ^ (prefixWord ++ tailWord_6739588).sum := by decide
  have hdescent : baseEnd_6739588 < baseStart_6739588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739598 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6739598 : Nat := 118140960795 + 6739598 * 2 ^ 59
def prefixEnd_6739598 : Nat := 4983230072969 + 3 ^ 40 * 6739598 * 2
def baseEnd_6739598 : Nat := 3460653192080627525530159

theorem tailTrace_6739598 : CollatzResearch.WordTrace tailWord_6739598 prefixEnd_6739598 3460653192080627525530159 := by
  unfold tailWord_6739598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30726666679699369068149431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163875555625063301696796965 30726666679699369068149431)
  ·
    refine ⟨46090000019549053602224147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30726666679699369068149431 46090000019549053602224147)
    ·
      refine ⟨69135000029323580403336221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46090000019549053602224147 69135000029323580403336221)
      ·
        refine ⟨25925625010996342651251083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69135000029323580403336221 25925625010996342651251083)
        ·
          refine ⟨38888437516494513976876625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925625010996342651251083 38888437516494513976876625)
          ·
            refine ⟨29166328137370885482657469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38888437516494513976876625 29166328137370885482657469)
            ·
              refine ⟨10937373051514082055996551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29166328137370885482657469 10937373051514082055996551)
              ·
                refine ⟨16406059577271123083994827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937373051514082055996551 16406059577271123083994827)
                ·
                  refine ⟨24609089365906684625992241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16406059577271123083994827 24609089365906684625992241)
                  ·
                    refine ⟨18456817024430013469494181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24609089365906684625992241 18456817024430013469494181)
                    ·
                      refine ⟨3460653192080627525530159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18456817024430013469494181 3460653192080627525530159)
                      ·
                        rfl

theorem cell23_6739598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6739598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739598 prefixEnd_6739598 := by exact prefixLift 6739598
  have htrace : WordTrace (prefixWord ++ tailWord_6739598) baseStart_6739598 baseEnd_6739598 := by
    simpa [prefixWord, tailWord_6739598, baseEnd_6739598] using wordTrace_append hprefix tailTrace_6739598
  have hstable : (prefixWord ++ tailWord_6739598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739598).length < 2 ^ (prefixWord ++ tailWord_6739598).sum := by decide
  have hdescent : baseEnd_6739598 < baseStart_6739598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739601 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_6739601 : Nat := 118140960795 + 6739601 * 2 ^ 59
def prefixEnd_6739601 : Nat := 4983230072969 + 3 ^ 40 * 6739601 * 2
def baseEnd_6739601 : Nat := 3460654732522591013792645

theorem tailTrace_6739601 : CollatzResearch.WordTrace tailWord_6739601 prefixEnd_6739601 3460654732522591013792645 := by
  unfold tailWord_6739601
  simp only [CollatzResearch.WordTrace]
  refine ⟨245813442856584084057554657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163875628571056056038369771 245813442856584084057554657)
  ·
    refine ⟨184360082142438063043165993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245813442856584084057554657 184360082142438063043165993)
    ·
      refine ⟨138270061606828547282374495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184360082142438063043165993 138270061606828547282374495)
      ·
        refine ⟨207405092410242820923561743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138270061606828547282374495 207405092410242820923561743)
        ·
          refine ⟨311107638615364231385342615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207405092410242820923561743 311107638615364231385342615)
          ·
            refine ⟨466661457923046347078013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311107638615364231385342615 466661457923046347078013923)
            ·
              refine ⟨699992186884569520617020885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466661457923046347078013923 699992186884569520617020885)
              ·
                refine ⟨16406066880107098139461427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 699992186884569520617020885 16406066880107098139461427)
                ·
                  refine ⟨24609100320160647209192141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16406066880107098139461427 24609100320160647209192141)
                  ·
                    refine ⟨9228412620060242703447053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24609100320160647209192141 9228412620060242703447053)
                    ·
                      refine ⟨3460654732522591013792645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228412620060242703447053 3460654732522591013792645)
                      ·
                        rfl

theorem cell23_6739601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_6739601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739601 prefixEnd_6739601 := by exact prefixLift 6739601
  have htrace : WordTrace (prefixWord ++ tailWord_6739601) baseStart_6739601 baseEnd_6739601 := by
    simpa [prefixWord, tailWord_6739601, baseEnd_6739601] using wordTrace_append hprefix tailTrace_6739601
  have hstable : (prefixWord ++ tailWord_6739601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739601).length < 2 ^ (prefixWord ++ tailWord_6739601).sum := by decide
  have hdescent : baseEnd_6739601 < baseStart_6739601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739608 : List Nat := [2, 1, 2, 4, 1, 4, 2, 7]
def baseStart_6739608 : Nat := 118140960795 + 6739608 * 2 ^ 59
def prefixEnd_6739608 : Nat := 4983230072969 + 3 ^ 40 * 6739608 * 2
def baseEnd_6739608 : Nat := 128172530625450832829819

theorem tailTrace_6739608 : CollatzResearch.WordTrace tailWord_6739608 prefixEnd_6739608 128172530625450832829819 := by
  unfold tailWord_6739608
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906849083779362126529739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163875798778372482835372985 122906849083779362126529739)
  ·
    refine ⟨184360273625669043189794609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122906849083779362126529739 184360273625669043189794609)
    ·
      refine ⟨138270205219251782392345957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184360273625669043189794609 138270205219251782392345957)
      ·
        refine ⟨25925663478609709198564867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138270205219251782392345957 25925663478609709198564867)
        ·
          refine ⟨38888495217914563797847301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25925663478609709198564867 38888495217914563797847301)
          ·
            refine ⟨7291592853358980712096369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38888495217914563797847301 7291592853358980712096369)
            ·
              refine ⟨5468694640019235534072277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291592853358980712096369 5468694640019235534072277)
              ·
                refine ⟨128172530625450832829819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5468694640019235534072277 128172530625450832829819)
                ·
                  rfl

theorem cell23_6739608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 7].length) (baseStart_6739608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739608 prefixEnd_6739608 := by exact prefixLift 6739608
  have htrace : WordTrace (prefixWord ++ tailWord_6739608) baseStart_6739608 baseEnd_6739608 := by
    simpa [prefixWord, tailWord_6739608, baseEnd_6739608] using wordTrace_append hprefix tailTrace_6739608
  have hstable : (prefixWord ++ tailWord_6739608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739608).length < 2 ^ (prefixWord ++ tailWord_6739608).sum := by decide
  have hdescent : baseEnd_6739608 < baseStart_6739608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739708 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_6739708 : Nat := 118140960795 + 6739708 * 2 ^ 59
def prefixEnd_6739708 : Nat := 4983230072969 + 3 ^ 40 * 6739708 * 2
def baseEnd_6739708 : Nat := 3460709674952622095154653

theorem tailTrace_6739708 : CollatzResearch.WordTrace tailWord_6739708 prefixEnd_6739708 3460709674952622095154653 := by
  unfold tailWord_6739708
  simp only [CollatzResearch.WordTrace]
  refine ⟨122908672733598220665849889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163878230311464294221133185 122908672733598220665849889)
  ·
    refine ⟨92181504550198665499387417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122908672733598220665849889 92181504550198665499387417)
    ·
      refine ⟨69136128412648999124540563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92181504550198665499387417 69136128412648999124540563)
      ·
        refine ⟨103704192618973498686810845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69136128412648999124540563 103704192618973498686810845)
        ·
          refine ⟨38889072232115062007554067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103704192618973498686810845 38889072232115062007554067)
          ·
            refine ⟨58333608348172593011331101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38889072232115062007554067 58333608348172593011331101)
            ·
              refine ⟨21875103130564722379249163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58333608348172593011331101 21875103130564722379249163)
              ·
                refine ⟨32812654695847083568873745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21875103130564722379249163 32812654695847083568873745)
                ·
                  refine ⟨24609491021885312676655309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32812654695847083568873745 24609491021885312676655309)
                  ·
                    refine ⟨9228559133206992253745741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24609491021885312676655309 9228559133206992253745741)
                    ·
                      refine ⟨3460709674952622095154653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228559133206992253745741 3460709674952622095154653)
                      ·
                        rfl

theorem cell23_6739708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_6739708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739708 prefixEnd_6739708 := by exact prefixLift 6739708
  have htrace : WordTrace (prefixWord ++ tailWord_6739708) baseStart_6739708 baseEnd_6739708 := by
    simpa [prefixWord, tailWord_6739708, baseEnd_6739708] using wordTrace_append hprefix tailTrace_6739708
  have hstable : (prefixWord ++ tailWord_6739708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739708).length < 2 ^ (prefixWord ++ tailWord_6739708).sum := by decide
  have hdescent : baseEnd_6739708 < baseStart_6739708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739711 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 4, 5]
def baseStart_6739711 : Nat := 118140960795 + 6739711 * 2 ^ 59
def prefixEnd_6739711 : Nat := 4983230072969 + 3 ^ 40 * 6739711 * 2
def baseEnd_6739711 : Nat := 1153570405131528527805713

theorem tailTrace_6739711 : CollatzResearch.WordTrace tailWord_6739711 prefixEnd_6739711 1153570405131528527805713 := by
  unfold tailWord_6739711
  simp only [CollatzResearch.WordTrace]
  refine ⟨245817454886185572844058987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163878303257457048562705991 245817454886185572844058987)
  ·
    refine ⟨368726182329278359266088481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245817454886185572844058987 368726182329278359266088481)
    ·
      refine ⟨276544636746958769449566361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368726182329278359266088481 276544636746958769449566361)
      ·
        refine ⟨207408477560219077087174771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276544636746958769449566361 207408477560219077087174771)
        ·
          refine ⟨311112716340328615630762157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207408477560219077087174771 311112716340328615630762157)
          ·
            refine ⟨116667268627623230861535809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311112716340328615630762157 116667268627623230861535809)
            ·
              refine ⟨87500451470717423146151857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116667268627623230861535809 87500451470717423146151857)
              ·
                refine ⟨65625338603038067359613893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87500451470717423146151857 65625338603038067359613893)
                ·
                  refine ⟨12304750988069637629927605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65625338603038067359613893 12304750988069637629927605)
                  ·
                    refine ⟨1153570405131528527805713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12304750988069637629927605 1153570405131528527805713)
                    ·
                      rfl

theorem cell23_6739711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_6739711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739711 prefixEnd_6739711 := by exact prefixLift 6739711
  have htrace : WordTrace (prefixWord ++ tailWord_6739711) baseStart_6739711 baseEnd_6739711 := by
    simpa [prefixWord, tailWord_6739711, baseEnd_6739711] using wordTrace_append hprefix tailTrace_6739711
  have hstable : (prefixWord ++ tailWord_6739711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739711).length < 2 ^ (prefixWord ++ tailWord_6739711).sum := by decide
  have hdescent : baseEnd_6739711 < baseStart_6739711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739768 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_6739768 : Nat := 118140960795 + 6739768 * 2 ^ 59
def prefixEnd_6739768 : Nat := 4983230072969 + 3 ^ 40 * 6739768 * 2
def baseEnd_6739768 : Nat := 3460740483791891860404377

theorem tailTrace_6739768 : CollatzResearch.WordTrace tailWord_6739768 prefixEnd_6739768 3460740483791891860404377 := by
  unfold tailWord_6739768
  simp only [CollatzResearch.WordTrace]
  refine ⟨122909766923489535789441979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163879689231319381052589305 122909766923489535789441979)
  ·
    refine ⟨184364650385234303684162969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122909766923489535789441979 184364650385234303684162969)
    ·
      refine ⟨138273487788925727763122227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184364650385234303684162969 138273487788925727763122227)
      ·
        refine ⟨207410231683388591644683341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138273487788925727763122227 207410231683388591644683341)
        ·
          refine ⟨77778836881270721866756253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207410231683388591644683341 77778836881270721866756253)
          ·
            refine ⟨29167063830476520700033595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77778836881270721866756253 29167063830476520700033595)
            ·
              refine ⟨43750595745714781050050393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29167063830476520700033595 43750595745714781050050393)
              ·
                refine ⟨32812946809286085787537795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43750595745714781050050393 32812946809286085787537795)
                ·
                  refine ⟨49219420213929128681306693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32812946809286085787537795 49219420213929128681306693)
                  ·
                    refine ⟨9228641290111711627745005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49219420213929128681306693 9228641290111711627745005)
                    ·
                      refine ⟨3460740483791891860404377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228641290111711627745005 3460740483791891860404377)
                      ·
                        rfl

theorem cell23_6739768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_6739768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739768 prefixEnd_6739768 := by exact prefixLift 6739768
  have htrace : WordTrace (prefixWord ++ tailWord_6739768) baseStart_6739768 baseEnd_6739768 := by
    simpa [prefixWord, tailWord_6739768, baseEnd_6739768] using wordTrace_append hprefix tailTrace_6739768
  have hstable : (prefixWord ++ tailWord_6739768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739768).length < 2 ^ (prefixWord ++ tailWord_6739768).sum := by decide
  have hdescent : baseEnd_6739768 < baseStart_6739768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739782 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6739782 : Nat := 118140960795 + 6739782 * 2 ^ 59
def prefixEnd_6739782 : Nat := 4983230072969 + 3 ^ 40 * 6739782 * 2
def baseEnd_6739782 : Nat := 3460747672521054805629313

theorem tailTrace_6739782 : CollatzResearch.WordTrace tailWord_6739782 prefixEnd_6739782 3460747672521054805629313 := by
  unfold tailWord_6739782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681876389654010999059175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163880029645952234646595733 7681876389654010999059175)
  ·
    refine ⟨11522814584481016498588763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681876389654010999059175 11522814584481016498588763)
    ·
      refine ⟨17284221876721524747883145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522814584481016498588763 17284221876721524747883145)
      ·
        refine ⟨12963166407541143560912359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17284221876721524747883145 12963166407541143560912359)
        ·
          refine ⟨19444749611311715341368539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963166407541143560912359 19444749611311715341368539)
          ·
            refine ⟨29167124416967573012052809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444749611311715341368539 29167124416967573012052809)
            ·
              refine ⟨21875343312725679759039607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29167124416967573012052809 21875343312725679759039607)
              ·
                refine ⟨32813014969088519638559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21875343312725679759039607 32813014969088519638559411)
                ·
                  refine ⟨49219522453632779457839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32813014969088519638559411 49219522453632779457839117)
                  ·
                    refine ⟨18457320920112292296689669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49219522453632779457839117 18457320920112292296689669)
                    ·
                      refine ⟨3460747672521054805629313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18457320920112292296689669 3460747672521054805629313)
                      ·
                        rfl

theorem cell23_6739782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6739782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739782 prefixEnd_6739782 := by exact prefixLift 6739782
  have htrace : WordTrace (prefixWord ++ tailWord_6739782) baseStart_6739782 baseEnd_6739782 := by
    simpa [prefixWord, tailWord_6739782, baseEnd_6739782] using wordTrace_append hprefix tailTrace_6739782
  have hstable : (prefixWord ++ tailWord_6739782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739782).length < 2 ^ (prefixWord ++ tailWord_6739782).sum := by decide
  have hdescent : baseEnd_6739782 < baseStart_6739782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739822 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_6739822 : Nat := 118140960795 + 6739822 * 2 ^ 59
def prefixEnd_6739822 : Nat := 4983230072969 + 3 ^ 40 * 6739822 * 2
def baseEnd_6739822 : Nat := 384529801305248294347681

theorem tailTrace_6739822 : CollatzResearch.WordTrace tailWord_6739822 prefixEnd_6739822 384529801305248294347681 := by
  unfold tailWord_6739822
  simp only [CollatzResearch.WordTrace]
  refine ⟨30727687923597929850168715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163881002259188959200899813 30727687923597929850168715)
  ·
    refine ⟨46091531885396894775253073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30727687923597929850168715 46091531885396894775253073)
    ·
      refine ⟨34568648914047671081439805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46091531885396894775253073 34568648914047671081439805)
      ·
        refine ⟨12963243342767876655539927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34568648914047671081439805 12963243342767876655539927)
        ·
          refine ⟨19444865014151814983309891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963243342767876655539927 19444865014151814983309891)
          ·
            refine ⟨29167297521227722474964837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444865014151814983309891 29167297521227722474964837)
            ·
              refine ⟨5468868285230197964055907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29167297521227722474964837 5468868285230197964055907)
              ·
                refine ⟨8203302427845296946083861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468868285230197964055907 8203302427845296946083861)
                ·
                  refine ⟨384529801305248294347681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8203302427845296946083861 384529801305248294347681)
                  ·
                    rfl

theorem cell23_6739822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_6739822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739822 prefixEnd_6739822 := by exact prefixLift 6739822
  have htrace : WordTrace (prefixWord ++ tailWord_6739822) baseStart_6739822 baseEnd_6739822 := by
    simpa [prefixWord, tailWord_6739822, baseEnd_6739822] using wordTrace_append hprefix tailTrace_6739822
  have hstable : (prefixWord ++ tailWord_6739822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739822).length < 2 ^ (prefixWord ++ tailWord_6739822).sum := by decide
  have hdescent : baseEnd_6739822 < baseStart_6739822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739825 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_6739825 : Nat := 118140960795 + 6739825 * 2 ^ 59
def prefixEnd_6739825 : Nat := 4983230072969 + 3 ^ 40 * 6739825 * 2
def baseEnd_6739825 : Nat := 3460769752189198137391615

theorem tailTrace_6739825 : CollatzResearch.WordTrace tailWord_6739825 prefixEnd_6739825 3460769752189198137391615 := by
  unfold tailWord_6739825
  simp only [CollatzResearch.WordTrace]
  refine ⟨245821612807772570313708929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163881075205181713542472619 245821612807772570313708929)
  ·
    refine ⟨184366209605829427735281697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245821612807772570313708929 184366209605829427735281697)
    ·
      refine ⟨138274657204372070801461273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184366209605829427735281697 138274657204372070801461273)
      ·
        refine ⟨103705992903279053101095955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138274657204372070801461273 103705992903279053101095955)
        ·
          refine ⟨155558989354918579651643933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103705992903279053101095955 155558989354918579651643933)
          ·
            refine ⟨58334621008094467369366475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155558989354918579651643933 58334621008094467369366475)
            ·
              refine ⟨87501931512141701054049713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58334621008094467369366475 87501931512141701054049713)
              ·
                refine ⟨65626448634106275790537285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87501931512141701054049713 65626448634106275790537285)
                ·
                  refine ⟨12304959118894926710725741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65626448634106275790537285 12304959118894926710725741)
                  ·
                    refine ⟨4614359669585597516522153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12304959118894926710725741 4614359669585597516522153)
                    ·
                      refine ⟨3460769752189198137391615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614359669585597516522153 3460769752189198137391615)
                      ·
                        rfl

theorem cell23_6739825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_6739825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739825 prefixEnd_6739825 := by exact prefixLift 6739825
  have htrace : WordTrace (prefixWord ++ tailWord_6739825) baseStart_6739825 baseEnd_6739825 := by
    simpa [prefixWord, tailWord_6739825, baseEnd_6739825] using wordTrace_append hprefix tailTrace_6739825
  have hstable : (prefixWord ++ tailWord_6739825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739825).length < 2 ^ (prefixWord ++ tailWord_6739825).sum := by decide
  have hdescent : baseEnd_6739825 < baseStart_6739825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739865 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_6739865 : Nat := 118140960795 + 6739865 * 2 ^ 59
def prefixEnd_6739865 : Nat := 4983230072969 + 3 ^ 40 * 6739865 * 2
def baseEnd_6739865 : Nat := 1153596763805125993630477

theorem tailTrace_6739865 : CollatzResearch.WordTrace tailWord_6739865 prefixEnd_6739865 1153596763805125993630477 := by
  unfold tailWord_6739865
  simp only [CollatzResearch.WordTrace]
  refine ⟨245823071727627657145165049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163882047818418438096776699 245823071727627657145165049)
  ·
    refine ⟨184367303795720742858873787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245823071727627657145165049 184367303795720742858873787)
    ·
      refine ⟨276550955693581114288310681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184367303795720742858873787 276550955693581114288310681)
      ·
        refine ⟨207413216770185835716233011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276550955693581114288310681 207413216770185835716233011)
        ·
          refine ⟨311119825155278753574349517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207413216770185835716233011 311119825155278753574349517)
          ·
            refine ⟨116669934433229532590381069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311119825155278753574349517 116669934433229532590381069)
            ·
              refine ⟨43751225412461074721392901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116669934433229532590381069 43751225412461074721392901)
              ·
                refine ⟨8203354764836451510261169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43751225412461074721392901 8203354764836451510261169)
                ·
                  refine ⟨6152516073627338632695877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8203354764836451510261169 6152516073627338632695877)
                  ·
                    refine ⟨1153596763805125993630477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152516073627338632695877 1153596763805125993630477)
                    ·
                      rfl

theorem cell23_6739865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_6739865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739865 prefixEnd_6739865 := by exact prefixLift 6739865
  have htrace : WordTrace (prefixWord ++ tailWord_6739865) baseStart_6739865 baseEnd_6739865 := by
    simpa [prefixWord, tailWord_6739865, baseEnd_6739865] using wordTrace_append hprefix tailTrace_6739865
  have hstable : (prefixWord ++ tailWord_6739865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739865).length < 2 ^ (prefixWord ++ tailWord_6739865).sum := by decide
  have hdescent : baseEnd_6739865 < baseStart_6739865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739866 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6739866 : Nat := 118140960795 + 6739866 * 2 ^ 59
def prefixEnd_6739866 : Nat := 4983230072969 + 3 ^ 40 * 6739866 * 2
def baseEnd_6739866 : Nat := 3460790804896032476978927

theorem tailTrace_6739866 : CollatzResearch.WordTrace tailWord_6739866 prefixEnd_6739866 3460790804896032476978927 := by
  unfold tailWord_6739866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61455777050156008578987863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163882072133749356210634301 61455777050156008578987863)
  ·
    refine ⟨92183665575234012868481795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61455777050156008578987863 92183665575234012868481795)
    ·
      refine ⟨138275498362851019302722693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92183665575234012868481795 138275498362851019302722693)
      ·
        refine ⟨25926655943034566119260505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138275498362851019302722693 25926655943034566119260505)
        ·
          refine ⟨19444991957275924589445379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25926655943034566119260505 19444991957275924589445379)
          ·
            refine ⟨29167487935913886884168069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444991957275924589445379 29167487935913886884168069)
            ·
              refine ⟨5468903987983853790781513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29167487935913886884168069 5468903987983853790781513)
              ·
                refine ⟨4101677990987890343086135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468903987983853790781513 4101677990987890343086135)
                ·
                  refine ⟨6152516986481835514629203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101677990987890343086135 6152516986481835514629203)
                  ·
                    refine ⟨9228775479722753271943805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152516986481835514629203 9228775479722753271943805)
                    ·
                      refine ⟨3460790804896032476978927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9228775479722753271943805 3460790804896032476978927)
                      ·
                        rfl

theorem cell23_6739866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6739866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739866 prefixEnd_6739866 := by exact prefixLift 6739866
  have htrace : WordTrace (prefixWord ++ tailWord_6739866) baseStart_6739866 baseEnd_6739866 := by
    simpa [prefixWord, tailWord_6739866, baseEnd_6739866] using wordTrace_append hprefix tailTrace_6739866
  have hstable : (prefixWord ++ tailWord_6739866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739866).length < 2 ^ (prefixWord ++ tailWord_6739866).sum := by decide
  have hdescent : baseEnd_6739866 < baseStart_6739866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739872 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2]
def baseStart_6739872 : Nat := 118140960795 + 6739872 * 2 ^ 59
def prefixEnd_6739872 : Nat := 4983230072969 + 3 ^ 40 * 6739872 * 2
def baseEnd_6739872 : Nat := 3460793885779959453503899

theorem tailTrace_6739872 : CollatzResearch.WordTrace tailWord_6739872 prefixEnd_6739872 3460793885779959453503899 := by
  unfold tailWord_6739872
  simp only [CollatzResearch.WordTrace]
  refine ⟨122911663519301148670334935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163882218025734864893779913 122911663519301148670334935)
  ·
    refine ⟨184367495278951723005502403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122911663519301148670334935 184367495278951723005502403)
    ·
      refine ⟨276551242918427584508253605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184367495278951723005502403 276551242918427584508253605)
      ·
        refine ⟨51853358047205172095297551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276551242918427584508253605 51853358047205172095297551)
        ·
          refine ⟨77780037070807758142946327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51853358047205172095297551 77780037070807758142946327)
          ·
            refine ⟨116670055606211637214419491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77780037070807758142946327 116670055606211637214419491)
            ·
              refine ⟨175005083409317455821629237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116670055606211637214419491 175005083409317455821629237)
              ·
                refine ⟨16406726569623511483277741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175005083409317455821629237 16406726569623511483277741)
                ·
                  refine ⟨6152522463608816806229153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16406726569623511483277741 6152522463608816806229153)
                  ·
                    refine ⟨4614391847706612604671865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152522463608816806229153 4614391847706612604671865)
                    ·
                      refine ⟨3460793885779959453503899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614391847706612604671865 3460793885779959453503899)
                      ·
                        rfl

theorem cell23_6739872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_6739872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739872 prefixEnd_6739872 := by exact prefixLift 6739872
  have htrace : WordTrace (prefixWord ++ tailWord_6739872) baseStart_6739872 baseEnd_6739872 := by
    simpa [prefixWord, tailWord_6739872, baseEnd_6739872] using wordTrace_append hprefix tailTrace_6739872
  have hstable : (prefixWord ++ tailWord_6739872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739872).length < 2 ^ (prefixWord ++ tailWord_6739872).sum := by decide
  have hdescent : baseEnd_6739872 < baseStart_6739872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739889 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6739889 : Nat := 118140960795 + 6739889 * 2 ^ 59
def prefixEnd_6739889 : Nat := 4983230072969 + 3 ^ 40 * 6739889 * 2
def baseEnd_6739889 : Nat := 3460802614951085886991321

theorem tailTrace_6739889 : CollatzResearch.WordTrace tailWord_6739889 prefixEnd_6739889 3460802614951085886991321 := by
  unfold tailWord_6739889
  simp only [CollatzResearch.WordTrace]
  refine ⟨245823947079540709244038721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163882631386360472829359147 245823947079540709244038721)
  ·
    refine ⟨184367960309655531933029041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245823947079540709244038721 184367960309655531933029041)
    ·
      refine ⟨138275970232241648949771781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184367960309655531933029041 138275970232241648949771781)
      ·
        refine ⟨25926744418545309178082209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138275970232241648949771781 25926744418545309178082209)
        ·
          refine ⟨19445058313908981883561657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25926744418545309178082209 19445058313908981883561657)
          ·
            refine ⟨14583793735431736412671243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19445058313908981883561657 14583793735431736412671243)
            ·
              refine ⟨21875690603147604619006865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14583793735431736412671243 21875690603147604619006865)
              ·
                refine ⟨16406767952360703464255149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21875690603147604619006865 16406767952360703464255149)
                ·
                  refine ⟨6152537982135263799095681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16406767952360703464255149 6152537982135263799095681)
                  ·
                    refine ⟨4614403486601447849321761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152537982135263799095681 4614403486601447849321761)
                    ·
                      refine ⟨3460802614951085886991321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614403486601447849321761 3460802614951085886991321)
                      ·
                        rfl

theorem cell23_6739889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6739889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739889 prefixEnd_6739889 := by exact prefixLift 6739889
  have htrace : WordTrace (prefixWord ++ tailWord_6739889) baseStart_6739889 baseEnd_6739889 := by
    simpa [prefixWord, tailWord_6739889, baseEnd_6739889] using wordTrace_append hprefix tailTrace_6739889
  have hstable : (prefixWord ++ tailWord_6739889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739889).length < 2 ^ (prefixWord ++ tailWord_6739889).sum := by decide
  have hdescent : baseEnd_6739889 < baseStart_6739889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739948 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6739948 : Nat := 118140960795 + 6739948 * 2 ^ 59
def prefixEnd_6739948 : Nat := 4983230072969 + 3 ^ 40 * 6739948 * 2
def baseEnd_6739948 : Nat := 3460832910309701156153549

theorem tailTrace_6739948 : CollatzResearch.WordTrace tailWord_6739948 prefixEnd_6739948 3460832910309701156153549 := by
  unfold tailWord_6739948
  simp only [CollatzResearch.WordTrace]
  refine ⟨122913049493163481160218249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163884065990884641546957665 122913049493163481160218249)
  ·
    refine ⟨92184787119872610870163687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122913049493163481160218249 92184787119872610870163687)
    ·
      refine ⟨138277180679808916305245531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92184787119872610870163687 138277180679808916305245531)
      ·
        refine ⟨207415771019713374457868297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138277180679808916305245531 207415771019713374457868297)
        ·
          refine ⟨155561828264785030843401223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207415771019713374457868297 155561828264785030843401223)
          ·
            refine ⟨233342742397177546265101835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155561828264785030843401223 233342742397177546265101835)
            ·
              refine ⟨350014113595766319397652753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233342742397177546265101835 350014113595766319397652753)
              ·
                refine ⟨262510585196824739548239565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350014113595766319397652753 262510585196824739548239565)
                ·
                  refine ⟨98441469448809277330589837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262510585196824739548239565 98441469448809277330589837)
                  ·
                    refine ⟨36915551043303478998971189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98441469448809277330589837 36915551043303478998971189)
                    ·
                      refine ⟨3460832910309701156153549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36915551043303478998971189 3460832910309701156153549)
                      ·
                        rfl

theorem cell23_6739948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6739948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739948 prefixEnd_6739948 := by exact prefixLift 6739948
  have htrace : WordTrace (prefixWord ++ tailWord_6739948) baseStart_6739948 baseEnd_6739948 := by
    simpa [prefixWord, tailWord_6739948, baseEnd_6739948] using wordTrace_append hprefix tailTrace_6739948
  have hstable : (prefixWord ++ tailWord_6739948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739948).length < 2 ^ (prefixWord ++ tailWord_6739948).sum := by decide
  have hdescent : baseEnd_6739948 < baseStart_6739948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739966 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6739966 : Nat := 118140960795 + 6739966 * 2 ^ 59
def prefixEnd_6739966 : Nat := 4983230072969 + 3 ^ 40 * 6739966 * 2
def baseEnd_6739966 : Nat := 3460842152961482085728467

theorem tailTrace_6739966 : CollatzResearch.WordTrace tailWord_6739966 prefixEnd_6739966 3460842152961482085728467 := by
  unfold tailWord_6739966
  simp only [CollatzResearch.WordTrace]
  refine ⟨30728344437532718924323969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163884503666841167596394501 30728344437532718924323969)
  ·
    refine ⟨23046258328149539193242977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30728344437532718924323969 23046258328149539193242977)
    ·
      refine ⟨17284693746112154394932233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23046258328149539193242977 17284693746112154394932233)
      ·
        refine ⟨12963520309584115796199175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17284693746112154394932233 12963520309584115796199175)
        ·
          refine ⟨19445280464376173694298763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963520309584115796199175 19445280464376173694298763)
          ·
            refine ⟨29167920696564260541448145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445280464376173694298763 29167920696564260541448145)
            ·
              refine ⟨21875940522423195406086109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29167920696564260541448145 21875940522423195406086109)
              ·
                refine ⟨8203477695908698277282291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21875940522423195406086109 8203477695908698277282291)
                ·
                  refine ⟨12305216543863047415923437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203477695908698277282291 12305216543863047415923437)
                  ·
                    refine ⟨4614456203948642780971289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12305216543863047415923437 4614456203948642780971289)
                    ·
                      refine ⟨3460842152961482085728467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614456203948642780971289 3460842152961482085728467)
                      ·
                        rfl

theorem cell23_6739966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6739966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739966 prefixEnd_6739966 := by exact prefixLift 6739966
  have htrace : WordTrace (prefixWord ++ tailWord_6739966) baseStart_6739966 baseEnd_6739966 := by
    simpa [prefixWord, tailWord_6739966, baseEnd_6739966] using wordTrace_append hprefix tailTrace_6739966
  have hstable : (prefixWord ++ tailWord_6739966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739966).length < 2 ^ (prefixWord ++ tailWord_6739966).sum := by decide
  have hdescent : baseEnd_6739966 < baseStart_6739966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739974 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6739974 : Nat := 118140960795 + 6739974 * 2 ^ 59
def prefixEnd_6739974 : Nat := 4983230072969 + 3 ^ 40 * 6739974 * 2
def baseEnd_6739974 : Nat := 3460846260806718054428431

theorem tailTrace_6739974 : CollatzResearch.WordTrace tailWord_6739974 prefixEnd_6739974 3460846260806718054428431 := by
  unfold tailWord_6739974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682095227632274023777593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163884698189488512507255317 7682095227632274023777593)
  ·
    refine ⟨5761571420724205517833195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7682095227632274023777593 5761571420724205517833195)
    ·
      refine ⟨8642357131086308276749793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761571420724205517833195 8642357131086308276749793)
      ·
        refine ⟨6481767848314731207562345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8642357131086308276749793 6481767848314731207562345)
        ·
          refine ⟨4861325886236048405671759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6481767848314731207562345 4861325886236048405671759)
          ·
            refine ⟨7291988829354072608507639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861325886236048405671759 7291988829354072608507639)
            ·
              refine ⟨10937983244031108912761459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291988829354072608507639 10937983244031108912761459)
              ·
                refine ⟨16406974866046663369142189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937983244031108912761459 16406974866046663369142189)
                ·
                  refine ⟨6152615574767498763428321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16406974866046663369142189 6152615574767498763428321)
                  ·
                    refine ⟨4614461681075624072571241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152615574767498763428321 4614461681075624072571241)
                    ·
                      refine ⟨3460846260806718054428431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614461681075624072571241 3460846260806718054428431)
                      ·
                        rfl

theorem cell23_6739974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6739974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739974 prefixEnd_6739974 := by exact prefixLift 6739974
  have htrace : WordTrace (prefixWord ++ tailWord_6739974) baseStart_6739974 baseEnd_6739974 := by
    simpa [prefixWord, tailWord_6739974, baseEnd_6739974] using wordTrace_append hprefix tailTrace_6739974
  have hstable : (prefixWord ++ tailWord_6739974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739974).length < 2 ^ (prefixWord ++ tailWord_6739974).sum := by decide
  have hdescent : baseEnd_6739974 < baseStart_6739974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739979 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 2, 2, 2]
def baseStart_6739979 : Nat := 118140960795 + 6739979 * 2 ^ 59
def prefixEnd_6739979 : Nat := 4983230072969 + 3 ^ 40 * 6739979 * 2
def baseEnd_6739979 : Nat := 3460848828209990534865907

theorem tailTrace_6739979 : CollatzResearch.WordTrace tailWord_6739979 prefixEnd_6739979 3460848828209990534865907 := by
  unfold tailWord_6739979
  simp only [CollatzResearch.WordTrace]
  refine ⟨245827229649214654614814991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163884819766143103076543327 245827229649214654614814991)
  ·
    refine ⟨368740844473821981922222487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245827229649214654614814991 368740844473821981922222487)
    ·
      refine ⟨553111266710732972883333731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368740844473821981922222487 553111266710732972883333731)
      ·
        refine ⟨829666900066099459325000597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553111266710732972883333731 829666900066099459325000597)
        ·
          refine ⟨38890635940598412155859403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 829666900066099459325000597 38890635940598412155859403)
          ·
            refine ⟨58335953910897618233789105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38890635940598412155859403 58335953910897618233789105)
            ·
              refine ⟨43751965433173213675341829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58335953910897618233789105 43751965433173213675341829)
              ·
                refine ⟨8203493518719977564126593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43751965433173213675341829 8203493518719977564126593)
                ·
                  refine ⟨6152620139039983173094945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8203493518719977564126593 6152620139039983173094945)
                  ·
                    refine ⟨4614465104279987379821209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152620139039983173094945 4614465104279987379821209)
                    ·
                      refine ⟨3460848828209990534865907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614465104279987379821209 3460848828209990534865907)
                      ·
                        rfl

theorem cell23_6739979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 2, 2].length) (baseStart_6739979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739979 prefixEnd_6739979 := by exact prefixLift 6739979
  have htrace : WordTrace (prefixWord ++ tailWord_6739979) baseStart_6739979 baseEnd_6739979 := by
    simpa [prefixWord, tailWord_6739979, baseEnd_6739979] using wordTrace_append hprefix tailTrace_6739979
  have hstable : (prefixWord ++ tailWord_6739979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739979).length < 2 ^ (prefixWord ++ tailWord_6739979).sum := by decide
  have hdescent : baseEnd_6739979 < baseStart_6739979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6739996 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6739996 : Nat := 118140960795 + 6739996 * 2 ^ 59
def prefixEnd_6739996 : Nat := 4983230072969 + 3 ^ 40 * 6739996 * 2
def baseEnd_6739996 : Nat := 3460857557381116968353329

theorem tailTrace_6739996 : CollatzResearch.WordTrace tailWord_6739996 prefixEnd_6739996 3460857557381116968353329 := by
  unfold tailWord_6739996
  simp only [CollatzResearch.WordTrace]
  refine ⟨122913924845076533259091921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163885233126768711012122561 122913924845076533259091921)
  ·
    refine ⟨92185443633807399944318941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122913924845076533259091921 92185443633807399944318941)
    ·
      refine ⟨34569541362677774979119603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92185443633807399944318941 34569541362677774979119603)
      ·
        refine ⟨51854312044016662468679405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34569541362677774979119603 51854312044016662468679405)
        ·
          refine ⟨19445367016506248425754777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51854312044016662468679405 19445367016506248425754777)
          ·
            refine ⟨14584025262379686319316083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19445367016506248425754777 14584025262379686319316083)
            ·
              refine ⟨21876037893569529478974125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14584025262379686319316083 21876037893569529478974125)
              ·
                refine ⟨8203514210088573554615297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21876037893569529478974125 8203514210088573554615297)
                ·
                  refine ⟨6152635657566430165961473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8203514210088573554615297 6152635657566430165961473)
                  ·
                    refine ⟨4614476743174822624471105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152635657566430165961473 4614476743174822624471105)
                    ·
                      refine ⟨3460857557381116968353329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614476743174822624471105 3460857557381116968353329)
                      ·
                        rfl

theorem cell23_6739996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6739996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6739996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6739996 prefixEnd_6739996 := by exact prefixLift 6739996
  have htrace : WordTrace (prefixWord ++ tailWord_6739996) baseStart_6739996 baseEnd_6739996 := by
    simpa [prefixWord, tailWord_6739996, baseEnd_6739996] using wordTrace_append hprefix tailTrace_6739996
  have hstable : (prefixWord ++ tailWord_6739996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6739996).length < 2 ^ (prefixWord ++ tailWord_6739996).sum := by decide
  have hdescent : baseEnd_6739996 < baseStart_6739996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6739996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740035 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4]
def baseStart_6740035 : Nat := 118140960795 + 6740035 * 2 ^ 59
def prefixEnd_6740035 : Nat := 4983230072969 + 3 ^ 40 * 6740035 * 2
def baseEnd_6740035 : Nat := 3460877583126642315765649

theorem tailTrace_6740035 : CollatzResearch.WordTrace tailWord_6740035 prefixEnd_6740035 3460877583126642315765649 := by
  unfold tailWord_6740035
  simp only [CollatzResearch.WordTrace]
  refine ⟨245829272137011776178853559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163886181424674517452569039 245829272137011776178853559)
  ·
    refine ⟨368743908205517664268280339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245829272137011776178853559 368743908205517664268280339)
    ·
      refine ⟨553115862308276496402420509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368743908205517664268280339 553115862308276496402420509)
      ·
        refine ⟨207418448365603686150907691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553115862308276496402420509 207418448365603686150907691)
        ·
          refine ⟨311127672548405529226361537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207418448365603686150907691 311127672548405529226361537)
          ·
            refine ⟨233345754411304146919771153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311127672548405529226361537 233345754411304146919771153)
            ·
              refine ⟨175009315808478110189828365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233345754411304146919771153 175009315808478110189828365)
              ·
                refine ⟨65628493428179291321185637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175009315808478110189828365 65628493428179291321185637)
                ·
                  refine ⟨12305342517783617122722307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65628493428179291321185637 12305342517783617122722307)
                  ·
                    refine ⟨18458013776675425684083461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12305342517783617122722307 18458013776675425684083461)
                    ·
                      refine ⟨3460877583126642315765649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18458013776675425684083461 3460877583126642315765649)
                      ·
                        rfl

theorem cell23_6740035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_6740035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740035 prefixEnd_6740035 := by exact prefixLift 6740035
  have htrace : WordTrace (prefixWord ++ tailWord_6740035) baseStart_6740035 baseEnd_6740035 := by
    simpa [prefixWord, tailWord_6740035, baseEnd_6740035] using wordTrace_append hprefix tailTrace_6740035
  have hstable : (prefixWord ++ tailWord_6740035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740035).length < 2 ^ (prefixWord ++ tailWord_6740035).sum := by decide
  have hdescent : baseEnd_6740035 < baseStart_6740035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740066 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6740066 : Nat := 118140960795 + 6740066 * 2 ^ 59
def prefixEnd_6740066 : Nat := 4983230072969 + 3 ^ 40 * 6740066 * 2
def baseEnd_6740066 : Nat := 1153631167008977231492669

theorem tailTrace_6740066 : CollatzResearch.WordTrace tailWord_6740066 prefixEnd_6740066 1153631167008977231492669 := by
  unfold tailWord_6740066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61457600699974867118308013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163886935199932978982154701 61457600699974867118308013)
  ·
    refine ⟨23046600262490575169365505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61457600699974867118308013 23046600262490575169365505)
    ·
      refine ⟨17284950196867931377024129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23046600262490575169365505 17284950196867931377024129)
      ·
        refine ⟨12963712647650948532768097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17284950196867931377024129 12963712647650948532768097)
        ·
          refine ⟨9722784485738211399576073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12963712647650948532768097 9722784485738211399576073)
          ·
            refine ⟨7292088364303658549682055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9722784485738211399576073 7292088364303658549682055)
            ·
              refine ⟨10938132546455487824523083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292088364303658549682055 10938132546455487824523083)
              ·
                refine ⟨16407198819683231736784625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10938132546455487824523083 16407198819683231736784625)
                ·
                  refine ⟨12305399114762423802588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16407198819683231736784625 12305399114762423802588469)
                  ·
                    refine ⟨1153631167008977231492669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12305399114762423802588469 1153631167008977231492669)
                    ·
                      rfl

theorem cell23_6740066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6740066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740066 prefixEnd_6740066 := by exact prefixLift 6740066
  have htrace : WordTrace (prefixWord ++ tailWord_6740066) baseStart_6740066 baseEnd_6740066 := by
    simpa [prefixWord, tailWord_6740066, baseEnd_6740066] using wordTrace_append hprefix tailTrace_6740066
  have hstable : (prefixWord ++ tailWord_6740066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740066).length < 2 ^ (prefixWord ++ tailWord_6740066).sum := by decide
  have hdescent : baseEnd_6740066 < baseStart_6740066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740069 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_6740069 : Nat := 118140960795 + 6740069 * 2 ^ 59
def prefixEnd_6740069 : Nat := 4983230072969 + 3 ^ 40 * 6740069 * 2
def baseEnd_6740069 : Nat := 3460895041468895182740493

theorem tailTrace_6740069 : CollatzResearch.WordTrace tailWord_6740069 prefixEnd_6740069 3460895041468895182740493 := by
  unfold tailWord_6740069
  simp only [CollatzResearch.WordTrace]
  refine ⟨245830512218888599985591261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163887008145925733323727507 245830512218888599985591261)
  ·
    refine ⟨92186442082083224994596723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245830512218888599985591261 92186442082083224994596723)
    ·
      refine ⟨138279663123124837491895085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92186442082083224994596723 138279663123124837491895085)
      ·
        refine ⟨51854873671171814059460657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138279663123124837491895085 51854873671171814059460657)
        ·
          refine ⟨38891155253378860544595493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51854873671171814059460657 38891155253378860544595493)
          ·
            refine ⟨7292091610008536352111655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38891155253378860544595493 7292091610008536352111655)
            ·
              refine ⟨10938137415012804528167483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292091610008536352111655 10938137415012804528167483)
              ·
                refine ⟨16407206122519206792251225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10938137415012804528167483 16407206122519206792251225)
                ·
                  refine ⟨12305404591889405094188419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16407206122519206792251225 12305404591889405094188419)
                  ·
                    refine ⟨18458106887834107641282629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12305404591889405094188419 18458106887834107641282629)
                    ·
                      refine ⟨3460895041468895182740493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18458106887834107641282629 3460895041468895182740493)
                      ·
                        rfl

theorem cell23_6740069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_6740069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740069 prefixEnd_6740069 := by exact prefixLift 6740069
  have htrace : WordTrace (prefixWord ++ tailWord_6740069) baseStart_6740069 baseEnd_6740069 := by
    simpa [prefixWord, tailWord_6740069, baseEnd_6740069] using wordTrace_append hprefix tailTrace_6740069
  have hstable : (prefixWord ++ tailWord_6740069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740069).length < 2 ^ (prefixWord ++ tailWord_6740069).sum := by decide
  have hdescent : baseEnd_6740069 < baseStart_6740069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740079 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 1, 4]
def baseStart_6740079 : Nat := 118140960795 + 6740079 * 2 ^ 59
def prefixEnd_6740079 : Nat := 4983230072969 + 3 ^ 40 * 6740079 * 2
def baseEnd_6740079 : Nat := 1153633392091813381205149

theorem tailTrace_6740079 : CollatzResearch.WordTrace tailWord_6740079 prefixEnd_6740079 1153633392091813381205149 := by
  unfold tailWord_6740079
  simp only [CollatzResearch.WordTrace]
  refine ⟨245830876948852371693455291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163887251299234914462303527 245830876948852371693455291)
  ·
    refine ⟨368746315423278557540182937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245830876948852371693455291 368746315423278557540182937)
    ·
      refine ⟨276559736567458918155137203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368746315423278557540182937 276559736567458918155137203)
      ·
        refine ⟨414839604851188377232705805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276559736567458918155137203 414839604851188377232705805)
        ·
          refine ⟨155564851819195641462264677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414839604851188377232705805 155564851819195641462264677)
          ·
            refine ⟨29168409716099182774174627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155564851819195641462264677 29168409716099182774174627)
            ·
              refine ⟨43752614574148774161261941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29168409716099182774174627 43752614574148774161261941)
              ·
                refine ⟨4101807616326447577618307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43752614574148774161261941 4101807616326447577618307)
                ·
                  refine ⟨6152711424489671366427461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101807616326447577618307 6152711424489671366427461)
                  ·
                    refine ⟨1153633392091813381205149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152711424489671366427461 1153633392091813381205149)
                    ·
                      rfl

theorem cell23_6740079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_6740079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740079 prefixEnd_6740079 := by exact prefixLift 6740079
  have htrace : WordTrace (prefixWord ++ tailWord_6740079) baseStart_6740079 baseEnd_6740079 := by
    simpa [prefixWord, tailWord_6740079, baseEnd_6740079] using wordTrace_append hprefix tailTrace_6740079
  have hstable : (prefixWord ++ tailWord_6740079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740079).length < 2 ^ (prefixWord ++ tailWord_6740079).sum := by decide
  have hdescent : baseEnd_6740079 < baseStart_6740079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740092 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 6]
def baseStart_6740092 : Nat := 118140960795 + 6740092 * 2 ^ 59
def prefixEnd_6740092 : Nat := 4983230072969 + 3 ^ 40 * 6740092 * 2
def baseEnd_6740092 : Nat := 384545205724883176972543

theorem tailTrace_6740092 : CollatzResearch.WordTrace tailWord_6740092 prefixEnd_6740092 384545205724883176972543 := by
  unfold tailWord_6740092
  simp only [CollatzResearch.WordTrace]
  refine ⟨122915675548902637456839265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163887567398536849942452353 122915675548902637456839265)
  ·
    refine ⟨92186756661676978092629449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122915675548902637456839265 92186756661676978092629449)
    ·
      refine ⟨69140067496257733569472087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92186756661676978092629449 69140067496257733569472087)
      ·
        refine ⟨103710101244386600354208131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69140067496257733569472087 103710101244386600354208131)
        ·
          refine ⟨155565151866579900531312197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103710101244386600354208131 155565151866579900531312197)
          ·
            refine ⟨29168465974983731349621037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155565151866579900531312197 29168465974983731349621037)
            ·
              refine ⟨10938174740618899256107889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29168465974983731349621037 10938174740618899256107889)
              ·
                refine ⟨8203631055464174442080917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10938174740618899256107889 8203631055464174442080917)
                ·
                  refine ⟨384545205724883176972543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8203631055464174442080917 384545205724883176972543)
                  ·
                    rfl

theorem cell23_6740092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_6740092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740092 prefixEnd_6740092 := by exact prefixLift 6740092
  have htrace : WordTrace (prefixWord ++ tailWord_6740092) baseStart_6740092 baseEnd_6740092 := by
    simpa [prefixWord, tailWord_6740092, baseEnd_6740092] using wordTrace_append hprefix tailTrace_6740092
  have hstable : (prefixWord ++ tailWord_6740092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740092).length < 2 ^ (prefixWord ++ tailWord_6740092).sum := by decide
  have hdescent : baseEnd_6740092 < baseStart_6740092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740112 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2]
def baseStart_6740112 : Nat := 118140960795 + 6740112 * 2 ^ 59
def prefixEnd_6740112 : Nat := 4983230072969 + 3 ^ 40 * 6740112 * 2
def baseEnd_6740112 : Nat := 3460917121137038514502795

theorem tailTrace_6740112 : CollatzResearch.WordTrace tailWord_6740112 prefixEnd_6740112 3460917121137038514502795 := by
  unfold tailWord_6740112
  simp only [CollatzResearch.WordTrace]
  refine ⟨122916040278866409164703295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163888053705155212219604393 122916040278866409164703295)
  ·
    refine ⟨184374060418299613747054943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122916040278866409164703295 184374060418299613747054943)
    ·
      refine ⟨276561090627449420620582415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184374060418299613747054943 276561090627449420620582415)
      ·
        refine ⟨414841635941174130930873623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276561090627449420620582415 414841635941174130930873623)
        ·
          refine ⟨622262453911761196396310435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414841635941174130930873623 622262453911761196396310435)
          ·
            refine ⟨933393680867641794594465653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622262453911761196396310435 933393680867641794594465653)
            ·
              refine ⟨87505657581341418243231155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 933393680867641794594465653 87505657581341418243231155)
              ·
                refine ⟨131258486372012127364846733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87505657581341418243231155 131258486372012127364846733)
                ·
                  refine ⟨49221932389504547761817525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131258486372012127364846733 49221932389504547761817525)
                  ·
                    refine ⟨4614556161516051352670393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49221932389504547761817525 4614556161516051352670393)
                    ·
                      refine ⟨3460917121137038514502795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614556161516051352670393 3460917121137038514502795)
                      ·
                        rfl

theorem cell23_6740112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 5, 2].length) (baseStart_6740112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740112 prefixEnd_6740112 := by exact prefixLift 6740112
  have htrace : WordTrace (prefixWord ++ tailWord_6740112) baseStart_6740112 baseEnd_6740112 := by
    simpa [prefixWord, tailWord_6740112, baseEnd_6740112] using wordTrace_append hprefix tailTrace_6740112
  have hstable : (prefixWord ++ tailWord_6740112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740112).length < 2 ^ (prefixWord ++ tailWord_6740112).sum := by decide
  have hdescent : baseEnd_6740112 < baseStart_6740112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740129 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6740129 : Nat := 118140960795 + 6740129 * 2 ^ 59
def prefixEnd_6740129 : Nat := 4983230072969 + 3 ^ 40 * 6740129 * 2
def baseEnd_6740129 : Nat := 3460925850308164947990217

theorem tailTrace_6740129 : CollatzResearch.WordTrace tailWord_6740129 prefixEnd_6740129 3460925850308164947990217 := by
  unfold tailWord_6740129
  simp only [CollatzResearch.WordTrace]
  refine ⟨245832700598671230232775441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163888467065780820155183627 245832700598671230232775441)
  ·
    refine ⟨184374525449003422674581581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245832700598671230232775441 184374525449003422674581581)
    ·
      refine ⟨69140447043376283502968093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184374525449003422674581581 69140447043376283502968093)
      ·
        refine ⟨25927667641266106313613035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69140447043376283502968093 25927667641266106313613035)
        ·
          refine ⟨38891501461899159470419553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25927667641266106313613035 38891501461899159470419553)
          ·
            refine ⟨29168626096424369602814665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38891501461899159470419553 29168626096424369602814665)
            ·
              refine ⟨21876469572318277202110999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29168626096424369602814665 21876469572318277202110999)
              ·
                refine ⟨32814704358477415803166499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21876469572318277202110999 32814704358477415803166499)
                ·
                  refine ⟨49222056537716123704749749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32814704358477415803166499 49222056537716123704749749)
                  ·
                    refine ⟨4614567800410886597320289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49222056537716123704749749 4614567800410886597320289)
                    ·
                      refine ⟨3460925850308164947990217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614567800410886597320289 3460925850308164947990217)
                      ·
                        rfl

theorem cell23_6740129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6740129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740129 prefixEnd_6740129 := by exact prefixLift 6740129
  have htrace : WordTrace (prefixWord ++ tailWord_6740129) baseStart_6740129 baseEnd_6740129 := by
    simpa [prefixWord, tailWord_6740129, baseEnd_6740129] using wordTrace_append hprefix tailTrace_6740129
  have hstable : (prefixWord ++ tailWord_6740129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740129).length < 2 ^ (prefixWord ++ tailWord_6740129).sum := by decide
  have hdescent : baseEnd_6740129 < baseStart_6740129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740152 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_6740152 : Nat := 118140960795 + 6740152 * 2 ^ 59
def prefixEnd_6740152 : Nat := 4983230072969 + 3 ^ 40 * 6740152 * 2
def baseEnd_6740152 : Nat := 1153645886787739452667537

theorem tailTrace_6740152 : CollatzResearch.WordTrace tailWord_6740152 prefixEnd_6740152 1153645886787739452667537 := by
  unfold tailWord_6740152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122916769738793952580431355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163889026318391936773908473 122916769738793952580431355)
  ·
    refine ⟨184375154608190928870647033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122916769738793952580431355 184375154608190928870647033)
    ·
      refine ⟨138281365956143196652985275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184375154608190928870647033 138281365956143196652985275)
      ·
        refine ⟨207422048934214794979477913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138281365956143196652985275 207422048934214794979477913)
        ·
          refine ⟨155566536700661096234608435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207422048934214794979477913 155566536700661096234608435)
          ·
            refine ⟨233349805050991644351912653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155566536700661096234608435 233349805050991644351912653)
            ·
              refine ⟨87506176894121866631967245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233349805050991644351912653 87506176894121866631967245)
              ·
                refine ⟨32814816335295699986987717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87506176894121866631967245 32814816335295699986987717)
                ·
                  refine ⟨6152778062867943747560197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32814816335295699986987717 6152778062867943747560197)
                  ·
                    refine ⟨1153645886787739452667537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152778062867943747560197 1153645886787739452667537)
                    ·
                      rfl

theorem cell23_6740152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_6740152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740152 prefixEnd_6740152 := by exact prefixLift 6740152
  have htrace : WordTrace (prefixWord ++ tailWord_6740152) baseStart_6740152 baseEnd_6740152 := by
    simpa [prefixWord, tailWord_6740152, baseEnd_6740152] using wordTrace_append hprefix tailTrace_6740152
  have hstable : (prefixWord ++ tailWord_6740152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740152).length < 2 ^ (prefixWord ++ tailWord_6740152).sum := by decide
  have hdescent : baseEnd_6740152 < baseStart_6740152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740153 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6740153 : Nat := 118140960795 + 6740153 * 2 ^ 59
def prefixEnd_6740153 : Nat := 4983230072969 + 3 ^ 40 * 6740153 * 2
def baseEnd_6740153 : Nat := 3460938173843872854090107

theorem tailTrace_6740153 : CollatzResearch.WordTrace tailWord_6740153 prefixEnd_6740153 3460938173843872854090107 := by
  unfold tailWord_6740153
  simp only [CollatzResearch.WordTrace]
  refine ⟨245833575950584282331649113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163889050633722854887766075 245833575950584282331649113)
  ·
    refine ⟨184375181962938211748736835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245833575950584282331649113 184375181962938211748736835)
    ·
      refine ⟨276562772944407317623105253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184375181962938211748736835 276562772944407317623105253)
      ·
        refine ⟨51855519927076372054332235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276562772944407317623105253 51855519927076372054332235)
        ·
          refine ⟨77783279890614558081498353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51855519927076372054332235 77783279890614558081498353)
          ·
            refine ⟨58337459917960918561123765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77783279890614558081498353 58337459917960918561123765)
            ·
              refine ⟨5469136867308836115105353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58337459917960918561123765 5469136867308836115105353)
              ·
                refine ⟨4101852650481627086329015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5469136867308836115105353 4101852650481627086329015)
                ·
                  refine ⟨6152778975722440629493523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101852650481627086329015 6152778975722440629493523)
                  ·
                    refine ⟨9229168463583660944240285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152778975722440629493523 9229168463583660944240285)
                    ·
                      refine ⟨3460938173843872854090107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9229168463583660944240285 3460938173843872854090107)
                      ·
                        rfl

theorem cell23_6740153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6740153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740153 prefixEnd_6740153 := by exact prefixLift 6740153
  have htrace : WordTrace (prefixWord ++ tailWord_6740153) baseStart_6740153 baseEnd_6740153 := by
    simpa [prefixWord, tailWord_6740153, baseEnd_6740153] using wordTrace_append hprefix tailTrace_6740153
  have hstable : (prefixWord ++ tailWord_6740153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740153).length < 2 ^ (prefixWord ++ tailWord_6740153).sum := by decide
  have hdescent : baseEnd_6740153 < baseStart_6740153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740155 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_6740155 : Nat := 118140960795 + 6740155 * 2 ^ 59
def prefixEnd_6740155 : Nat := 4983230072969 + 3 ^ 40 * 6740155 * 2
def baseEnd_6740155 : Nat := 3460939200805181846265097

theorem tailTrace_6740155 : CollatzResearch.WordTrace tailWord_6740155 prefixEnd_6740155 3460939200805181846265097 := by
  unfold tailWord_6740155
  simp only [CollatzResearch.WordTrace]
  refine ⟨245833648896577036673221919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163889099264384691115481279 245833648896577036673221919)
  ·
    refine ⟨368750473344865555009832879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245833648896577036673221919 368750473344865555009832879)
    ·
      refine ⟨553125710017298332514749319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368750473344865555009832879 553125710017298332514749319)
      ·
        refine ⟨829688565025947498772123979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553125710017298332514749319 829688565025947498772123979)
        ·
          refine ⟨1244532847538921248158185969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829688565025947498772123979 1244532847538921248158185969)
          ·
            refine ⟨933399635654190936118639477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244532847538921248158185969 933399635654190936118639477)
            ·
              refine ⟨87506215842580400261122451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 933399635654190936118639477 87506215842580400261122451)
              ·
                refine ⟨131259323763870600391683677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87506215842580400261122451 131259323763870600391683677)
                ·
                  refine ⟨49222246411451475146881379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131259323763870600391683677 49222246411451475146881379)
                  ·
                    refine ⟨73833369617177212720322069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49222246411451475146881379 73833369617177212720322069)
                    ·
                      refine ⟨3460939200805181846265097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73833369617177212720322069 3460939200805181846265097)
                      ·
                        rfl

theorem cell23_6740155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_6740155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740155 prefixEnd_6740155 := by exact prefixLift 6740155
  have htrace : WordTrace (prefixWord ++ tailWord_6740155) baseStart_6740155 baseEnd_6740155 := by
    simpa [prefixWord, tailWord_6740155, baseEnd_6740155] using wordTrace_append hprefix tailTrace_6740155
  have hstable : (prefixWord ++ tailWord_6740155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740155).length < 2 ^ (prefixWord ++ tailWord_6740155).sum := by decide
  have hdescent : baseEnd_6740155 < baseStart_6740155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740165 : List Nat := [1, 3, 1, 1, 1, 1, 5, 10]
def baseStart_6740165 : Nat := 118140960795 + 6740165 * 2 ^ 59
def prefixEnd_6740165 : Nat := 4983230072969 + 3 ^ 40 * 6740165 * 2
def baseEnd_6740165 : Nat := 128183123541175066931113

theorem tailTrace_6740165 : CollatzResearch.WordTrace tailWord_6740165 prefixEnd_6740165 128183123541175066931113 := by
  unfold tailWord_6740165
  simp only [CollatzResearch.WordTrace]
  refine ⟨245834013626540808381085949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163889342417693872254057299 245834013626540808381085949)
  ·
    refine ⟨92187755109952803142907231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245834013626540808381085949 92187755109952803142907231)
    ·
      refine ⟨138281632664929204714360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92187755109952803142907231 138281632664929204714360847)
      ·
        refine ⟨207422448997393807071541271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138281632664929204714360847 207422448997393807071541271)
        ·
          refine ⟨311133673496090710607311907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207422448997393807071541271 311133673496090710607311907)
          ·
            refine ⟨466700510244136065910967861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311133673496090710607311907 466700510244136065910967861)
            ·
              refine ⟨43753172835387756179153237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 466700510244136065910967861 43753172835387756179153237)
              ·
                refine ⟨128183123541175066931113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43753172835387756179153237 128183123541175066931113)
                ·
                  rfl

theorem cell23_6740165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 10].length) (baseStart_6740165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740165 prefixEnd_6740165 := by exact prefixLift 6740165
  have htrace : WordTrace (prefixWord ++ tailWord_6740165) baseStart_6740165 baseEnd_6740165 := by
    simpa [prefixWord, tailWord_6740165, baseEnd_6740165] using wordTrace_append hprefix tailTrace_6740165
  have hstable : (prefixWord ++ tailWord_6740165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740165).length < 2 ^ (prefixWord ++ tailWord_6740165).sum := by decide
  have hdescent : baseEnd_6740165 < baseStart_6740165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740189 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6740189 : Nat := 118140960795 + 6740189 * 2 ^ 59
def prefixEnd_6740189 : Nat := 4983230072969 + 3 ^ 40 * 6740189 * 2
def baseEnd_6740189 : Nat := 3460956659147434713239941

theorem tailTrace_6740189 : CollatzResearch.WordTrace tailWord_6740189 prefixEnd_6740189 3460956659147434713239941 := by
  unfold tailWord_6740189
  simp only [CollatzResearch.WordTrace]
  refine ⟨245834888978453860479959621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163889925985635906986639747 245834888978453860479959621)
  ·
    refine ⟨46094041683460098839992429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245834888978453860479959621 46094041683460098839992429)
    ·
      refine ⟨17285265631297537064997161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46094041683460098839992429 17285265631297537064997161)
      ·
        refine ⟨12963949223473152798747871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17285265631297537064997161 12963949223473152798747871)
        ·
          refine ⟨19445923835209729198121807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963949223473152798747871 19445923835209729198121807)
          ·
            refine ⟨29168885752814593797182711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445923835209729198121807 29168885752814593797182711)
            ·
              refine ⟨43753328629221890695774067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29168885752814593797182711 43753328629221890695774067)
              ·
                refine ⟨65629992943832836043661101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43753328629221890695774067 65629992943832836043661101)
                ·
                  refine ⟨24611247353937313516372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65629992943832836043661101 24611247353937313516372913)
                  ·
                    refine ⟨18458435515452985137279685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24611247353937313516372913 18458435515452985137279685)
                    ·
                      refine ⟨3460956659147434713239941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18458435515452985137279685 3460956659147434713239941)
                      ·
                        rfl

theorem cell23_6740189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6740189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740189 prefixEnd_6740189 := by exact prefixLift 6740189
  have htrace : WordTrace (prefixWord ++ tailWord_6740189) baseStart_6740189 baseEnd_6740189 := by
    simpa [prefixWord, tailWord_6740189, baseEnd_6740189] using wordTrace_append hprefix tailTrace_6740189
  have hstable : (prefixWord ++ tailWord_6740189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740189).length < 2 ^ (prefixWord ++ tailWord_6740189).sum := by decide
  have hdescent : baseEnd_6740189 < baseStart_6740189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740193 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_6740193 : Nat := 118140960795 + 6740193 * 2 ^ 59
def prefixEnd_6740193 : Nat := 4983230072969 + 3 ^ 40 * 6740193 * 2
def baseEnd_6740193 : Nat := 3460958713070052697589923

theorem tailTrace_6740193 : CollatzResearch.WordTrace tailWord_6740193 prefixEnd_6740193 3460958713070052697589923 := by
  unfold tailWord_6740193
  simp only [CollatzResearch.WordTrace]
  refine ⟨245835034870439369163105233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163890023246959579442070155 245835034870439369163105233)
  ·
    refine ⟨184376276152829526872328925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245835034870439369163105233 184376276152829526872328925)
    ·
      refine ⟨69141103557311072577123347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184376276152829526872328925 69141103557311072577123347)
      ·
        refine ⟨103711655335966608865685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69141103557311072577123347 103711655335966608865685021)
        ·
          refine ⟨38891870750987478324631883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103711655335966608865685021 38891870750987478324631883)
          ·
            refine ⟨58337806126481217486947825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38891870750987478324631883 58337806126481217486947825)
            ·
              refine ⟨43753354594860913115210869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58337806126481217486947825 43753354594860913115210869)
              ·
                refine ⟨4101876993268210604551019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43753354594860913115210869 4101876993268210604551019)
                ·
                  refine ⟨6152815489902315906826529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101876993268210604551019 6152815489902315906826529)
                  ·
                    refine ⟨4614611617426736930119897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152815489902315906826529 4614611617426736930119897)
                    ·
                      refine ⟨3460958713070052697589923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614611617426736930119897 3460958713070052697589923)
                      ·
                        rfl

theorem cell23_6740193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_6740193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740193 prefixEnd_6740193 := by exact prefixLift 6740193
  have htrace : WordTrace (prefixWord ++ tailWord_6740193) baseStart_6740193 baseEnd_6740193 := by
    simpa [prefixWord, tailWord_6740193, baseEnd_6740193] using wordTrace_append hprefix tailTrace_6740193
  have hstable : (prefixWord ++ tailWord_6740193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740193).length < 2 ^ (prefixWord ++ tailWord_6740193).sum := by decide
  have hdescent : baseEnd_6740193 < baseStart_6740193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740209 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_6740209 : Nat := 118140960795 + 6740209 * 2 ^ 59
def prefixEnd_6740209 : Nat := 4983230072969 + 3 ^ 40 * 6740209 * 2
def baseEnd_6740209 : Nat := 3460966928760524634989849

theorem tailTrace_6740209 : CollatzResearch.WordTrace tailWord_6740209 prefixEnd_6740209 3460966928760524634989849 := by
  unfold tailWord_6740209
  simp only [CollatzResearch.WordTrace]
  refine ⟨245835618438381403895687681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163890412292254269263791787 245835618438381403895687681)
  ·
    refine ⟨184376713828786052921765761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245835618438381403895687681 184376713828786052921765761)
    ·
      refine ⟨138282535371589539691324321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184376713828786052921765761 138282535371589539691324321)
      ·
        refine ⟨103711901528692154768493241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138282535371589539691324321 103711901528692154768493241)
        ·
          refine ⟨77783926146519116076369931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103711901528692154768493241 77783926146519116076369931)
          ·
            refine ⟨116675889219778674114554897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77783926146519116076369931 116675889219778674114554897)
            ·
              refine ⟨87506916914834005585916173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116675889219778674114554897 87506916914834005585916173)
              ·
                refine ⟨32815093843062752094718565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87506916914834005585916173 32815093843062752094718565)
                ·
                  refine ⟨6152830095574266017759731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32815093843062752094718565 6152830095574266017759731)
                  ·
                    refine ⟨9229245143361399026639597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152830095574266017759731 9229245143361399026639597)
                    ·
                      refine ⟨3460966928760524634989849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9229245143361399026639597 3460966928760524634989849)
                      ·
                        rfl

theorem cell23_6740209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_6740209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740209 prefixEnd_6740209 := by exact prefixLift 6740209
  have htrace : WordTrace (prefixWord ++ tailWord_6740209) baseStart_6740209 baseEnd_6740209 := by
    simpa [prefixWord, tailWord_6740209, baseEnd_6740209] using wordTrace_append hprefix tailTrace_6740209
  have hstable : (prefixWord ++ tailWord_6740209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740209).length < 2 ^ (prefixWord ++ tailWord_6740209).sum := by decide
  have hdescent : baseEnd_6740209 < baseStart_6740209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740210 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6740210 : Nat := 118140960795 + 6740210 * 2 ^ 59
def prefixEnd_6740210 : Nat := 4983230072969 + 3 ^ 40 * 6740210 * 2
def baseEnd_6740210 : Nat := 3460967442241179131077345

theorem tailTrace_6740210 : CollatzResearch.WordTrace tailWord_6740210 prefixEnd_6740210 3460967442241179131077345 := by
  unfold tailWord_6740210
  simp only [CollatzResearch.WordTrace]
  refine ⟨61458913727844445266618521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163890436607585187377649389 61458913727844445266618521)
  ·
    refine ⟨46094185295883333949963891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61458913727844445266618521 46094185295883333949963891)
    ·
      refine ⟨69141277943825000924945837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46094185295883333949963891 69141277943825000924945837)
      ·
        refine ⟨25927979228934375346854689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69141277943825000924945837 25927979228934375346854689)
        ·
          refine ⟨19445984421700781510141017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25927979228934375346854689 19445984421700781510141017)
          ·
            refine ⟨14584488316275586132605763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19445984421700781510141017 14584488316275586132605763)
            ·
              refine ⟨21876732474413379198908645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14584488316275586132605763 21876732474413379198908645)
              ·
                refine ⟨4101887338952508599795371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21876732474413379198908645 4101887338952508599795371)
                ·
                  refine ⟨6152831008428762899693057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101887338952508599795371 6152831008428762899693057)
                  ·
                    refine ⟨4614623256321572174769793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152831008428762899693057 4614623256321572174769793)
                    ·
                      refine ⟨3460967442241179131077345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614623256321572174769793 3460967442241179131077345)
                      ·
                        rfl

theorem cell23_6740210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6740210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740210 prefixEnd_6740210 := by exact prefixLift 6740210
  have htrace : WordTrace (prefixWord ++ tailWord_6740210) baseStart_6740210 baseEnd_6740210 := by
    simpa [prefixWord, tailWord_6740210, baseEnd_6740210] using wordTrace_append hprefix tailTrace_6740210
  have hstable : (prefixWord ++ tailWord_6740210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740210).length < 2 ^ (prefixWord ++ tailWord_6740210).sum := by decide
  have hdescent : baseEnd_6740210 < baseStart_6740210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740226 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_6740226 : Nat := 118140960795 + 6740226 * 2 ^ 59
def prefixEnd_6740226 : Nat := 4983230072969 + 3 ^ 40 * 6740226 * 2
def baseEnd_6740226 : Nat := 3460975657931651068477271

theorem tailTrace_6740226 : CollatzResearch.WordTrace tailWord_6740226 prefixEnd_6740226 3460975657931651068477271 := by
  unfold tailWord_6740226
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459059619829953949764133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163890825652879877199371021 61459059619829953949764133)
  ·
    refine ⟨11523573678718116365580775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61459059619829953949764133 11523573678718116365580775)
    ·
      refine ⟨17285360518077174548371163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523573678718116365580775 17285360518077174548371163)
      ·
        refine ⟨25928040777115761822556745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285360518077174548371163 25928040777115761822556745)
        ·
          refine ⟨19446030582836821366917559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25928040777115761822556745 19446030582836821366917559)
          ·
            refine ⟨29169045874255232050376339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19446030582836821366917559 29169045874255232050376339)
            ·
              refine ⟨43753568811382848075564509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29169045874255232050376339 43753568811382848075564509)
              ·
                refine ⟨16407588304268568028336691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43753568811382848075564509 16407588304268568028336691)
                ·
                  refine ⟨24611382456402852042505037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16407588304268568028336691 24611382456402852042505037)
                  ·
                    refine ⟨9229268421151069515939389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24611382456402852042505037 9229268421151069515939389)
                    ·
                      refine ⟨3460975657931651068477271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9229268421151069515939389 3460975657931651068477271)
                      ·
                        rfl

theorem cell23_6740226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_6740226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740226 prefixEnd_6740226 := by exact prefixLift 6740226
  have htrace : WordTrace (prefixWord ++ tailWord_6740226) baseStart_6740226 baseEnd_6740226 := by
    simpa [prefixWord, tailWord_6740226, baseEnd_6740226] using wordTrace_append hprefix tailTrace_6740226
  have hstable : (prefixWord ++ tailWord_6740226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740226).length < 2 ^ (prefixWord ++ tailWord_6740226).sum := by decide
  have hdescent : baseEnd_6740226 < baseStart_6740226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740236 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 1, 3, 2]
def baseStart_6740236 : Nat := 118140960795 + 6740236 * 2 ^ 59
def prefixEnd_6740236 : Nat := 4983230072969 + 3 ^ 40 * 6740236 * 2
def baseEnd_6740236 : Nat := 3460980792738196029352225

theorem tailTrace_6740236 : CollatzResearch.WordTrace tailWord_6740236 prefixEnd_6740236 3460980792738196029352225 := by
  unfold tailWord_6740236
  simp only [CollatzResearch.WordTrace]
  refine ⟨122918301604641793753460281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163891068806189058337947041 122918301604641793753460281)
  ·
    refine ⟨92188726203481345315095211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122918301604641793753460281 92188726203481345315095211)
    ·
      refine ⟨138283089305222017972642817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92188726203481345315095211 138283089305222017972642817)
      ·
        refine ⟨103712316978916513479482113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138283089305222017972642817 103712316978916513479482113)
        ·
          refine ⟨77784237734187385109611585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103712316978916513479482113 77784237734187385109611585)
          ·
            refine ⟨58338178300640538832208689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77784237734187385109611585 58338178300640538832208689)
            ·
              refine ⟨43753633725480404124156517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58338178300640538832208689 43753633725480404124156517)
              ·
                refine ⟨8203806323527575773279347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43753633725480404124156517 8203806323527575773279347)
                ·
                  refine ⟨12305709485291363659919021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203806323527575773279347 12305709485291363659919021)
                  ·
                    refine ⟨4614641056984261372469633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12305709485291363659919021 4614641056984261372469633)
                    ·
                      refine ⟨3460980792738196029352225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614641056984261372469633 3460980792738196029352225)
                      ·
                        rfl

theorem cell23_6740236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_6740236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740236 prefixEnd_6740236 := by exact prefixLift 6740236
  have htrace : WordTrace (prefixWord ++ tailWord_6740236) baseStart_6740236 baseEnd_6740236 := by
    simpa [prefixWord, tailWord_6740236, baseEnd_6740236] using wordTrace_append hprefix tailTrace_6740236
  have hstable : (prefixWord ++ tailWord_6740236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740236).length < 2 ^ (prefixWord ++ tailWord_6740236).sum := by decide
  have hdescent : baseEnd_6740236 < baseStart_6740236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740252 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6740252 : Nat := 118140960795 + 6740252 * 2 ^ 59
def prefixEnd_6740252 : Nat := 4983230072969 + 3 ^ 40 * 6740252 * 2
def baseEnd_6740252 : Nat := 3460989008428667966752151

theorem tailTrace_6740252 : CollatzResearch.WordTrace tailWord_6740252 prefixEnd_6740252 3460989008428667966752151 := by
  unfold tailWord_6740252
  simp only [CollatzResearch.WordTrace]
  refine ⟨122918593388612811119751505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163891457851483748159668673 122918593388612811119751505)
  ·
    refine ⟨92188945041459608339813629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122918593388612811119751505 92188945041459608339813629)
    ·
      refine ⟨34570854390547353127430111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92188945041459608339813629 34570854390547353127430111)
      ·
        refine ⟨51856281585821029691145167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34570854390547353127430111 51856281585821029691145167)
        ·
          refine ⟨77784422378731544536717751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51856281585821029691145167 77784422378731544536717751)
          ·
            refine ⟨116676633568097316805076627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77784422378731544536717751 116676633568097316805076627)
            ·
              refine ⟨175014950352145975207614941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116676633568097316805076627 175014950352145975207614941)
              ·
                refine ⟨65630606382054740702855603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175014950352145975207614941 65630606382054740702855603)
                ·
                  refine ⟨98445909573082111054283405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65630606382054740702855603 98445909573082111054283405)
                  ·
                    refine ⟨36917216089905791645356277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98445909573082111054283405 36917216089905791645356277)
                    ·
                      refine ⟨3460989008428667966752151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36917216089905791645356277 3460989008428667966752151)
                      ·
                        rfl

theorem cell23_6740252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6740252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740252 prefixEnd_6740252 := by exact prefixLift 6740252
  have htrace : WordTrace (prefixWord ++ tailWord_6740252) baseStart_6740252 baseEnd_6740252 := by
    simpa [prefixWord, tailWord_6740252, baseEnd_6740252] using wordTrace_append hprefix tailTrace_6740252
  have hstable : (prefixWord ++ tailWord_6740252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740252).length < 2 ^ (prefixWord ++ tailWord_6740252).sum := by decide
  have hdescent : baseEnd_6740252 < baseStart_6740252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740306 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 5]
def baseStart_6740306 : Nat := 118140960795 + 6740306 * 2 ^ 59
def prefixEnd_6740306 : Nat := 4983230072969 + 3 ^ 40 * 6740306 * 2
def baseEnd_6740306 : Nat := 384557415153778972830767

theorem tailTrace_6740306 : CollatzResearch.WordTrace tailWord_6740306 prefixEnd_6740306 384557415153778972830767 := by
  unfold tailWord_6740306
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459789079757497365492193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163892770879353326307979181 61459789079757497365492193)
  ·
    refine ⟨46094841809818123024119145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61459789079757497365492193 46094841809818123024119145)
    ·
      refine ⟨34571131357363592268089359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46094841809818123024119145 34571131357363592268089359)
      ·
        refine ⟨51856697036045388402134039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34571131357363592268089359 51856697036045388402134039)
        ·
          refine ⟨77785045554068082603201059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51856697036045388402134039 77785045554068082603201059)
          ·
            refine ⟨116677568331102123904801589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77785045554068082603201059 116677568331102123904801589)
            ·
              refine ⟨10938522031040824116075149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116677568331102123904801589 10938522031040824116075149)
              ·
                refine ⟨4101945761640309043528181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938522031040824116075149 4101945761640309043528181)
                ·
                  refine ⟨384557415153778972830767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101945761640309043528181 384557415153778972830767)
                  ·
                    rfl

theorem cell23_6740306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_6740306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740306 prefixEnd_6740306 := by exact prefixLift 6740306
  have htrace : WordTrace (prefixWord ++ tailWord_6740306) baseStart_6740306 baseEnd_6740306 := by
    simpa [prefixWord, tailWord_6740306, baseEnd_6740306] using wordTrace_append hprefix tailTrace_6740306
  have hstable : (prefixWord ++ tailWord_6740306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740306).length < 2 ^ (prefixWord ++ tailWord_6740306).sum := by decide
  have hdescent : baseEnd_6740306 < baseStart_6740306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740352 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_6740352 : Nat := 118140960795 + 6740352 * 2 ^ 59
def prefixEnd_6740352 : Nat := 4983230072969 + 3 ^ 40 * 6740352 * 2
def baseEnd_6740352 : Nat := 3461040356494117575501691

theorem tailTrace_6740352 : CollatzResearch.WordTrace tailWord_6740352 prefixEnd_6740352 3461040356494117575501691 := by
  unfold tailWord_6740352
  simp only [CollatzResearch.WordTrace]
  refine ⟨122920417038431669659071655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163893889384575559545428873 122920417038431669659071655)
  ·
    refine ⟨184380625557647504488607483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122920417038431669659071655 184380625557647504488607483)
    ·
      refine ⟨276570938336471256732911225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184380625557647504488607483 276570938336471256732911225)
      ·
        refine ⟨207428203752353442549683419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276570938336471256732911225 207428203752353442549683419)
        ·
          refine ⟨311142305628530163824525129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207428203752353442549683419 311142305628530163824525129)
          ·
            refine ⟨233356729221397622868393847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311142305628530163824525129 233356729221397622868393847)
            ·
              refine ⟨350035093832096434302590771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233356729221397622868393847 350035093832096434302590771)
              ·
                refine ⟨525052640748144651453886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350035093832096434302590771 525052640748144651453886157)
                ·
                  refine ⟨196894740280554244295207309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525052640748144651453886157 196894740280554244295207309)
                  ·
                    refine ⟨73835527605207841610702741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196894740280554244295207309 73835527605207841610702741)
                    ·
                      refine ⟨3461040356494117575501691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73835527605207841610702741 3461040356494117575501691)
                      ·
                        rfl

theorem cell23_6740352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_6740352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740352 prefixEnd_6740352 := by exact prefixLift 6740352
  have htrace : WordTrace (prefixWord ++ tailWord_6740352) baseStart_6740352 baseEnd_6740352 := by
    simpa [prefixWord, tailWord_6740352, baseEnd_6740352] using wordTrace_append hprefix tailTrace_6740352
  have hstable : (prefixWord ++ tailWord_6740352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740352).length < 2 ^ (prefixWord ++ tailWord_6740352).sum := by decide
  have hdescent : baseEnd_6740352 < baseStart_6740352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740356 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6740356 : Nat := 118140960795 + 6740356 * 2 ^ 59
def prefixEnd_6740356 : Nat := 4983230072969 + 3 ^ 40 * 6740356 * 2
def baseEnd_6740356 : Nat := 3461042410416735559851673

theorem tailTrace_6740356 : CollatzResearch.WordTrace tailWord_6740356 prefixEnd_6740356 3461042410416735559851673 := by
  unfold tailWord_6740356
  simp only [CollatzResearch.WordTrace]
  refine ⟨122920489984424424000644461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163893986645899232000859281 122920489984424424000644461)
  ·
    refine ⟨46095183744159159000241673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122920489984424424000644461 46095183744159159000241673)
    ·
      refine ⟨34571387808119369250181255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46095183744159159000241673 34571387808119369250181255)
      ·
        refine ⟨51857081712179053875271883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34571387808119369250181255 51857081712179053875271883)
        ·
          refine ⟨77785622568268580812907825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51857081712179053875271883 77785622568268580812907825)
          ·
            refine ⟨58339216926201435609680869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77785622568268580812907825 58339216926201435609680869)
            ·
              refine ⟨10938603173662769176815163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58339216926201435609680869 10938603173662769176815163)
              ·
                refine ⟨16407904760494153765222745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10938603173662769176815163 16407904760494153765222745)
                ·
                  refine ⟨12305928570370615323917059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16407904760494153765222745 12305928570370615323917059)
                  ·
                    refine ⟨18458892855555922985875589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12305928570370615323917059 18458892855555922985875589)
                    ·
                      refine ⟨3461042410416735559851673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18458892855555922985875589 3461042410416735559851673)
                      ·
                        rfl

theorem cell23_6740356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6740356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740356 prefixEnd_6740356 := by exact prefixLift 6740356
  have htrace : WordTrace (prefixWord ++ tailWord_6740356) baseStart_6740356 baseEnd_6740356 := by
    simpa [prefixWord, tailWord_6740356, baseEnd_6740356] using wordTrace_append hprefix tailTrace_6740356
  have hstable : (prefixWord ++ tailWord_6740356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740356).length < 2 ^ (prefixWord ++ tailWord_6740356).sum := by decide
  have hdescent : baseEnd_6740356 < baseStart_6740356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740383 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 1, 4]
def baseStart_6740383 : Nat := 118140960795 + 6740383 * 2 ^ 59
def prefixEnd_6740383 : Nat := 4983230072969 + 3 ^ 40 * 6740383 * 2
def baseEnd_6740383 : Nat := 1153685424798135651404683

theorem tailTrace_6740383 : CollatzResearch.WordTrace tailWord_6740383 prefixEnd_6740383 1153685424798135651404683 := by
  unfold tailWord_6740383
  simp only [CollatzResearch.WordTrace]
  refine ⟨245841964739751031612521803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163894643159834021075014535 245841964739751031612521803)
  ·
    refine ⟨368762947109626547418782705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245841964739751031612521803 368762947109626547418782705)
    ·
      refine ⟨276572210332219910564087029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368762947109626547418782705 276572210332219910564087029)
      ·
        refine ⟨25928644718645616615383159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276572210332219910564087029 25928644718645616615383159)
        ·
          refine ⟨38892967077968424923074739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25928644718645616615383159 38892967077968424923074739)
          ·
            refine ⟨58339450616952637384612109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38892967077968424923074739 58339450616952637384612109)
            ·
              refine ⟨21877293981357239019229541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58339450616952637384612109 21877293981357239019229541)
              ·
                refine ⟨4101992621504482316105539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21877293981357239019229541 4101992621504482316105539)
                ·
                  refine ⟨6152988932256723474158309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101992621504482316105539 6152988932256723474158309)
                  ·
                    refine ⟨1153685424798135651404683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6152988932256723474158309 1153685424798135651404683)
                    ·
                      rfl

theorem cell23_6740383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_6740383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740383 prefixEnd_6740383 := by exact prefixLift 6740383
  have htrace : WordTrace (prefixWord ++ tailWord_6740383) baseStart_6740383 baseEnd_6740383 := by
    simpa [prefixWord, tailWord_6740383, baseEnd_6740383] using wordTrace_append hprefix tailTrace_6740383
  have hstable : (prefixWord ++ tailWord_6740383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740383).length < 2 ^ (prefixWord ++ tailWord_6740383).sum := by decide
  have hdescent : baseEnd_6740383 < baseStart_6740383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740426 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_6740426 : Nat := 118140960795 + 6740426 * 2 ^ 59
def prefixEnd_6740426 : Nat := 4983230072969 + 3 ^ 40 * 6740426 * 2
def baseEnd_6740426 : Nat := 1153692784687516761992117

theorem tailTrace_6740426 : CollatzResearch.WordTrace tailWord_6740426 prefixEnd_6740426 1153692784687516761992117 := by
  unfold tailWord_6740426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61460883269648812489084283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163895688719063499970891421 61460883269648812489084283)
  ·
    refine ⟨92191324904473218733626425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61460883269648812489084283 92191324904473218733626425)
    ·
      refine ⟨69143493678354914050219819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92191324904473218733626425 69143493678354914050219819)
      ·
        refine ⟨103715240517532371075329729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69143493678354914050219819 103715240517532371075329729)
        ·
          refine ⟨77786430388149278306497297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103715240517532371075329729 77786430388149278306497297)
          ·
            refine ⟨58339822791111958729872973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77786430388149278306497297 58339822791111958729872973)
            ·
              refine ⟨21877433546666984523702365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58339822791111958729872973 21877433546666984523702365)
              ·
                refine ⟨8204037580000119196388387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21877433546666984523702365 8204037580000119196388387)
                ·
                  refine ⟨12306056370000178794582581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204037580000119196388387 12306056370000178794582581)
                  ·
                    refine ⟨1153692784687516761992117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12306056370000178794582581 1153692784687516761992117)
                    ·
                      rfl

theorem cell23_6740426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_6740426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740426 prefixEnd_6740426 := by exact prefixLift 6740426
  have htrace : WordTrace (prefixWord ++ tailWord_6740426) baseStart_6740426 baseEnd_6740426 := by
    simpa [prefixWord, tailWord_6740426, baseEnd_6740426] using wordTrace_append hprefix tailTrace_6740426
  have hstable : (prefixWord ++ tailWord_6740426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740426).length < 2 ^ (prefixWord ++ tailWord_6740426).sum := by decide
  have hdescent : baseEnd_6740426 < baseStart_6740426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740456 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6740456 : Nat := 118140960795 + 6740456 * 2 ^ 59
def prefixEnd_6740456 : Nat := 4983230072969 + 3 ^ 40 * 6740456 * 2
def baseEnd_6740456 : Nat := 1153697919494061722867071

theorem tailTrace_6740456 : CollatzResearch.WordTrace tailWord_6740456 prefixEnd_6740456 1153697919494061722867071 := by
  unfold tailWord_6740456
  simp only [CollatzResearch.WordTrace]
  refine ⟨122922313634243282539964611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163896418178991043386619481 122922313634243282539964611)
  ·
    refine ⟨184383470451364923809946917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122922313634243282539964611 184383470451364923809946917)
    ·
      refine ⟨34571900709630923214365047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184383470451364923809946917 34571900709630923214365047)
      ·
        refine ⟨51857851064446384821547571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34571900709630923214365047 51857851064446384821547571)
        ·
          refine ⟨77786776596669577232321357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51857851064446384821547571 77786776596669577232321357)
          ·
            refine ⟨29170041223751091462120509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77786776596669577232321357 29170041223751091462120509)
            ·
              refine ⟨10938765458906659298295191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29170041223751091462120509 10938765458906659298295191)
              ·
                refine ⟨16408148188359988947442787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10938765458906659298295191 16408148188359988947442787)
                ·
                  refine ⟨24612222282539983421164181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16408148188359988947442787 24612222282539983421164181)
                  ·
                    refine ⟨1153697919494061722867071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24612222282539983421164181 1153697919494061722867071)
                    ·
                      rfl

theorem cell23_6740456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6740456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740456 prefixEnd_6740456 := by exact prefixLift 6740456
  have htrace : WordTrace (prefixWord ++ tailWord_6740456) baseStart_6740456 baseEnd_6740456 := by
    simpa [prefixWord, tailWord_6740456, baseEnd_6740456] using wordTrace_append hprefix tailTrace_6740456
  have hstable : (prefixWord ++ tailWord_6740456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740456).length < 2 ^ (prefixWord ++ tailWord_6740456).sum := by decide
  have hdescent : baseEnd_6740456 < baseStart_6740456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740459 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_6740459 : Nat := 118140960795 + 6740459 * 2 ^ 59
def prefixEnd_6740459 : Nat := 4983230072969 + 3 ^ 40 * 6740459 * 2
def baseEnd_6740459 : Nat := 3461095298924148656863699

theorem tailTrace_6740459 : CollatzResearch.WordTrace tailWord_6740459 prefixEnd_6740459 3461095298924148656863699 := by
  unfold tailWord_6740459
  simp only [CollatzResearch.WordTrace]
  refine ⟨245844736687475696592288431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163896491124983797728192287 245844736687475696592288431)
  ·
    refine ⟨368767105031213544888432647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245844736687475696592288431 368767105031213544888432647)
    ·
      refine ⟨553150657546820317332648971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368767105031213544888432647 553150657546820317332648971)
      ·
        refine ⟨829725986320230475998973457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553150657546820317332648971 829725986320230475998973457)
        ·
          refine ⟨622294489740172856999230093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829725986320230475998973457 622294489740172856999230093)
          ·
            refine ⟨233360433652564821374711285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622294489740172856999230093 233360433652564821374711285)
            ·
              refine ⟨21877540654927952003879183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233360433652564821374711285 21877540654927952003879183)
              ·
                refine ⟨32816310982391928005818775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21877540654927952003879183 32816310982391928005818775)
                ·
                  refine ⟨49224466473587892008728163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32816310982391928005818775 49224466473587892008728163)
                  ·
                    refine ⟨73836699710381838013092245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49224466473587892008728163 73836699710381838013092245)
                    ·
                      refine ⟨3461095298924148656863699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73836699710381838013092245 3461095298924148656863699)
                      ·
                        rfl

theorem cell23_6740459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_6740459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740459 prefixEnd_6740459 := by exact prefixLift 6740459
  have htrace : WordTrace (prefixWord ++ tailWord_6740459) baseStart_6740459 baseEnd_6740459 := by
    simpa [prefixWord, tailWord_6740459, baseEnd_6740459] using wordTrace_append hprefix tailTrace_6740459
  have hstable : (prefixWord ++ tailWord_6740459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740459).length < 2 ^ (prefixWord ++ tailWord_6740459).sum := by decide
  have hdescent : baseEnd_6740459 < baseStart_6740459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740499 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 2, 7]
def baseStart_6740499 : Nat := 118140960795 + 6740499 * 2 ^ 59
def prefixEnd_6740499 : Nat := 4983230072969 + 3 ^ 40 * 6740499 * 2
def baseEnd_6740499 : Nat := 1153705279383442833454505

theorem tailTrace_6740499 : CollatzResearch.WordTrace tailWord_6740499 prefixEnd_6740499 1153705279383442833454505 := by
  unfold tailWord_6740499
  simp only [CollatzResearch.WordTrace]
  refine ⟨245846195607330783423744551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163897463738220522282496367 245846195607330783423744551)
  ·
    refine ⟨368769293410996175135616827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245846195607330783423744551 368769293410996175135616827)
    ·
      refine ⟨553153940116494262703425241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368769293410996175135616827 553153940116494262703425241)
      ·
        refine ⟨414865455087370697027568931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553153940116494262703425241 414865455087370697027568931)
        ·
          refine ⟨622298182631056045541353397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414865455087370697027568931 622298182631056045541353397)
          ·
            refine ⟨58340454621661504269501881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 622298182631056045541353397 58340454621661504269501881)
            ·
              refine ⟨43755340966246128202126411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58340454621661504269501881 43755340966246128202126411)
              ·
                refine ⟨65633011449369192303189617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43755340966246128202126411 65633011449369192303189617)
                ·
                  refine ⟨49224758587026894227392213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65633011449369192303189617 49224758587026894227392213)
                  ·
                    refine ⟨1153705279383442833454505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49224758587026894227392213 1153705279383442833454505)
                    ·
                      rfl

theorem cell23_6740499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_6740499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740499 prefixEnd_6740499 := by exact prefixLift 6740499
  have htrace : WordTrace (prefixWord ++ tailWord_6740499) baseStart_6740499 baseEnd_6740499 := by
    simpa [prefixWord, tailWord_6740499, baseEnd_6740499] using wordTrace_append hprefix tailTrace_6740499
  have hstable : (prefixWord ++ tailWord_6740499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740499).length < 2 ^ (prefixWord ++ tailWord_6740499).sum := by decide
  have hdescent : baseEnd_6740499 < baseStart_6740499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740503 : List Nat := [1, 1, 3, 6, 1, 1, 2, 8]
def baseStart_6740503 : Nat := 118140960795 + 6740503 * 2 ^ 59
def prefixEnd_6740503 : Nat := 4983230072969 + 3 ^ 40 * 6740503 * 2
def baseEnd_6740503 : Nat := 128189551558257277211611

theorem tailTrace_6740503 : CollatzResearch.WordTrace tailWord_6740503 prefixEnd_6740503 128189551558257277211611 := by
  unfold tailWord_6740503
  simp only [CollatzResearch.WordTrace]
  refine ⟨245846341499316292106890163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163897560999544194737926775 245846341499316292106890163)
  ·
    refine ⟨368769512248974438160335245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245846341499316292106890163 368769512248974438160335245)
    ·
      refine ⟨138288567093365414310125717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368769512248974438160335245 138288567093365414310125717)
      ·
        refine ⟨6482276582501503795787143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138288567093365414310125717 6482276582501503795787143)
        ·
          refine ⟨9723414873752255693680715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482276582501503795787143 9723414873752255693680715)
          ·
            refine ⟨14585122310628383540521073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723414873752255693680715 14585122310628383540521073)
            ·
              refine ⟨10938841732971287655390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14585122310628383540521073 10938841732971287655390805)
              ·
                refine ⟨128189551558257277211611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10938841732971287655390805 128189551558257277211611)
                ·
                  rfl

theorem cell23_6740503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 8].length) (baseStart_6740503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740503 prefixEnd_6740503 := by exact prefixLift 6740503
  have htrace : WordTrace (prefixWord ++ tailWord_6740503) baseStart_6740503 baseEnd_6740503 := by
    simpa [prefixWord, tailWord_6740503, baseEnd_6740503] using wordTrace_append hprefix tailTrace_6740503
  have hstable : (prefixWord ++ tailWord_6740503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740503).length < 2 ^ (prefixWord ++ tailWord_6740503).sum := by decide
  have hdescent : baseEnd_6740503 < baseStart_6740503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740539 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_6740539 : Nat := 118140960795 + 6740539 * 2 ^ 59
def prefixEnd_6740539 : Nat := 4983230072969 + 3 ^ 40 * 6740539 * 2
def baseEnd_6740539 : Nat := 3461136377376508343863331

theorem tailTrace_6740539 : CollatzResearch.WordTrace tailWord_6740539 prefixEnd_6740539 3461136377376508343863331 := by
  unfold tailWord_6740539
  simp only [CollatzResearch.WordTrace]
  refine ⟨245847654527185870255200671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163898436351457246836800447 245847654527185870255200671)
  ·
    refine ⟨368771481790778805382801007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245847654527185870255200671 368771481790778805382801007)
    ·
      refine ⟨553157222686168208074201511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368771481790778805382801007 553157222686168208074201511)
      ·
        refine ⟨829735834029252312111302267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553157222686168208074201511 829735834029252312111302267)
        ·
          refine ⟨1244603751043878468166953401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829735834029252312111302267 1244603751043878468166953401)
          ·
            refine ⟨933452813282908851125215051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244603751043878468166953401 933452813282908851125215051)
            ·
              refine ⟨1400179219924363276687822577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933452813282908851125215051 1400179219924363276687822577)
              ·
                refine ⟨1050134414943272457515866933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400179219924363276687822577 1050134414943272457515866933)
                ·
                  refine ⟨98450101400931792892112525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1050134414943272457515866933 98450101400931792892112525)
                  ·
                    refine ⟨36918788025349422334542197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98450101400931792892112525 36918788025349422334542197)
                    ·
                      refine ⟨3461136377376508343863331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36918788025349422334542197 3461136377376508343863331)
                      ·
                        rfl

theorem cell23_6740539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_6740539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740539 prefixEnd_6740539 := by exact prefixLift 6740539
  have htrace : WordTrace (prefixWord ++ tailWord_6740539) baseStart_6740539 baseEnd_6740539 := by
    simpa [prefixWord, tailWord_6740539, baseEnd_6740539] using wordTrace_append hprefix tailTrace_6740539
  have hstable : (prefixWord ++ tailWord_6740539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740539).length < 2 ^ (prefixWord ++ tailWord_6740539).sum := by decide
  have hdescent : baseEnd_6740539 < baseStart_6740539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740548 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6740548 : Nat := 118140960795 + 6740548 * 2 ^ 59
def prefixEnd_6740548 : Nat := 4983230072969 + 3 ^ 40 * 6740548 * 2
def baseEnd_6740548 : Nat := 3461140998702398808650791

theorem tailTrace_6740548 : CollatzResearch.WordTrace tailWord_6740548 prefixEnd_6740548 3461140998702398808650791 := by
  unfold tailWord_6740548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122923991392076632396139149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163898655189435509861518865 122923991392076632396139149)
  ·
    refine ⟨46096496772028737148552181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122923991392076632396139149 46096496772028737148552181)
    ·
      refine ⟨4321546572377694107676767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46096496772028737148552181 4321546572377694107676767)
      ·
        refine ⟨6482319858566541161515151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321546572377694107676767 6482319858566541161515151)
        ·
          refine ⟨9723479787849811742272727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482319858566541161515151 9723479787849811742272727)
          ·
            refine ⟨14585219681774717613409091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723479787849811742272727 14585219681774717613409091)
            ·
              refine ⟨21877829522662076420113637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14585219681774717613409091 21877829522662076420113637)
              ·
                refine ⟨4102093035499139328771307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21877829522662076420113637 4102093035499139328771307)
                ·
                  refine ⟨6153139553248708993156961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102093035499139328771307 6153139553248708993156961)
                  ·
                    refine ⟨4614854664936531744867721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6153139553248708993156961 4614854664936531744867721)
                    ·
                      refine ⟨3461140998702398808650791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614854664936531744867721 3461140998702398808650791)
                      ·
                        rfl

theorem cell23_6740548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6740548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740548 prefixEnd_6740548 := by exact prefixLift 6740548
  have htrace : WordTrace (prefixWord ++ tailWord_6740548) baseStart_6740548 baseEnd_6740548 := by
    simpa [prefixWord, tailWord_6740548, baseEnd_6740548] using wordTrace_append hprefix tailTrace_6740548
  have hstable : (prefixWord ++ tailWord_6740548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740548).length < 2 ^ (prefixWord ++ tailWord_6740548).sum := by decide
  have hdescent : baseEnd_6740548 < baseStart_6740548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740556 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_6740556 : Nat := 118140960795 + 6740556 * 2 ^ 59
def prefixEnd_6740556 : Nat := 4983230072969 + 3 ^ 40 * 6740556 * 2
def baseEnd_6740556 : Nat := 3461145106547634777350753

theorem tailTrace_6740556 : CollatzResearch.WordTrace tailWord_6740556 prefixEnd_6740556 3461145106547634777350753 := by
  unfold tailWord_6740556
  simp only [CollatzResearch.WordTrace]
  refine ⟨122924137284062141079284761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163898849712082854772379681 122924137284062141079284761)
  ·
    refine ⟨92193102963046605809463571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122924137284062141079284761 92193102963046605809463571)
    ·
      refine ⟨138289654444569908714195357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92193102963046605809463571 138289654444569908714195357)
      ·
        refine ⟨51858620416713715767823259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138289654444569908714195357 51858620416713715767823259)
        ·
          refine ⟨77787930625070573651734889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51858620416713715767823259 77787930625070573651734889)
          ·
            refine ⟨58340947968802930238801167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77787930625070573651734889 58340947968802930238801167)
            ·
              refine ⟨87511421953204395358201751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58340947968802930238801167 87511421953204395358201751)
              ·
                refine ⟨131267132929806593037302627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87511421953204395358201751 131267132929806593037302627)
                ·
                  refine ⟨196900699394709889555953941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131267132929806593037302627 196900699394709889555953941)
                  ·
                    refine ⟨9229720284127026072935341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 196900699394709889555953941 9229720284127026072935341)
                    ·
                      refine ⟨3461145106547634777350753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9229720284127026072935341 3461145106547634777350753)
                      ·
                        rfl

theorem cell23_6740556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_6740556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740556 prefixEnd_6740556 := by exact prefixLift 6740556
  have htrace : WordTrace (prefixWord ++ tailWord_6740556) baseStart_6740556 baseEnd_6740556 := by
    simpa [prefixWord, tailWord_6740556, baseEnd_6740556] using wordTrace_append hprefix tailTrace_6740556
  have hstable : (prefixWord ++ tailWord_6740556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740556).length < 2 ^ (prefixWord ++ tailWord_6740556).sum := by decide
  have hdescent : baseEnd_6740556 < baseStart_6740556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740643 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 4, 2]
def baseStart_6740643 : Nat := 118140960795 + 6740643 * 2 ^ 59
def prefixEnd_6740643 : Nat := 4983230072969 + 3 ^ 40 * 6740643 * 2
def baseEnd_6740643 : Nat := 3461189779364575936962853

theorem tailTrace_6740643 : CollatzResearch.WordTrace tailWord_6740643 prefixEnd_6740643 3461189779364575936962853 := by
  unfold tailWord_6740643
  simp only [CollatzResearch.WordTrace]
  refine ⟨245851447718809096016986583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163900965145872730677991055 245851447718809096016986583)
  ·
    refine ⟨368777171578213644025479875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245851447718809096016986583 368777171578213644025479875)
    ·
      refine ⟨553165757367320466038219813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368777171578213644025479875 553165757367320466038219813)
      ·
        refine ⟨103718579506372587382166215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 553165757367320466038219813 103718579506372587382166215)
        ·
          refine ⟨155577869259558881073249323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103718579506372587382166215 155577869259558881073249323)
          ·
            refine ⟨233366803889338321609873985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155577869259558881073249323 233366803889338321609873985)
            ·
              refine ⟨175025102917003741207405489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233366803889338321609873985 175025102917003741207405489)
              ·
                refine ⟨131268827187752805905554117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175025102917003741207405489 131268827187752805905554117)
                ·
                  refine ⟨24612905097703651107291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131268827187752805905554117 24612905097703651107291397)
                  ·
                    refine ⟨4614919705819434582617137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24612905097703651107291397 4614919705819434582617137)
                    ·
                      refine ⟨3461189779364575936962853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614919705819434582617137 3461189779364575936962853)
                      ·
                        rfl

theorem cell23_6740643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_6740643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740643 prefixEnd_6740643 := by exact prefixLift 6740643
  have htrace : WordTrace (prefixWord ++ tailWord_6740643) baseStart_6740643 baseEnd_6740643 := by
    simpa [prefixWord, tailWord_6740643, baseEnd_6740643] using wordTrace_append hprefix tailTrace_6740643
  have hstable : (prefixWord ++ tailWord_6740643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740643).length < 2 ^ (prefixWord ++ tailWord_6740643).sum := by decide
  have hdescent : baseEnd_6740643 < baseStart_6740643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740666 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 8]
def baseStart_6740666 : Nat := 118140960795 + 6740666 * 2 ^ 59
def prefixEnd_6740666 : Nat := 4983230072969 + 3 ^ 40 * 6740666 * 2
def baseEnd_6740666 : Nat := 384577954379958816330583

theorem tailTrace_6740666 : CollatzResearch.WordTrace tailWord_6740666 prefixEnd_6740666 384577954379958816330583 := by
  unfold tailWord_6740666
  simp only [CollatzResearch.WordTrace]
  refine ⟨61463071649431442736268463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163901524398483847296715901 61463071649431442736268463)
  ·
    refine ⟨92194607474147164104402695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61463071649431442736268463 92194607474147164104402695)
    ·
      refine ⟨138291911211220746156604043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92194607474147164104402695 138291911211220746156604043)
      ·
        refine ⟨207437866816831119234906065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138291911211220746156604043 207437866816831119234906065)
        ·
          refine ⟨155578400112623339426179549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207437866816831119234906065 155578400112623339426179549)
          ·
            refine ⟨58341900042233752284817331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155578400112623339426179549 58341900042233752284817331)
            ·
              refine ⟨87512850063350628427225997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58341900042233752284817331 87512850063350628427225997)
              ·
                refine ⟨32817318773756485660209749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87512850063350628427225997 32817318773756485660209749)
                ·
                  refine ⟨384577954379958816330583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32817318773756485660209749 384577954379958816330583)
                  ·
                    rfl

theorem cell23_6740666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_6740666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740666 prefixEnd_6740666 := by exact prefixLift 6740666
  have htrace : WordTrace (prefixWord ++ tailWord_6740666) baseStart_6740666 baseEnd_6740666 := by
    simpa [prefixWord, tailWord_6740666, baseEnd_6740666] using wordTrace_append hprefix tailTrace_6740666
  have hstable : (prefixWord ++ tailWord_6740666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740666).length < 2 ^ (prefixWord ++ tailWord_6740666).sum := by decide
  have hdescent : baseEnd_6740666 < baseStart_6740666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740713 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_6740713 : Nat := 118140960795 + 6740713 * 2 ^ 59
def prefixEnd_6740713 : Nat := 4983230072969 + 3 ^ 40 * 6740713 * 2
def baseEnd_6740713 : Nat := 1153741907670130221029177

theorem tailTrace_6740713 : CollatzResearch.WordTrace tailWord_6740713 prefixEnd_6740713 1153741907670130221029177 := by
  unfold tailWord_6740713
  simp only [CollatzResearch.WordTrace]
  refine ⟨245854000828555497972034793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163902667219036998648023195 245854000828555497972034793)
  ·
    refine ⟨184390500621416623479026095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245854000828555497972034793 184390500621416623479026095)
    ·
      refine ⟨276585750932124935218539143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184390500621416623479026095 276585750932124935218539143)
      ·
        refine ⟨414878626398187402827808715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276585750932124935218539143 414878626398187402827808715)
        ·
          refine ⟨622317939597281104241713073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414878626398187402827808715 622317939597281104241713073)
          ·
            refine ⟨466738454697960828181284805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622317939597281104241713073 466738454697960828181284805)
            ·
              refine ⟨87513460255867655283990901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466738454697960828181284805 87513460255867655283990901)
              ·
                refine ⟨8204386898987592682874147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87513460255867655283990901 8204386898987592682874147)
                ·
                  refine ⟨12306580348481389024311221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204386898987592682874147 12306580348481389024311221)
                  ·
                    refine ⟨1153741907670130221029177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12306580348481389024311221 1153741907670130221029177)
                    ·
                      rfl

theorem cell23_6740713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_6740713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740713 prefixEnd_6740713 := by exact prefixLift 6740713
  have htrace : WordTrace (prefixWord ++ tailWord_6740713) baseStart_6740713 baseEnd_6740713 := by
    simpa [prefixWord, tailWord_6740713, baseEnd_6740713] using wordTrace_append hprefix tailTrace_6740713
  have hstable : (prefixWord ++ tailWord_6740713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740713).length < 2 ^ (prefixWord ++ tailWord_6740713).sum := by decide
  have hdescent : baseEnd_6740713 < baseStart_6740713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740720 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2]
def baseStart_6740720 : Nat := 118140960795 + 6740720 * 2 ^ 59
def prefixEnd_6740720 : Nat := 4983230072969 + 3 ^ 40 * 6740720 * 2
def baseEnd_6740720 : Nat := 3461229317374972135699999

theorem tailTrace_6740720 : CollatzResearch.WordTrace tailWord_6740720 prefixEnd_6740720 3461229317374972135699999 := by
  unfold tailWord_6740720
  simp only [CollatzResearch.WordTrace]
  refine ⟨122927128069765069083769807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163902837426353425445026409 122927128069765069083769807)
  ·
    refine ⟨184390692104647603625654711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122927128069765069083769807 184390692104647603625654711)
    ·
      refine ⟨276586038156971405438482067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184390692104647603625654711 276586038156971405438482067)
      ·
        refine ⟨414879057235457108157723101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276586038156971405438482067 414879057235457108157723101)
        ·
          refine ⟨155579646463296415559146163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414879057235457108157723101 155579646463296415559146163)
          ·
            refine ⟨233369469694944623338719245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155579646463296415559146163 233369469694944623338719245)
            ·
              refine ⟨87513551135604233752019717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233369469694944623338719245 87513551135604233752019717)
              ·
                refine ⟨16408790837925793828503697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87513551135604233752019717 16408790837925793828503697)
                ·
                  refine ⟨12306593128444345371377773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16408790837925793828503697 12306593128444345371377773)
                  ·
                    refine ⟨4614972423166629514266665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12306593128444345371377773 4614972423166629514266665)
                    ·
                      refine ⟨3461229317374972135699999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614972423166629514266665 3461229317374972135699999)
                      ·
                        rfl

theorem cell23_6740720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 3, 2].length) (baseStart_6740720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740720 prefixEnd_6740720 := by exact prefixLift 6740720
  have htrace : WordTrace (prefixWord ++ tailWord_6740720) baseStart_6740720 baseEnd_6740720 := by
    simpa [prefixWord, tailWord_6740720, baseEnd_6740720] using wordTrace_append hprefix tailTrace_6740720
  have hstable : (prefixWord ++ tailWord_6740720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740720).length < 2 ^ (prefixWord ++ tailWord_6740720).sum := by decide
  have hdescent : baseEnd_6740720 < baseStart_6740720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740733 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6740733 : Nat := 118140960795 + 6740733 * 2 ^ 59
def prefixEnd_6740733 : Nat := 4983230072969 + 3 ^ 40 * 6740733 * 2
def baseEnd_6740733 : Nat := 3461235992623480584837439

theorem tailTrace_6740733 : CollatzResearch.WordTrace tailWord_6740733 prefixEnd_6740733 3461235992623480584837439 := by
  unfold tailWord_6740733
  simp only [CollatzResearch.WordTrace]
  refine ⟨245854730288483041387762853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163903153525655360925175235 245854730288483041387762853)
  ·
    refine ⟨46097761929090570260205535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245854730288483041387762853 46097761929090570260205535)
    ·
      refine ⟨69146642893635855390308303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46097761929090570260205535 69146642893635855390308303)
      ·
        refine ⟨103719964340453783085462455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69146642893635855390308303 103719964340453783085462455)
        ·
          refine ⟨155579946510680674628193683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103719964340453783085462455 155579946510680674628193683)
          ·
            refine ⟨233369919766021011942290525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155579946510680674628193683 233369919766021011942290525)
            ·
              refine ⟨87513719912257879478358947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233369919766021011942290525 87513719912257879478358947)
              ·
                refine ⟨131270579868386819217538421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87513719912257879478358947 131270579868386819217538421)
                ·
                  refine ⟨12306616862661264301644227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131270579868386819217538421 12306616862661264301644227)
                  ·
                    refine ⟨18459925293991896452466341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12306616862661264301644227 18459925293991896452466341)
                    ·
                      refine ⟨3461235992623480584837439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18459925293991896452466341 3461235992623480584837439)
                      ·
                        rfl

theorem cell23_6740733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6740733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740733 prefixEnd_6740733 := by exact prefixLift 6740733
  have htrace : WordTrace (prefixWord ++ tailWord_6740733) baseStart_6740733 baseEnd_6740733 := by
    simpa [prefixWord, tailWord_6740733, baseEnd_6740733] using wordTrace_append hprefix tailTrace_6740733
  have hstable : (prefixWord ++ tailWord_6740733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740733).length < 2 ^ (prefixWord ++ tailWord_6740733).sum := by decide
  have hdescent : baseEnd_6740733 < baseStart_6740733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6740750 : Nat := 118140960795 + 6740750 * 2 ^ 59
def prefixEnd_6740750 : Nat := 4983230072969 + 3 ^ 40 * 6740750 * 2
def baseEnd_6740750 : Nat := 3461244721794607018324861

theorem tailTrace_6740750 : CollatzResearch.WordTrace tailWord_6740750 prefixEnd_6740750 3461244721794607018324861 := by
  unfold tailWord_6740750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30731918791177681661391463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163903566886280968860754469 30731918791177681661391463)
  ·
    refine ⟨46097878186766522492087195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30731918791177681661391463 46097878186766522492087195)
    ·
      refine ⟨69146817280149783738130793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46097878186766522492087195 69146817280149783738130793)
      ·
        refine ⟨51860112960112337803598095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69146817280149783738130793 51860112960112337803598095)
        ·
          refine ⟨77790169440168506705397143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51860112960112337803598095 77790169440168506705397143)
          ·
            refine ⟨116685254160252760058095715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77790169440168506705397143 116685254160252760058095715)
            ·
              refine ⟨175027881240379140087143573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116685254160252760058095715 175027881240379140087143573)
              ·
                refine ⟨8204431933142772191584855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175027881240379140087143573 8204431933142772191584855)
                ·
                  refine ⟨12306647899714158287377283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204431933142772191584855 12306647899714158287377283)
                  ·
                    refine ⟨18459971849571237431065925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12306647899714158287377283 18459971849571237431065925)
                    ·
                      refine ⟨3461244721794607018324861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18459971849571237431065925 3461244721794607018324861)
                      ·
                        rfl

theorem cell23_6740750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6740750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740750 prefixEnd_6740750 := by exact prefixLift 6740750
  have htrace : WordTrace (prefixWord ++ tailWord_6740750) baseStart_6740750 baseEnd_6740750 := by
    simpa [prefixWord, tailWord_6740750, baseEnd_6740750] using wordTrace_append hprefix tailTrace_6740750
  have hstable : (prefixWord ++ tailWord_6740750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740750).length < 2 ^ (prefixWord ++ tailWord_6740750).sum := by decide
  have hdescent : baseEnd_6740750 < baseStart_6740750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740754 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6740754 : Nat := 118140960795 + 6740754 * 2 ^ 59
def prefixEnd_6740754 : Nat := 4983230072969 + 3 ^ 40 * 6740754 * 2
def baseEnd_6740754 : Nat := 3461246775717225002674843

theorem tailTrace_6740754 : CollatzResearch.WordTrace tailWord_6740754 prefixEnd_6740754 3461246775717225002674843 := by
  unfold tailWord_6740754
  simp only [CollatzResearch.WordTrace]
  refine ⟨61463874055351740493569329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163903664147604641316184877 61463874055351740493569329)
  ·
    refine ⟨46097905541513805370176997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61463874055351740493569329 46097905541513805370176997)
    ·
      refine ⟨8643357289033838506908187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46097905541513805370176997 8643357289033838506908187)
      ·
        refine ⟨12965035933550757760362281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8643357289033838506908187 12965035933550757760362281)
        ·
          refine ⟨9723776950163068320271711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12965035933550757760362281 9723776950163068320271711)
          ·
            refine ⟨14585665425244602480407567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723776950163068320271711 14585665425244602480407567)
            ·
              refine ⟨21878498137866903720611351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14585665425244602480407567 21878498137866903720611351)
              ·
                refine ⟨32817747206800355580917027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21878498137866903720611351 32817747206800355580917027)
                ·
                  refine ⟨49226620810200533371375541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32817747206800355580917027 49226620810200533371375541)
                  ·
                    refine ⟨4614995700956300003566457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49226620810200533371375541 4614995700956300003566457)
                    ·
                      refine ⟨3461246775717225002674843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4614995700956300003566457 3461246775717225002674843)
                      ·
                        rfl

theorem cell23_6740754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6740754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740754 prefixEnd_6740754 := by exact prefixLift 6740754
  have htrace : WordTrace (prefixWord ++ tailWord_6740754) baseStart_6740754 baseEnd_6740754 := by
    simpa [prefixWord, tailWord_6740754, baseEnd_6740754] using wordTrace_append hprefix tailTrace_6740754
  have hstable : (prefixWord ++ tailWord_6740754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740754).length < 2 ^ (prefixWord ++ tailWord_6740754).sum := by decide
  have hdescent : baseEnd_6740754 < baseStart_6740754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740767 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 1, 1, 4]
def baseStart_6740767 : Nat := 118140960795 + 6740767 * 2 ^ 59
def prefixEnd_6740767 : Nat := 4983230072969 + 3 ^ 40 * 6740767 * 2
def baseEnd_6740767 : Nat := 3461253450965733451812283

theorem tailTrace_6740767 : CollatzResearch.WordTrace tailWord_6740767 prefixEnd_6740767 3461253450965733451812283 := by
  unfold tailWord_6740767
  simp only [CollatzResearch.WordTrace]
  refine ⟨245855970370359865194500555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163903980246906576796333703 245855970370359865194500555)
  ·
    refine ⟨368783955555539797791750833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245855970370359865194500555 368783955555539797791750833)
    ·
      refine ⟨276587966666654848343813125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368783955555539797791750833 276587966666654848343813125)
      ·
        refine ⟨51860243749997784064464961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276587966666654848343813125 51860243749997784064464961)
        ·
          refine ⟨38895182812498338048348721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51860243749997784064464961 38895182812498338048348721)
          ·
            refine ⟨29171387109373753536261541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38895182812498338048348721 29171387109373753536261541)
            ·
              refine ⟨5469635083007578788049039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29171387109373753536261541 5469635083007578788049039)
              ·
                refine ⟨8204452624511368182073559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469635083007578788049039 8204452624511368182073559)
                ·
                  refine ⟨12306678936767052273110339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204452624511368182073559 12306678936767052273110339)
                  ·
                    refine ⟨18460018405150578409665509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12306678936767052273110339 18460018405150578409665509)
                    ·
                      refine ⟨3461253450965733451812283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18460018405150578409665509 3461253450965733451812283)
                      ·
                        rfl

theorem cell23_6740767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_6740767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740767 prefixEnd_6740767 := by exact prefixLift 6740767
  have htrace : WordTrace (prefixWord ++ tailWord_6740767) baseStart_6740767 baseEnd_6740767 := by
    simpa [prefixWord, tailWord_6740767, baseEnd_6740767] using wordTrace_append hprefix tailTrace_6740767
  have hstable : (prefixWord ++ tailWord_6740767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740767).length < 2 ^ (prefixWord ++ tailWord_6740767).sum := by decide
  have hdescent : baseEnd_6740767 < baseStart_6740767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740794 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_6740794 : Nat := 118140960795 + 6740794 * 2 ^ 59
def prefixEnd_6740794 : Nat := 4983230072969 + 3 ^ 40 * 6740794 * 2
def baseEnd_6740794 : Nat := 1153755771647801615391553

theorem tailTrace_6740794 : CollatzResearch.WordTrace tailWord_6740794 prefixEnd_6740794 1153755771647801615391553 := by
  unfold tailWord_6740794
  simp only [CollatzResearch.WordTrace]
  refine ⟨61464238785315512201433359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163904636760841365870488957 61464238785315512201433359)
  ·
    refine ⟨92196358177973268302150039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61464238785315512201433359 92196358177973268302150039)
    ·
      refine ⟨138294537266959902453225059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92196358177973268302150039 138294537266959902453225059)
      ·
        refine ⟨207441805900439853679837589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138294537266959902453225059 207441805900439853679837589)
        ·
          refine ⟨9723834651583118141242387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207441805900439853679837589 9723834651583118141242387)
          ·
            refine ⟨14585751977374677211863581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723834651583118141242387 14585751977374677211863581)
            ·
              refine ⟨5469656991515503954448843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14585751977374677211863581 5469656991515503954448843)
              ·
                refine ⟨8204485487273255931673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469656991515503954448843 8204485487273255931673265)
                ·
                  refine ⟨6153364115454941948754949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8204485487273255931673265 6153364115454941948754949)
                  ·
                    refine ⟨1153755771647801615391553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6153364115454941948754949 1153755771647801615391553)
                    ·
                      rfl

theorem cell23_6740794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_6740794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740794 prefixEnd_6740794 := by exact prefixLift 6740794
  have htrace : WordTrace (prefixWord ++ tailWord_6740794) baseStart_6740794 baseEnd_6740794 := by
    simpa [prefixWord, tailWord_6740794, baseEnd_6740794] using wordTrace_append hprefix tailTrace_6740794
  have hstable : (prefixWord ++ tailWord_6740794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740794).length < 2 ^ (prefixWord ++ tailWord_6740794).sum := by decide
  have hdescent : baseEnd_6740794 < baseStart_6740794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740833 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_6740833 : Nat := 118140960795 + 6740833 * 2 ^ 59
def prefixEnd_6740833 : Nat := 4983230072969 + 3 ^ 40 * 6740833 * 2
def baseEnd_6740833 : Nat := 1153762446896310064528993

theorem tailTrace_6740833 : CollatzResearch.WordTrace tailWord_6740833 prefixEnd_6740833 1153762446896310064528993 := by
  unfold tailWord_6740833
  simp only [CollatzResearch.WordTrace]
  refine ⟨245858377588120758466403153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163905585058747172310935435 245858377588120758466403153)
  ·
    refine ⟨184393783191090568849802365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245858377588120758466403153 184393783191090568849802365)
    ·
      refine ⟨69147668696658963318675887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184393783191090568849802365 69147668696658963318675887)
      ·
        refine ⟨103721503044988444978013831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69147668696658963318675887 103721503044988444978013831)
        ·
          refine ⟨155582254567482667467020747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103721503044988444978013831 155582254567482667467020747)
          ·
            refine ⟨233373381851224001200531121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155582254567482667467020747 233373381851224001200531121)
            ·
              refine ⟨175030036388418000900398341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233373381851224001200531121 175030036388418000900398341)
              ·
                refine ⟨32818131822828375168824689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175030036388418000900398341 32818131822828375168824689)
                ·
                  refine ⟨24613598867121281376618517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32818131822828375168824689 24613598867121281376618517)
                  ·
                    refine ⟨1153762446896310064528993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24613598867121281376618517 1153762446896310064528993)
                    ·
                      rfl

theorem cell23_6740833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_6740833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740833 prefixEnd_6740833 := by exact prefixLift 6740833
  have htrace : WordTrace (prefixWord ++ tailWord_6740833) baseStart_6740833 baseEnd_6740833 := by
    simpa [prefixWord, tailWord_6740833, baseEnd_6740833] using wordTrace_append hprefix tailTrace_6740833
  have hstable : (prefixWord ++ tailWord_6740833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740833).length < 2 ^ (prefixWord ++ tailWord_6740833).sum := by decide
  have hdescent : baseEnd_6740833 < baseStart_6740833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740863 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 7]
def baseStart_6740863 : Nat := 118140960795 + 6740863 * 2 ^ 59
def prefixEnd_6740863 : Nat := 4983230072969 + 3 ^ 40 * 6740863 * 2
def baseEnd_6740863 : Nat := 384589193900951675134649

theorem tailTrace_6740863 : CollatzResearch.WordTrace tailWord_6740863 prefixEnd_6740863 384589193900951675134649 := by
  unfold tailWord_6740863
  simp only [CollatzResearch.WordTrace]
  refine ⟨245859471778012073589995243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163906314518674715726663495 245859471778012073589995243)
  ·
    refine ⟨368789207667018110384992865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245859471778012073589995243 368789207667018110384992865)
    ·
      refine ⟨276591905750263582788744649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368789207667018110384992865 276591905750263582788744649)
      ·
        refine ⟨207443929312697687091558487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276591905750263582788744649 207443929312697687091558487)
        ·
          refine ⟨311165893969046530637337731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207443929312697687091558487 311165893969046530637337731)
          ·
            refine ⟨466748840953569795956006597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311165893969046530637337731 466748840953569795956006597)
            ·
              refine ⟨87515407678794336741751237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466748840953569795956006597 87515407678794336741751237)
              ·
                refine ⟨16409138939773938139078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87515407678794336741751237 16409138939773938139078357)
                ·
                  refine ⟨384589193900951675134649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16409138939773938139078357 384589193900951675134649)
                  ·
                    rfl

theorem cell23_6740863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 7].length) (baseStart_6740863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740863 prefixEnd_6740863 := by exact prefixLift 6740863
  have htrace : WordTrace (prefixWord ++ tailWord_6740863) baseStart_6740863 baseEnd_6740863 := by
    simpa [prefixWord, tailWord_6740863, baseEnd_6740863] using wordTrace_append hprefix tailTrace_6740863
  have hstable : (prefixWord ++ tailWord_6740863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740863).length < 2 ^ (prefixWord ++ tailWord_6740863).sum := by decide
  have hdescent : baseEnd_6740863 < baseStart_6740863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740874 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6740874 : Nat := 118140960795 + 6740874 * 2 ^ 59
def prefixEnd_6740874 : Nat := 4983230072969 + 3 ^ 40 * 6740874 * 2
def baseEnd_6740874 : Nat := 3461308393395764533174291

theorem tailTrace_6740874 : CollatzResearch.WordTrace tailWord_6740874 prefixEnd_6740874 3461308393395764533174291 := by
  unfold tailWord_6740874
  simp only [CollatzResearch.WordTrace]
  refine ⟨61464968245243055617161419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163906581987314814979097117 61464968245243055617161419)
  ·
    refine ⟨92197452367864583425742129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61464968245243055617161419 92197452367864583425742129)
    ·
      refine ⟨69148089275898437569306597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92197452367864583425742129 69148089275898437569306597)
      ·
        refine ⟨12965266739230957044244987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69148089275898437569306597 12965266739230957044244987)
        ·
          refine ⟨19447900108846435566367481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12965266739230957044244987 19447900108846435566367481)
          ·
            refine ⟨14585925081634826674775611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19447900108846435566367481 14585925081634826674775611)
            ·
              refine ⟨21878887622452240012163417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14585925081634826674775611 21878887622452240012163417)
              ·
                refine ⟨16409165716839180009122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21878887622452240012163417 16409165716839180009122563)
                ·
                  refine ⟨24613748575258770013683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16409165716839180009122563 24613748575258770013683845)
                  ·
                    refine ⟨4615077857861019377565721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24613748575258770013683845 4615077857861019377565721)
                    ·
                      refine ⟨3461308393395764533174291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615077857861019377565721 3461308393395764533174291)
                      ·
                        rfl

theorem cell23_6740874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6740874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740874 prefixEnd_6740874 := by exact prefixLift 6740874
  have htrace : WordTrace (prefixWord ++ tailWord_6740874) baseStart_6740874 baseEnd_6740874 := by
    simpa [prefixWord, tailWord_6740874, baseEnd_6740874] using wordTrace_append hprefix tailTrace_6740874
  have hstable : (prefixWord ++ tailWord_6740874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740874).length < 2 ^ (prefixWord ++ tailWord_6740874).sum := by decide
  have hdescent : baseEnd_6740874 < baseStart_6740874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740917 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_6740917 : Nat := 118140960795 + 6740917 * 2 ^ 59
def prefixEnd_6740917 : Nat := 4983230072969 + 3 ^ 40 * 6740917 * 2
def baseEnd_6740917 : Nat := 3461330473063907864936593

theorem tailTrace_6740917 : CollatzResearch.WordTrace tailWord_6740917 prefixEnd_6740917 3461330473063907864936593 := by
  unfold tailWord_6740917
  simp only [CollatzResearch.WordTrace]
  refine ⟨245861441319816440812461005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163907627546544293874974003 245861441319816440812461005)
  ·
    refine ⟨92198040494931165304672877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245861441319816440812461005 92198040494931165304672877)
    ·
      refine ⟨34574265185599186989252329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92198040494931165304672877 34574265185599186989252329)
      ·
        refine ⟨25930698889199390241939247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34574265185599186989252329 25930698889199390241939247)
        ·
          refine ⟨38896048333799085362908871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25930698889199390241939247 38896048333799085362908871)
          ·
            refine ⟨58344072500698628044363307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38896048333799085362908871 58344072500698628044363307)
            ·
              refine ⟨87516108751047942066544961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58344072500698628044363307 87516108751047942066544961)
              ·
                refine ⟨65637081563285956549908721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87516108751047942066544961 65637081563285956549908721)
                ·
                  refine ⟨49227811172464467412431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65637081563285956549908721 49227811172464467412431541)
                  ·
                    refine ⟨4615107297418543819915457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49227811172464467412431541 4615107297418543819915457)
                    ·
                      refine ⟨3461330473063907864936593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615107297418543819915457 3461330473063907864936593)
                      ·
                        rfl

theorem cell23_6740917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_6740917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740917 prefixEnd_6740917 := by exact prefixLift 6740917
  have htrace : WordTrace (prefixWord ++ tailWord_6740917) baseStart_6740917 baseEnd_6740917 := by
    simpa [prefixWord, tailWord_6740917, baseEnd_6740917] using wordTrace_append hprefix tailTrace_6740917
  have hstable : (prefixWord ++ tailWord_6740917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740917).length < 2 ^ (prefixWord ++ tailWord_6740917).sum := by decide
  have hdescent : baseEnd_6740917 < baseStart_6740917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6740967 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6740967 : Nat := 118140960795 + 6740967 * 2 ^ 59
def prefixEnd_6740967 : Nat := 4983230072969 + 3 ^ 40 * 6740967 * 2
def baseEnd_6740967 : Nat := 3461356147096632669311363

theorem tailTrace_6740967 : CollatzResearch.WordTrace tailWord_6740967 prefixEnd_6740967 3461356147096632669311363 := by
  unfold tailWord_6740967
  simp only [CollatzResearch.WordTrace]
  refine ⟨245863264969635299351781155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163908843313090199567854103 245863264969635299351781155)
  ·
    refine ⟨368794897454452949027671733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245863264969635299351781155 368794897454452949027671733)
    ·
      refine ⟨34574521636354963971344225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 368794897454452949027671733 34574521636354963971344225)
      ·
        refine ⟨25930891227266222978508169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34574521636354963971344225 25930891227266222978508169)
        ·
          refine ⟨19448168420449667233881127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25930891227266222978508169 19448168420449667233881127)
          ·
            refine ⟨29172252630674500850821691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19448168420449667233881127 29172252630674500850821691)
            ·
              refine ⟨43758378946011751276232537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29172252630674500850821691 43758378946011751276232537)
              ·
                refine ⟨32818784209508813457174403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43758378946011751276232537 32818784209508813457174403)
                ·
                  refine ⟨49228176314263220185761605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32818784209508813457174403 49228176314263220185761605)
                  ·
                    refine ⟨9230283058924353784830301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49228176314263220185761605 9230283058924353784830301)
                    ·
                      refine ⟨3461356147096632669311363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230283058924353784830301 3461356147096632669311363)
                      ·
                        rfl

theorem cell23_6740967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6740967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6740967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6740967 prefixEnd_6740967 := by exact prefixLift 6740967
  have htrace : WordTrace (prefixWord ++ tailWord_6740967) baseStart_6740967 baseEnd_6740967 := by
    simpa [prefixWord, tailWord_6740967, baseEnd_6740967] using wordTrace_append hprefix tailTrace_6740967
  have hstable : (prefixWord ++ tailWord_6740967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6740967).length < 2 ^ (prefixWord ++ tailWord_6740967).sum := by decide
  have hdescent : baseEnd_6740967 < baseStart_6740967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6740967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741021 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 6]
def baseStart_6741021 : Nat := 118140960795 + 6741021 * 2 ^ 59
def prefixEnd_6741021 : Nat := 4983230072969 + 3 ^ 40 * 6741021 * 2
def baseEnd_6741021 : Nat := 384598208339108384226235

theorem tailTrace_6741021 : CollatzResearch.WordTrace tailWord_6741021 prefixEnd_6741021 384598208339108384226235 := by
  unfold tailWord_6741021
  simp only [CollatzResearch.WordTrace]
  refine ⟨245865234511439666574246917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163910156340959777716164611 245865234511439666574246917)
  ·
    refine ⟨46099731470894937482671297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 245865234511439666574246917 46099731470894937482671297)
    ·
      refine ⟨34574798603171203112003473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46099731470894937482671297 34574798603171203112003473)
      ·
        refine ⟨25931098952378402334002605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34574798603171203112003473 25931098952378402334002605)
        ·
          refine ⟨9724162107141900875250977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25931098952378402334002605 9724162107141900875250977)
          ·
            refine ⟨7293121580356425656438233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9724162107141900875250977 7293121580356425656438233)
            ·
              refine ⟨5469841185267319242328675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7293121580356425656438233 5469841185267319242328675)
              ·
                refine ⟨8204761777900978863493013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469841185267319242328675 8204761777900978863493013)
                ·
                  refine ⟨384598208339108384226235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8204761777900978863493013 384598208339108384226235)
                  ·
                    rfl

theorem cell23_6741021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_6741021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741021 prefixEnd_6741021 := by exact prefixLift 6741021
  have htrace : WordTrace (prefixWord ++ tailWord_6741021) baseStart_6741021 baseEnd_6741021 := by
    simpa [prefixWord, tailWord_6741021, baseEnd_6741021] using wordTrace_append hprefix tailTrace_6741021
  have hstable : (prefixWord ++ tailWord_6741021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741021).length < 2 ^ (prefixWord ++ tailWord_6741021).sum := by decide
  have hdescent : baseEnd_6741021 < baseStart_6741021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741034 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_6741034 : Nat := 118140960795 + 6741034 * 2 ^ 59
def prefixEnd_6741034 : Nat := 4983230072969 + 3 ^ 40 * 6741034 * 2
def baseEnd_6741034 : Nat := 1153796850100161302391185

theorem tailTrace_6741034 : CollatzResearch.WordTrace tailWord_6741034 prefixEnd_6741034 1153796850100161302391185 := by
  unfold tailWord_6741034
  simp only [CollatzResearch.WordTrace]
  refine ⟨61466427165098142448617539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163910472440261713196313437 61466427165098142448617539)
  ·
    refine ⟨92199640747647213672926309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61466427165098142448617539 92199640747647213672926309)
    ·
      refine ⟨17287432640183852563673683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92199640747647213672926309 17287432640183852563673683)
      ·
        refine ⟨25931148960275778845510525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287432640183852563673683 25931148960275778845510525)
        ·
          refine ⟨9724180860103417067066447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25931148960275778845510525 9724180860103417067066447)
          ·
            refine ⟨14586271290155125600599671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9724180860103417067066447 14586271290155125600599671)
            ·
              refine ⟨21879406935232688400899507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14586271290155125600599671 21879406935232688400899507)
              ·
                refine ⟨32819110402849032601349261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21879406935232688400899507 32819110402849032601349261)
                ·
                  refine ⟨12307166401068387225505973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32819110402849032601349261 12307166401068387225505973)
                  ·
                    refine ⟨1153796850100161302391185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12307166401068387225505973 1153796850100161302391185)
                    ·
                      rfl

theorem cell23_6741034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_6741034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741034 prefixEnd_6741034 := by exact prefixLift 6741034
  have htrace : WordTrace (prefixWord ++ tailWord_6741034) baseStart_6741034 baseEnd_6741034 := by
    simpa [prefixWord, tailWord_6741034, baseEnd_6741034] using wordTrace_append hprefix tailTrace_6741034
  have hstable : (prefixWord ++ tailWord_6741034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741034).length < 2 ^ (prefixWord ++ tailWord_6741034).sum := by decide
  have hdescent : baseEnd_6741034 < baseStart_6741034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741064 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_6741064 : Nat := 118140960795 + 6741064 * 2 ^ 59
def prefixEnd_6741064 : Nat := 4983230072969 + 3 ^ 40 * 6741064 * 2
def baseEnd_6741064 : Nat := 1153801984906706263266139

theorem tailTrace_6741064 : CollatzResearch.WordTrace tailWord_6741064 prefixEnd_6741064 1153801984906706263266139 := by
  unfold tailWord_6741064
  simp only [CollatzResearch.WordTrace]
  refine ⟨122933401425141942459031123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163911201900189256612041497 122933401425141942459031123)
  ·
    refine ⟨184400102137712913688546685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122933401425141942459031123 184400102137712913688546685)
    ·
      refine ⟨69150038301642342633205007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184400102137712913688546685 69150038301642342633205007)
      ·
        refine ⟨103725057452463513949807511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69150038301642342633205007 103725057452463513949807511)
        ·
          refine ⟨155587586178695270924711267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103725057452463513949807511 155587586178695270924711267)
          ·
            refine ⟨233381379268042906387066901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155587586178695270924711267 233381379268042906387066901)
            ·
              refine ⟨10939752153189511236893761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233381379268042906387066901 10939752153189511236893761)
              ·
                refine ⟨8204814114892133427670321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10939752153189511236893761 8204814114892133427670321)
                ·
                  refine ⟨6153610586169100070752741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8204814114892133427670321 6153610586169100070752741)
                  ·
                    refine ⟨1153801984906706263266139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6153610586169100070752741 1153801984906706263266139)
                    ·
                      rfl

theorem cell23_6741064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_6741064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741064 prefixEnd_6741064 := by exact prefixLift 6741064
  have htrace : WordTrace (prefixWord ++ tailWord_6741064) baseStart_6741064 baseEnd_6741064 := by
    simpa [prefixWord, tailWord_6741064, baseEnd_6741064] using wordTrace_append hprefix tailTrace_6741064
  have hstable : (prefixWord ++ tailWord_6741064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741064).length < 2 ^ (prefixWord ++ tailWord_6741064).sum := by decide
  have hdescent : baseEnd_6741064 < baseStart_6741064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741074 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_6741074 : Nat := 118140960795 + 6741074 * 2 ^ 59
def prefixEnd_6741074 : Nat := 4983230072969 + 3 ^ 40 * 6741074 * 2
def baseEnd_6741074 : Nat := 3461411089526663750673371

theorem tailTrace_6741074 : CollatzResearch.WordTrace tailWord_6741074 prefixEnd_6741074 3461411089526663750673371 := by
  unfold tailWord_6741074
  simp only [CollatzResearch.WordTrace]
  refine ⟨61466791895061914156481569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163911445053498437750617517 61466791895061914156481569)
  ·
    refine ⟨46100093921296435617361177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61466791895061914156481569 46100093921296435617361177)
    ·
      refine ⟨34575070440972326713020883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46100093921296435617361177 34575070440972326713020883)
      ·
        refine ⟨51862605661458490069531325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34575070440972326713020883 51862605661458490069531325)
        ·
          refine ⟨19448477123046933776074247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51862605661458490069531325 19448477123046933776074247)
          ·
            refine ⟨29172715684570400664111371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19448477123046933776074247 29172715684570400664111371)
            ·
              refine ⟨43759073526855600996167057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29172715684570400664111371 43759073526855600996167057)
              ·
                refine ⟨32819305145141700747125293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43759073526855600996167057 32819305145141700747125293)
                ·
                  refine ⟨12307239429428137780171985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32819305145141700747125293 12307239429428137780171985)
                  ·
                    refine ⟨9230429572071103335128989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12307239429428137780171985 9230429572071103335128989)
                    ·
                      refine ⟨3461411089526663750673371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230429572071103335128989 3461411089526663750673371)
                      ·
                        rfl

theorem cell23_6741074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_6741074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741074 prefixEnd_6741074 := by exact prefixLift 6741074
  have htrace : WordTrace (prefixWord ++ tailWord_6741074) baseStart_6741074 baseEnd_6741074 := by
    simpa [prefixWord, tailWord_6741074, baseEnd_6741074] using wordTrace_append hprefix tailTrace_6741074
  have hstable : (prefixWord ++ tailWord_6741074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741074).length < 2 ^ (prefixWord ++ tailWord_6741074).sum := by decide
  have hdescent : baseEnd_6741074 < baseStart_6741074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741084 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6741084 : Nat := 118140960795 + 6741084 * 2 ^ 59
def prefixEnd_6741084 : Nat := 4983230072969 + 3 ^ 40 * 6741084 * 2
def baseEnd_6741084 : Nat := 3461416224333208711548325

theorem tailTrace_6741084 : CollatzResearch.WordTrace tailWord_6741084 prefixEnd_6741084 3461416224333208711548325 := by
  unfold tailWord_6741084
  simp only [CollatzResearch.WordTrace]
  refine ⟨122933766155105714166895153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163911688206807618889193537 122933766155105714166895153)
  ·
    refine ⟨92200324616329285625171365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122933766155105714166895153 92200324616329285625171365)
    ·
      refine ⟨17287560865561741054719631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92200324616329285625171365 17287560865561741054719631)
      ·
        refine ⟨25931341298342611582079447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287560865561741054719631 25931341298342611582079447)
        ·
          refine ⟨38897011947513917373119171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25931341298342611582079447 38897011947513917373119171)
          ·
            refine ⟨58345517921270876059678757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38897011947513917373119171 58345517921270876059678757)
            ·
              refine ⟨10939784610238289261189767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58345517921270876059678757 10939784610238289261189767)
              ·
                refine ⟨16409676915357433891784651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10939784610238289261189767 16409676915357433891784651)
                ·
                  refine ⟨24614515373036150837676977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16409676915357433891784651 24614515373036150837676977)
                  ·
                    refine ⟨18460886529777113128257733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24614515373036150837676977 18460886529777113128257733)
                    ·
                      refine ⟨3461416224333208711548325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18460886529777113128257733 3461416224333208711548325)
                      ·
                        rfl

theorem cell23_6741084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6741084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741084 prefixEnd_6741084 := by exact prefixLift 6741084
  have htrace : WordTrace (prefixWord ++ tailWord_6741084) baseStart_6741084 baseEnd_6741084 := by
    simpa [prefixWord, tailWord_6741084, baseEnd_6741084] using wordTrace_append hprefix tailTrace_6741084
  have hstable : (prefixWord ++ tailWord_6741084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741084).length < 2 ^ (prefixWord ++ tailWord_6741084).sum := by decide
  have hdescent : baseEnd_6741084 < baseStart_6741084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741104 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_6741104 : Nat := 118140960795 + 6741104 * 2 ^ 59
def prefixEnd_6741104 : Nat := 4983230072969 + 3 ^ 40 * 6741104 * 2
def baseEnd_6741104 : Nat := 3461426493946298633298233

theorem tailTrace_6741104 : CollatzResearch.WordTrace tailWord_6741104 prefixEnd_6741104 3461426493946298633298233 := by
  unfold tailWord_6741104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122934130885069485874759183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163912174513425981166345577 122934130885069485874759183)
  ·
    refine ⟨184401196327604228812138775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122934130885069485874759183 184401196327604228812138775)
    ·
      refine ⟨276601794491406343218208163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184401196327604228812138775 276601794491406343218208163)
      ·
        refine ⟨414902691737109514827312245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276601794491406343218208163 414902691737109514827312245)
        ·
          refine ⟨38897127350354017015060523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 414902691737109514827312245 38897127350354017015060523)
          ·
            refine ⟨58345691025531025522590785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38897127350354017015060523 58345691025531025522590785)
            ·
              refine ⟨43759268269148269141943089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58345691025531025522590785 43759268269148269141943089)
              ·
                refine ⟨32819451201861201856457317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43759268269148269141943089 32819451201861201856457317)
                ·
                  refine ⟨6153647100348975348085747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32819451201861201856457317 6153647100348975348085747)
                  ·
                    refine ⟨9230470650523463022128621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6153647100348975348085747 9230470650523463022128621)
                    ·
                      refine ⟨3461426493946298633298233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230470650523463022128621 3461426493946298633298233)
                      ·
                        rfl

theorem cell23_6741104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_6741104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741104 prefixEnd_6741104 := by exact prefixLift 6741104
  have htrace : WordTrace (prefixWord ++ tailWord_6741104) baseStart_6741104 baseEnd_6741104 := by
    simpa [prefixWord, tailWord_6741104, baseEnd_6741104] using wordTrace_append hprefix tailTrace_6741104
  have hstable : (prefixWord ++ tailWord_6741104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741104).length < 2 ^ (prefixWord ++ tailWord_6741104).sum := by decide
  have hdescent : baseEnd_6741104 < baseStart_6741104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741121 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6741121 : Nat := 118140960795 + 6741121 * 2 ^ 59
def prefixEnd_6741121 : Nat := 4983230072969 + 3 ^ 40 * 6741121 * 2
def baseEnd_6741121 : Nat := 3461435223117425066785655

theorem tailTrace_6741121 : CollatzResearch.WordTrace tailWord_6741121 prefixEnd_6741121 3461435223117425066785655 := by
  unfold tailWord_6741121
  simp only [CollatzResearch.WordTrace]
  refine ⟨245868881811077383652887217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163912587874051589101924811 245868881811077383652887217)
  ·
    refine ⟨184401661358308037739665413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 245868881811077383652887217 184401661358308037739665413)
    ·
      refine ⟨34575311504682757076187265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184401661358308037739665413 34575311504682757076187265)
      ·
        refine ⟨25931483628512067807140449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34575311504682757076187265 25931483628512067807140449)
        ·
          refine ⟨19448612721384050855355337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25931483628512067807140449 19448612721384050855355337)
          ·
            refine ⟨14586459541038038141516503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19448612721384050855355337 14586459541038038141516503)
            ·
              refine ⟨21879689311557057212274755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14586459541038038141516503 21879689311557057212274755)
              ·
                refine ⟨32819533967335585818412133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21879689311557057212274755 32819533967335585818412133)
                ·
                  refine ⟨6153662618875422340952275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32819533967335585818412133 6153662618875422340952275)
                  ·
                    refine ⟨9230493928313133511428413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6153662618875422340952275 9230493928313133511428413)
                    ·
                      refine ⟨3461435223117425066785655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230493928313133511428413 3461435223117425066785655)
                      ·
                        rfl

theorem cell23_6741121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6741121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741121 prefixEnd_6741121 := by exact prefixLift 6741121
  have htrace : WordTrace (prefixWord ++ tailWord_6741121) baseStart_6741121 baseEnd_6741121 := by
    simpa [prefixWord, tailWord_6741121, baseEnd_6741121] using wordTrace_append hprefix tailTrace_6741121
  have hstable : (prefixWord ++ tailWord_6741121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741121).length < 2 ^ (prefixWord ++ tailWord_6741121).sum := by decide
  have hdescent : baseEnd_6741121 < baseStart_6741121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741148 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_6741148 : Nat := 118140960795 + 6741148 * 2 ^ 59
def prefixEnd_6741148 : Nat := 4983230072969 + 3 ^ 40 * 6741148 * 2
def baseEnd_6741148 : Nat := 3461449087095096461148031

theorem tailTrace_6741148 : CollatzResearch.WordTrace tailWord_6741148 prefixEnd_6741148 3461449087095096461148031 := by
  unfold tailWord_6741148
  simp only [CollatzResearch.WordTrace]
  refine ⟨122934933290989783632060049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163913244387986378176080065 122934933290989783632060049)
  ·
    refine ⟨92201199968242337724045037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122934933290989783632060049 92201199968242337724045037)
    ·
      refine ⟨34575449988090876646516889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92201199968242337724045037 34575449988090876646516889)
      ·
        refine ⟨25931587491068157484887667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34575449988090876646516889 25931587491068157484887667)
        ·
          refine ⟨38897381236602236227331501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25931587491068157484887667 38897381236602236227331501)
          ·
            refine ⟨14586517963725838585249313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38897381236602236227331501 14586517963725838585249313)
            ·
              refine ⟨10939888472794378938936985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14586517963725838585249313 10939888472794378938936985)
              ·
                refine ⟨8204916354595784204202739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10939888472794378938936985 8204916354595784204202739)
                ·
                  refine ⟨12307374531893676306304109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204916354595784204202739 12307374531893676306304109)
                  ·
                    refine ⟨4615265449460128614864041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12307374531893676306304109 4615265449460128614864041)
                    ·
                      refine ⟨3461449087095096461148031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615265449460128614864041 3461449087095096461148031)
                      ·
                        rfl

theorem cell23_6741148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_6741148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741148 prefixEnd_6741148 := by exact prefixLift 6741148
  have htrace : WordTrace (prefixWord ++ tailWord_6741148) baseStart_6741148 baseEnd_6741148 := by
    simpa [prefixWord, tailWord_6741148, baseEnd_6741148] using wordTrace_append hprefix tailTrace_6741148
  have hstable : (prefixWord ++ tailWord_6741148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741148).length < 2 ^ (prefixWord ++ tailWord_6741148).sum := by decide
  have hdescent : baseEnd_6741148 < baseStart_6741148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741251 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 4, 2]
def baseStart_6741251 : Nat := 118140960795 + 6741251 * 2 ^ 59
def prefixEnd_6741251 : Nat := 4983230072969 + 3 ^ 40 * 6741251 * 2
def baseEnd_6741251 : Nat := 3461501975602509558160057

theorem tailTrace_6741251 : CollatzResearch.WordTrace tailWord_6741251 prefixEnd_6741251 3461501975602509558160057 := by
  unfold tailWord_6741251
  simp only [CollatzResearch.WordTrace]
  refine ⟨245873623300606415855119607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163915748867070943903413071 245873623300606415855119607)
  ·
    refine ⟨368810434950909623782679411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245873623300606415855119607 368810434950909623782679411)
    ·
      refine ⟨553215652426364435674019117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368810434950909623782679411 553215652426364435674019117)
      ·
        refine ⟨207455869659886663377757169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553215652426364435674019117 207455869659886663377757169)
        ·
          refine ⟨155591902244914997533317877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207455869659886663377757169 155591902244914997533317877)
          ·
            refine ⟨14586740835460781018748551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155591902244914997533317877 14586740835460781018748551)
            ·
              refine ⟨21880111253191171528122827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14586740835460781018748551 21880111253191171528122827)
              ·
                refine ⟨32820166879786757292184241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21880111253191171528122827 32820166879786757292184241)
                ·
                  refine ⟨24615125159840067969138181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32820166879786757292184241 24615125159840067969138181)
                  ·
                    refine ⟨4615335967470012744213409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24615125159840067969138181 4615335967470012744213409)
                    ·
                      refine ⟨3461501975602509558160057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615335967470012744213409 3461501975602509558160057)
                      ·
                        rfl

theorem cell23_6741251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_6741251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741251 prefixEnd_6741251 := by exact prefixLift 6741251
  have htrace : WordTrace (prefixWord ++ tailWord_6741251) baseStart_6741251 baseEnd_6741251 := by
    simpa [prefixWord, tailWord_6741251, baseEnd_6741251] using wordTrace_append hprefix tailTrace_6741251
  have hstable : (prefixWord ++ tailWord_6741251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741251).length < 2 ^ (prefixWord ++ tailWord_6741251).sum := by decide
  have hdescent : baseEnd_6741251 < baseStart_6741251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741311 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 5, 2]
def baseStart_6741311 : Nat := 118140960795 + 6741311 * 2 ^ 59
def prefixEnd_6741311 : Nat := 4983230072969 + 3 ^ 40 * 6741311 * 2
def baseEnd_6741311 : Nat := 3461532784441779323409781

theorem tailTrace_6741311 : CollatzResearch.WordTrace tailWord_6741311 prefixEnd_6741311 3461532784441779323409781 := by
  unfold tailWord_6741311
  simp only [CollatzResearch.WordTrace]
  refine ⟨245875811680389046102303787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163917207786926030734869191 245875811680389046102303787)
  ·
    refine ⟨368813717520583569153455681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245875811680389046102303787 368813717520583569153455681)
    ·
      refine ⟨276610288140437676865091761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368813717520583569153455681 276610288140437676865091761)
      ·
        refine ⟨207457716105328257648818821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276610288140437676865091761 207457716105328257648818821)
        ·
          refine ⟨38898321769749048309153529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207457716105328257648818821 38898321769749048309153529)
          ·
            refine ⟨29173741327311786231865147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38898321769749048309153529 29173741327311786231865147)
            ·
              refine ⟨43760611990967679347797721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29173741327311786231865147 43760611990967679347797721)
              ·
                refine ⟨32820458993225759510848291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43760611990967679347797721 32820458993225759510848291)
                ·
                  refine ⟨49230688489838639266272437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32820458993225759510848291 49230688489838639266272437)
                  ·
                    refine ⟨4615377045922372431213041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49230688489838639266272437 4615377045922372431213041)
                    ·
                      refine ⟨3461532784441779323409781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4615377045922372431213041 3461532784441779323409781)
                      ·
                        rfl

theorem cell23_6741311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_6741311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741311 prefixEnd_6741311 := by exact prefixLift 6741311
  have htrace : WordTrace (prefixWord ++ tailWord_6741311) baseStart_6741311 baseEnd_6741311 := by
    simpa [prefixWord, tailWord_6741311, baseEnd_6741311] using wordTrace_append hprefix tailTrace_6741311
  have hstable : (prefixWord ++ tailWord_6741311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741311).length < 2 ^ (prefixWord ++ tailWord_6741311).sum := by decide
  have hdescent : baseEnd_6741311 < baseStart_6741311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741335 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 1, 1, 3]
def baseStart_6741335 : Nat := 118140960795 + 6741335 * 2 ^ 59
def prefixEnd_6741335 : Nat := 4983230072969 + 3 ^ 40 * 6741335 * 2
def baseEnd_6741335 : Nat := 3461545107977487229509671

theorem tailTrace_6741335 : CollatzResearch.WordTrace tailWord_6741335 prefixEnd_6741335 3461545107977487229509671 := by
  unfold tailWord_6741335
  simp only [CollatzResearch.WordTrace]
  refine ⟨245876687032302098201177459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163917791354868065467451639 245876687032302098201177459)
  ·
    refine ⟨368815030548453147301766189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245876687032302098201177459 368815030548453147301766189)
    ·
      refine ⟨138305636455669930238162321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368815030548453147301766189 138305636455669930238162321)
      ·
        refine ⟨103729227341752447678621741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138305636455669930238162321 103729227341752447678621741)
        ·
          refine ⟨38898460253157167879483153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103729227341752447678621741 38898460253157167879483153)
          ·
            refine ⟨29173845189867875909612365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38898460253157167879483153 29173845189867875909612365)
            ·
              refine ⟨10940191946200453466104637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29173845189867875909612365 10940191946200453466104637)
              ·
                refine ⟨4102571979825170049789239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10940191946200453466104637 4102571979825170049789239)
                ·
                  refine ⟨6153857969737755074683859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102571979825170049789239 6153857969737755074683859)
                  ·
                    refine ⟨9230786954606632612025789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6153857969737755074683859 9230786954606632612025789)
                    ·
                      refine ⟨3461545107977487229509671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230786954606632612025789 3461545107977487229509671)
                      ·
                        rfl

theorem cell23_6741335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_6741335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741335 prefixEnd_6741335 := by exact prefixLift 6741335
  have htrace : WordTrace (prefixWord ++ tailWord_6741335) baseStart_6741335 baseEnd_6741335 := by
    simpa [prefixWord, tailWord_6741335, baseEnd_6741335] using wordTrace_append hprefix tailTrace_6741335
  have hstable : (prefixWord ++ tailWord_6741335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741335).length < 2 ^ (prefixWord ++ tailWord_6741335).sum := by decide
  have hdescent : baseEnd_6741335 < baseStart_6741335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741352 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6741352 : Nat := 118140960795 + 6741352 * 2 ^ 59
def prefixEnd_6741352 : Nat := 4983230072969 + 3 ^ 40 * 6741352 * 2
def baseEnd_6741352 : Nat := 3461553837148613662997093

theorem tailTrace_6741352 : CollatzResearch.WordTrace tailWord_6741352 prefixEnd_6741352 3461553837148613662997093 := by
  unfold tailWord_6741352
  simp only [CollatzResearch.WordTrace]
  refine ⟨122938653536620255052273155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163918204715493673403030873 122938653536620255052273155)
  ·
    refine ⟨184407980304930382578409733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122938653536620255052273155 184407980304930382578409733)
    ·
      refine ⟨34576496307174446733451825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184407980304930382578409733 34576496307174446733451825)
      ·
        refine ⟨25932372230380835050088869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34576496307174446733451825 25932372230380835050088869)
        ·
          refine ⟨4862319793196406571891663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25932372230380835050088869 4862319793196406571891663)
          ·
            refine ⟨7293479689794609857837495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862319793196406571891663 7293479689794609857837495)
            ·
              refine ⟨10940219534691914786756243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293479689794609857837495 10940219534691914786756243)
              ·
                refine ⟨16410329302037872180134365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940219534691914786756243 16410329302037872180134365)
                ·
                  refine ⟨6153873488264202067550387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16410329302037872180134365 6153873488264202067550387)
                  ·
                    refine ⟨9230810232396303101325581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6153873488264202067550387 9230810232396303101325581)
                    ·
                      refine ⟨3461553837148613662997093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9230810232396303101325581 3461553837148613662997093)
                      ·
                        rfl

theorem cell23_6741352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6741352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6741352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6741352 prefixEnd_6741352 := by exact prefixLift 6741352
  have htrace : WordTrace (prefixWord ++ tailWord_6741352) baseStart_6741352 baseEnd_6741352 := by
    simpa [prefixWord, tailWord_6741352, baseEnd_6741352] using wordTrace_append hprefix tailTrace_6741352
  have hstable : (prefixWord ++ tailWord_6741352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741352).length < 2 ^ (prefixWord ++ tailWord_6741352).sum := by decide
  have hdescent : baseEnd_6741352 < baseStart_6741352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
